# tools/link: separate compilation + N-way link for pa-mm0 closures

Goal: replace the monolithic final compile with three steps. Today that compile flattens the whole import
closure into one `<root>-proof-input.mm1` and runs one `mm0-rs compile`; for `zfc_incompleteness_root`
(8.1 GB, ~3,029 modules) that pass takes 45–60+ h. The replacement:

1. compile each module once, against stubs of its dependencies;
2. link the per-module `.mmb`s mechanically;
3. run one `mm0-c` check against the same joined spec.

| file | role |
| --- | --- |
| `mm1lib.py` | closure order (= `pa-mm0/check.py` flat order), MM1 statement splitter, theorem → stub |
| `mkiface.py` | module → interface items (stubs + verbatim defs / `do` / notations) |
| `compile_one.py` | compile one module against its closure's (pruned) interfaces; content-hash cache |
| `build_all.py` | `compile_one` over a whole closure, in parallel (modules are independent) |
| `rawmmb.py` | byte-level MMB reader / writer used by the linker |
| `linkn.py` | N-way linker → `OUT.mmb` + `OUT.mm0` |
| `link_check.py` | check.py's source checks + join + link + `mm0-c` + axiom check + false control → `report.json` |
| `runstat.py` | wall time / peak memory of a child (Linux `wait4` RSS; Windows peak commit of the process handle) |
| `selftest.py` | toy project: positive case and tamper cases (a few seconds) |

Usage (from anywhere; `MM0TOOLS` or `--tools` names the dir holding `mm0-rs` / `mm0-c`, `.exe` on Windows;
`LINK_PA` / `LINK_VENDOR` name the module dir and the peano vendor dir, default `<repo>/pa-mm0`, `<repo>/lean-mm0/vendor`):

    python3 tools/link/build_all.py  ROOT --build DIR -j 4 [--mem-gb G] [--progress FILE] [--cache-max-gb C]
    python3 tools/link/link_check.py ROOT --build DIR [--out OUT]   # link + check.py's checks, OUT/report.json
    python3 tools/link/selftest.py [--vendor DIR]

On the host, the runner action `link-check` runs both through `host/link/link_job.py` (host-release), from a pinned
snapshot of this directory (`host/link/src`, `host/link/MANIFEST.sha256`, refreshed by `host/link/sync.py`).

## 1. Design

**Interface of a module** (`mkiface.py`): its statements in source order, with comments and imports removed:
- `def` / `term` / `sort` / notation statements stay verbatim, annotations included. Def bodies are
  therefore exact.
- `do` blocks stay verbatim.
- each `[@a] [pub] theorem N BIS: TYPE = PROOF;` becomes the stub `[@a] axiom N BIS: TYPE;`.

**Compiling module M** (`compile_one.py`): the input `DIR/M/input.mm1` is

    import "../_peano/peano_iface.mm1";   -- peano.mm1 with its theorems stubbed (see 4.3)
    <interface items of M's closure, in check.py's flat order, pruned>
    <M's own source with its imports removed>   -- the exact chunk check.py's flattening contains

`mm0-rs compile` turns this into `DIR/M/M.mmb`, which holds stubs and copies plus M's own proofs. The
compile passes iff mm0-rs exits 0 and its output contains no "contains sorry" (as in check.py). Each
module is compiled against its dependencies' **sources**, not their compiled outputs, so all modules
can compile in parallel and in any order.

**Pruning** (on by default): every `do` block and notation of the closure is kept. A def or stub is kept
iff its name is reachable from an identifier of M's source or of a kept item, transitively. An identifier
of the form `<def>eq…` / `<def>eqd…` keeps `<def>`, whose `@_` derive-eq annotation regenerates it.
Pruning is untrusted: if it drops something M needs, M's compile fails, and `--full` turns it off.

**Linking** (`linkn.py`): the output starts with peano, followed by each module's OWN statements in
check.py's flat order, which is the declaration sequence of the monolithic flattened compile.

Each term/def or theorem/axiom of `M.mmb` whose name is declared by a module in M's closure is a COPY:
- the lookup is closure-scoped;
- two candidates is an error;
- a copy is identified with the original after renumbering, and its raw statement bytes must equal the
  original's: binders, return/conclusion, hypotheses, def body;
- a copied axiom is a resolved stub; a copied theorem was re-derived by an annotation or `do` block.

Everything else is OWN: it is appended with term/theorem ids renumbered and keeps its visibility. An own
non-peano axiom is a LINK ERROR (an unresolved stub, or a real axiom), and so is an own primitive term.

**Spec**: the public statements of the output (sorts, terms, public defs, axioms, public theorems) are
compared by kind and name with the joined spec (`mm0-rs join ROOT.mm0`, as check.py). In every pilot
they matched in order, so `OUT.mm0` is a **byte copy of the joined spec**. If they ever don't, `--reorder`
reorders the spec as `tools/gen7/link.py` does; otherwise it is a LINK ERROR.

## 2. What an importer can use (experiments, mm0-rs 00ddf79a)

All of these were confirmed by compiling small throwaway files; `selftest.py` re-checks the first group (private theorem, local def, `do`-block tactic, derive-eq theorem across modules):

- **Visible through `import`:**
  - private (non-`pub`) theorems;
  - `local def`s;
  - Lisp definitions from `do` blocks (a tactic defined in A works in B);
  - theorems generated by annotations (`@_ def foo` ⇒ `fooeq1`, `fooeqd`, …);
  - Lisp registrations (`register-eqd`, `eqd-map`).

  So interfaces must include private theorems, local defs, annotations and every `do` block.
- **Annotations on theorems matter.** `peano.mm1` registers equality theorems with
  `@(register-eqd 'not) theorem noteqd …`. When stubs dropped the annotation, later derive-eq failed
  ("equality theorem not found for not"). Stubs keep annotations.
- **Name clashes are elaboration errors, not crashes.** "theorem 'X' redeclared" and "previously
  declared here" appeared both for duplicate theorems and for duplicate `local def` / `@_ def` across
  two imports. The "no entry found for key" crash did not reproduce in these experiments.
- **mm0-rs can `import "x.mmb"`, including its Lisp state.** The `.mmb` has a `Lisp` index table:
  `eqtac`, `named` and derive-eq all worked after importing a `.mmb`. However, two `.mmb` imports that
  share content fail with "constant '1' declared twice": there is no dedup, so a dependency diamond
  breaks. Precompiled per-dependency `.mmb` interfaces are therefore not usable. Source interfaces plus
  per-module caching are used instead.

## 3. Trust argument

Unchanged from today. The trusted base is still `mm0-c` + the joined spec (`mm0-rs join`, as check.py) +
the axiom check (+ the false control as a sanity check of the checker run). Everything in this directory
— interface generation, pruning, separate `mm0-rs` compiles, linking — produces an untrusted proof
object. `mm0-c` checks every proof step of `OUT.mmb` (local theorems included) against the definitions
and statements of `OUT.mm0`:

- If a stub's text differed from the real theorem, every proof using the stub is checked against the
  real statement, and mm0-c rejects.
- If a module's copy of a def had a different body, its own proofs are checked against the original
  body, and mm0-c rejects.
- A missing, extra or misordered public statement makes the spec walk fail.

The linker's own statement comparison only gives early, readable errors. `selftest.py` disables it
(`LINKN_TEST_NO_VERIFY=1`, test only) and shows that mm0-c alone rejects a tampered stub and a tampered
def.

Only peano's 26 axioms can remain:
- the linker rejects any other own axiom;
- `link_check.py` counts the output's axioms;
- it checks the spec's axiom texts against `peano.mm0`, like `tools/gen7/axioms.py`.

mm0-c pairs each `.mmb` axiom with the spec axiom in the same position, so nothing else can be assumed.

In the pilots the output spec is byte-identical to the joined spec the monolithic path checks (same
sha256). The linked `.mmb` also has exactly the monolithic declaration sequence (kind, visibility, name),
and over 99.9% of its proof streams are byte-identical to the monolithic file's.

## 4. Hazards found

1. **Local names reused in unrelated subtrees.** Name resolution is closure-scoped, so two modules in
   different subtrees may both have a local `t`. The output then has two local theorems named `t`, which
   mm0-c accepts because local names do not matter to it. Within one closure the names are unique, as
   in the monolithic compile.
2. **A module redeclaring a name of its closure.** The monolithic compile reports "redeclared". A pruned
   interface could hide the clash, and the linker would then treat M's declaration as a copy.
   `compile_one` therefore rejects any def or theorem of M whose name is a def or theorem anywhere in its
   closure, pruned or not.
3. **Annotations and `do` blocks re-run in every importer.** derive-eq re-derives eq theorems (with
   proofs) for every kept def, and `do` blocks are always kept. The linker drops these copies by name
   after checking that their statements are equal. Guarded generation such as
   `(if (undef? (get-decl 'X)) …)` is order-dependent; the interface keeps the flat order, so the guard
   sees the same state as in the monolithic compile.
4. **Ordering.**
   - The term and theorem tables must follow the statement order. Own entries are appended in module
     order and modules in post-order, so every reference points backward.
   - The public order equals the joined spec only because check.py's flat order (post-order DFS of the
     `.mm1` imports) matches `mm0-rs join` on the `.mm0` imports. The monolithic path relies on the same
     fact.
   - A module whose `.mm0` imports differ from its `.mm1` imports would need `--reorder`.
5. **Defs must stay definitionally identical.** Interfaces copy def bodies verbatim, and the linker
   compares each copy's unify stream byte-for-byte after renumbering.
6. **Stale builds.** `link.json` records the module's closure order and a cache key. The key is the sha256
   of `input.mm1`, of the peano interface and of mm0-rs, so it covers the module's source and every
   interface item it was compiled against. The linker refuses a module whose recorded closure differs
   from the current one, or which did not pass. Because mm0-c is the final check, a stale `.mmb` can at
   worst cause a rejection.
7. **Pruning is heuristic.** Pruning by identifiers can miss names that a tactic computes at run time.
   The only effect is a failed compile, and then `--full` is used. This never happened in the pilots.
8. **Tactics that read proofs** (`get-decl` / `get-proof`), e.g. `tvDedLift` in
   `source_reflection_transfer_tv_row_guard` and `tvExistDedLift` in `..._tv_existence_logic`: a `do` block
   reads a theorem's proof, recursively the proofs of the theorems it uses (peano's included), and adds new
   theorems (`tvDed_<t>_<mask>`) with `add-thm!`. Against stubs it fails (`match failed: (axiom t ..)`), and so
   does every importer, which replays the block. Rule (`compile_one.Plan.verbatim`):
   - a **reader block** is a `do` block that uses `get-decl` / `get-proof`, or calls a Lisp name defined in one;
   - if a module's input contains a reader block (its own or one of its closure) that names a theorem, the
     module is compiled against the real `peano.mm1`, and the theorems reachable from the names in those reader
     blocks are kept **verbatim, with their proofs**, instead of as stubs. Reachable = closure under the
     identifiers of the theorems' texts, also seeded by the theorems named in any `do` block and the annotated
     theorems (tactics such as `register-eqd` put those into elaborated proofs without the source naming them);
   - if the compile still meets a stub (`match failed: (axiom X ..)`), X is added and the module recompiled (at
     most 20 rounds; the learned names are kept in `link.json` as `reader_extra`).
   Every importer then replays the reader blocks in flat order, exactly as the monolithic compile does, and
   regenerates the same theorems; the module that generates a name first in flat order owns it, and the linker
   treats the importers' regenerated theorems and verbatim theorems as copies (statement compared, proof dropped).
   Modules without a reader block in their input are unaffected. Cost: about 3,860 verbatim theorems (0.9 MB)
   and ~1 s per module downstream of `tv_row_guard` (24 modules of `k215_final_thm1`, 28 of the root).
   A registration made outside a module's closure but before it in the global flat order (e.g. a later
   `register-eqd` of the same term) changes what the monolithic compile elaborates but not what the separate one
   does; then a generated name can differ (`source_reflection_transfer_tv_producers`: `tv_row_guard` generates
   `tvDed_zfcQuantFullDerives_congr_01` where the monolithic compile generates `tvDed_rawDist_Full_congr_01`,
   which here the root module generates later: one extra local theorem). mm0-c still checks every proof; local
   names do not matter to it.

## 5. Measured results (local: 4 vCPU, 15 GB; stock mm0-c `5caf35d7…`, mm0-rs `00ddf79a…`, Linux builds)

These are the stock tools in `/home/user/mm0-zflr/tools`, not the host's capacity2 build. All closures
below passed on the host with the stock checker.

All four pilot closures pass both pipelines:
- mm0-c rc 0;
- the false control is rejected (rc 255; conclusion of the root's last theorem set to `F.`);
- axioms are exactly peano's 26;
- the spec sha256 equals the monolithic one.

Monolithic = `pa-mm0/check.py` unchanged, with Linux tool symlinks. Separate = `build_all -j 4` (pruned)
+ `link_check`.

| closure | modules | flat MB | mono compile | mono peak RSS | sep. CPU (sum) | sep. max module | link | linked .mmb | mm0-c mono / link |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| g2_generic_g4 | 148 | 6.4 | 16.1 s | 1.08 GB | 101 s¹ | 4.0 s, 0.32 GB | 3.4 s | 5.7 MB | 0.05 / 0.04 s |
| g2_generic_s1_local | 311 | 7.4 | 17.8 s | 1.11 GB | 234 s¹ | 3.7 s, 0.49 GB | 8.9 s | 13.2 MB | 0.09 / 0.13 s |
| g2_generic_sf_defines | 337 | 28.1 | 48.2 s | 4.32 GB | 276 s¹ | 7.2 s, 1.12 GB | 7.0 s | 25.4 MB | 0.15 / 0.14 s |
| g2_generic_s1_subnum | 279 | 54.1 | 102.5 s | 7.61 GB | 184 s² (265 s¹) | 65.6 s, 4.33 GB | 6.9 s | 42.8 MB | 0.22 / 0.22 s |

¹ importing the real `peano.mm1` (0.47 s per module). ² with the stubbed peano interface (0.16 s).

For s1_subnum, the separate wall time at -j4 was 75 s. That is bounded by its one 33 MB module,
`g2_generic_s1_sub` (65.6 s, 4.33 GB); the other 278 modules took 119 s of CPU together. The link
used under 0.1 GB, and the join, axiom check and false control together took under 3 s.

**Per-module overhead vs closure depth** (s1_subnum, pruned, median per bucket):

| closure size (modules) | n | closure source | interface kept | items kept / total | compile |
| --- | --- | --- | --- | --- | --- |
| 1–29 | 73 | 0.1 MB | 10 KB | 100 / 462 | 0.52 s |
| 30–79 | 125 | 0.8 MB | 41 KB | 340 / 2476 | 0.63 s |
| 80–149 | 43 | 1.1 MB | 45 KB | 357 / 3347 | 0.71 s |
| 150–219 | 5 | 3.9 MB | 297 KB | 515 / 4801 | 1.17 s |
| 220–299 | 33 | 5.1 MB | 55 KB | 457 / 9235 | 0.71 s |

(These times use the real peano; the peano interface saves about 0.3 s per module.)

The pruned interface stays bounded: it tracks what the module uses, not the closure size.
Without pruning, the subnum root's input was 24.2 MB and took 21.8 s (0.87 GB); pruned, it was
0.55 MB and 0.9 s. Unpruned interfaces would make the total cost O(modules × closure), so pruning is
required. The remaining fixed cost per module (peano interface + interface + export) is about 0.3–0.4 s.

**Linker throughput**: about 6 MB/s of output (subnum: 42.8 MB in 6.9 s, single-threaded Python).
- A profile shows the proof-stream id remap (`rawmmb.remap`) is about 70% of link time, at about
  10 MB/s of proof bytes.
- The rest is a per-module cost proportional to the interface copies: names and raw tables. Peano's
  copies in every module are skipped by a byte-compare fast path.
- The first, object-based version (`translator/mmb_reader`) was 3–4x slower, mostly building Python
  objects for the copies. The byte-level rewrite produces the same `.mmb` up to the debug index.
- Projection for an 8 GB root: 20–25 min. If that matters, the remap can run per module in parallel,
  since each module's id maps are known once its tables are resolved.

**How the monolithic compile scales** (host `results/*/status.json`, check jobs that passed,
median wall time per MB of flat input):

| flat size | ≤ 400 MB | 400–800 MB | 0.8–1.6 GB | 1.6–3.2 GB | 8.1 GB root |
| --- | --- | --- | --- | --- | --- |
| s / MB | 0.9–1.7 | 1.4 | 2.0 | 3.3 (worst 5.9) | 20–27 (45–60 h) |

Peak commit is about 150–170 bytes per input byte (500 GB at 3.1 GB). Locally, up to 54 MB, the cost is
about linear (1.7–1.9 s/MB, about 140 B of RSS per input byte).

Separate compilation keeps each compile at its own module's size: one module at a time, at about
1 s/MB plus about 0.4 s fixed.

**Root closure**: in git it has 2,844 modules (6.58 GB). Another 184 imports are host-staged
(`results/staged-sources.json`), some of them large, e.g. 302 MB. The largest module in git is 88 MB;
16 modules are over 50 MB, and 217 over 10 MB (5.1 GB together).

Projection for the root on the host, before measurement:
- about 2.5–3.5 h of total compile CPU, plus about 20 min of fixed cost;
- with -j 16–32 on the r6i.32xlarge, wall time is bounded by the largest staged module (minutes);
- link: 20–25 min;
- mm0-c: as on the 4.6 GB / 7 min run, scaled.

## 6. Host integration

Runner action `{"action": "link-check", "module": "<root>", "jobs": N, "timeout_minutes": M}` (coordinator jobs
only, exclusive like capacity2), on host-release: `host/runner.ps1` extracts `host/link` from the fetched
host-release commit, checks `host/link/src` against `host/link/MANIFEST.sha256`, and runs `host/link/link_job.py`
with the pinned Python and the capacity2 tools (mm0-rs and mm0-c from `capacity2_tools_dir`, the same pair the
monolithic capacity2 check uses). `link_job.py` runs `build_all.py` then `link_check.py`, and writes
`results/<id>/report.json` (check.py's format plus `compile` and `link` sections), `build.json`, the stage logs and
the failing modules' compile logs.

- **Scale.** `compile_one.Plan` computes the closure, every interface and a name index once per job; each module
  then costs O(what it reaches), not O(closure). (Before, every module re-read and re-hashed its whole closure: about
  3,000 x 7 GB for the root.) `Plan.select` returns exactly the items of the per-module selection (`select_flat`):
  the pilot's 279 inputs are byte-identical, and `selftest.py` checks it.
- **Per-module cache.**
  - `DIR/<m>/<m>.mmb` + `link.json`, keyed by `sha256(input.mm1 text) : sha256(peano_iface) : sha256(mm0-rs)`.
    `input.mm1` contains the module's own source and every interface item it sees, so a change to a dependency's
    statement, def or `do` block invalidates exactly the modules that can see it. The key is computed in memory;
    `input.mm1` is written only for a compile and deleted after it passes.
  - A change confined to a dependency's proofs does not invalidate any importer, because interfaces contain no proofs.
  - Host: `C:\K215Proof\linkcache` (config `link_cache_dir` overrides). About 1.3 MB per module (mostly the stubbed
    peano part) plus the module's own proofs: about 0.4 GB for the 279-module pilot, a projected 10-20 GB for the root.
  - Bounded by `build_all.py --cache-max-gb` (job field `cache_max_gb`, default 300): after a build, least recently used
    module dirs of other closures are deleted until the module dirs fit. Deleting the whole directory at any time no
    job is running is safe; the next job recompiles everything.
  - Logs over 1 MB are deleted on success.
- **Memory.** `build_all.py --mem-gb G` starts a compile only while the estimates of the running ones plus its own fit
  (estimate 1 GB + 160 B per source byte, 230 for `_slim<N>_` files). `link_job.py` sets G from the free commit at
  start minus 64 GB (job field `mem_budget_gb` overrides).
- **Windows.** Tool names get `.exe`; every file is written as UTF-8 with LF; subprocesses get `stdin=DEVNULL`;
  `runstat.run` reads the child's peak commit from its process handle (`PeakPagefileUsage`); a module path over 240
  characters fails that module with a readable error (the longest module name is 68 characters, so
  `C:\K215Proof\linkcache` stays under 170).
- **Staged sources.** `closure_order` reads `pa-mm0/` as staged on the host (`LINK_PA` = the repo checkout), so the
  host-staged modules (runtime blocks, slim copies) are compiled exactly as check.py's flattening would include them.
- **Progress.** `build_all.py --progress` and `link_check.py --progress` keep one status line
  (`stage=build total=.. done=.. compiled=.. cached=.. failed=.. running=..`) that the runner appends to
  `results/<id>/progress.log` every `progress_minutes`.

## 7. Open points

- Not yet run on the host or on the root. The 184 staged modules and the largest ones (88–300+ MB) are
  unmeasured.
- Possible next speedups:
  - stub the derive-eq theorems of kept defs (the s1_subnum link dropped 178k re-derived copies);
  - parallel proof remap;
  - a C remap helper, if the 20–25 min link matters.
- Duplicate local names in the output index: harmless for mm0-c, but any future tool reading names from
  the linked `.mmb` must not assume they are unique.
