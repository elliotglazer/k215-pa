# translator/ — MMB tooling for the certifying translator (B2)

Pure python3 (stdlib only). It reads, rewrites and writes `.mmb` files as
produced by `tools/mm0-rs compile`, and gives a DAG-preserving view of proof
streams for the later translation pass (negative + Friedman translation, with
nat terms turned into set-valued graphs). Every file it writes is meant to be
checked by `tools/mm0-c out.mmb < spec.mm0`.

```
python3 -m translator stats build/peano.mmb
python3 -m translator roundtrip build/peano.mmb out.mmb [--index preserve|rebuild|none] [--reencode]
python3 -m translator dump build/peano.mmb ax_mp
python3 -m unittest translator.tests.test_peano -v     # from the repo root
```

## Files
- `mmb_format.py`: constants (sort flags, statement/proof/unify opcodes,
  index ids) and the command codec (`unpack_cmd`, `iter_cmds`, `encode_cmd(s)`,
  `encode_stmt`). Proof and unify commands use the minimal data width, and
  statements use mm0-rs `write_cmd_bytes` widths, so a re-encoded file is
  byte-identical.
- `mmb_reader.py`: the data model and `MMBFile` (mmap-backed, lazy).
- `mmb_writer.py`: `MMBWriter` (streaming) and `write_mmb` (re-emit a model).
- `proof_dag.py`: `build_stmt_dag` (proof stream to DAG) and `decode_unify`
  (table unify stream to expression DAG).

## Data model (everything stays in MMB id space)
- `MMBFile.sorts[i]`: `Sort(id, mods, name)`. `mods` is the bit set
  PURE=1, STRICT=2, PROVABLE=4, FREE=8. For peano: wff (provable), nat, set (strict).
- `MMBFile.terms[i]`: `Term(id, sort, is_def, args, ret, unify, name, var_names)`.
  `args` holds the raw u64 binder words: bit 63 marks a bound var, bits 56–62
  hold the sort, and bits 0–54 hold the bound-variable dependency set. Use
  `mmb_format.type_bound/type_sort/type_deps` to read them. `ret` is the return
  word, whose deps give the bound args the value depends on. For a def, `unify`
  is the body as a unify command list, End excluded: prefix order, `URef i` is
  arg i or a saved subterm, `UTermSave` saves a subterm, and `UDummy s` is a def
  dummy. Term ids are positions in this list.
- `MMBFile.thms[i]`: `Thm(id, args, unify, name, var_names, hyp_names, num_hyps, kind)`.
  `unify` encodes the conclusion, then for each hypothesis in reverse order:
  `UHyp` followed by the hyp expr. `kind` is `axiom`, `thm` or `local_thm`, and
  is set while the stream is iterated.
- `MMBFile.iter_stmts()`: yields `Stmt(op, kind, ref, body, offset, new_cmds)`
  lazily in declaration order. `kind` is one of sort, term, def, local_def,
  axiom, thm or local_thm. `ref` is the sort, term or thm id it introduces.
  `body` is a memoryview of the proof command stream, including its End; it is
  empty for sort and term. `Stmt.cmds()` decodes `(op, data)` pairs on demand.
  Setting `new_cmds` (a list without End) replaces the proof when the file is
  written.
- `MMBFile.tail` / `tail_offset`: the raw bytes after the proof stream (the
  debugging index). `index_tables()` lists the index header
  (Name/VarN/HypN/Delm/Nota/Lisp). Names come from Name, VarN and HypN only;
  notation and lisp data are carried along as opaque bytes.

## Proof DAG (`build_stmt_dag(mmb, stmt) -> ProofDAG`)
This runs mm0-c's stack machine symbolically, without unification checks. You
get a flat `nodes` table, `heap` (the stack elements stored in the heap, in
heap order: binders first, then Dummy / *Save / Hyp / ConvSave entries),
`hyps` (the hypothesis expression nodes) and `result`. Every heap entry is one
node, shared by every `Ref` to it, so the DAG has the same size as the stream
and is never expanded. Node kinds:

| kind | node | meaning |
|---|---|---|
| expr | `('var', i)`, `('dummy', sort)`, `('app', termid, args)` | |
| proof | `('hyp', k, e)`, `('thm', thmid, args, hyp_proofs, e)`, `('conv', e1, p2, c)`, `('sorry', e)` | proves `e` (conv proves e1 from p2 : e2) |
| conv | `('refl', e)`, `('symm', c)`, `('cong', termid, cs)`, `('unfold', termid, lhs, e, c)`, `('cut', c)`, `('cref', c)` | a proof of e1 = e2 |

Stack elements are `('E', n)`, `('P', n, e)`, `('C', e1, e2, n)` (a saved
conversion) and `('CO', e1, e2, hole)` (an open obligation). In a `thm`, the
hyp proofs come in declaration order and the args in binder order. A def or
axiom stream ends with `('E', body_or_conclusion)`; a theorem stream ends with
`('P', proof, e)`.
`decode_unify(mmb, decl)` returns `(nodes, root, hyps)` in the same expression
format (hyps in declaration order).
The tests check, for every statement of peano.mmb, that the proof-stream DAG
gives the same conclusion and hypotheses as the table's unify stream.

## Writer (`MMBWriter`)
`add_sort` / `add_term` / `add_thm` register table entries. These must all be
added before `finish`, but they can be interleaved with `add_stmt`.
`add_stmt(op, body=|cmds=)` spools stream statements to a temp file, which
keeps memory modest. `finish(index)` writes the header, sorts, the 8-aligned
term table and arg arrays (each def followed by its unify stream and End), the
thm table, the stream with its final End, and then the index. This is the
mm0-rs `export.rs` layout. The index is written in one of three modes:
- `rebuild` fresh Name/VarN/HypN tables, plus empty Delm/Nota tables, built
  from the `name`, `var_names` and `hyp_names` fields. This mode is for
  translated output, because it gives mm0-c error messages names.
- `preserve` copies the original tail and relocates its pointers, padding the
  stream so the shift is a multiple of 8. It remaps Name.p_proof through the
  statement offsets. It is valid only when the declaration list is unchanged.
- `none` writes `p_index = 0`.

`write_mmb(mmb, path, index, reencode)` re-emits a parsed file. Tables are
always re-encoded from the model. With `reencode=True`, every proof is also
decoded and re-encoded. `mmb.override_stmts` can supply an edited statement list.

## Results on foundation/peano.mm1 (mm0-rs 0.1.0)
- 3 sorts, 12 terms, 158 defs (104 def plus 54 local def), 26 axioms and
  2700 theorems (55 pub plus 2645 local). The file is 963,640 bytes.
- Proof commands: 245,243 in total. Ref 151232, TermSave 35001, Term 24826,
  Thm 23328, Refl 2934, Cong 1851, Unfold 1442, Hyp 1304, Dummy 1206, Conv 1166,
  ThmSave 553, Symm 197, ConvCut 95, ConvSave 95, Save 13.
- Unify commands: URef 18403, UTerm 16108, UHyp 1304, UTermSave 270, UDummy 152.
- Round trip with `preserve` (and with `--reencode`) is byte-identical, and
  mm0-c exits 0. Round trip with `rebuild` or `none` is semantically equal, and
  mm0-c exits 0.
- Negative tests: flipping the thm-id byte of one `Thm` command makes mm0-c
  exit 255 ("unify failure at ref"). Dropping a proof's last command through
  the model is also rejected.
- The whole-file DAG build needs about 0.4 s and under 20 MB RSS.

## Known gaps
- No semantic checking. The DAG builder trusts the stream; mm0-c is the checker.
- The DAG/unify cross-check skips defs with dummies, because dummy identity is
  not matched up.
- The Lisp, Nota and Delm index tables are not parsed. `rebuild` mode drops
  Lisp and notation, which mm0-c does not need.
- No `.mmu` output, and no `.mm0` spec emission. The HA-side `.mm0` must be
  written separately.
- `MMBFile` keeps the whole term/thm tables in memory (but not proofs). Files
  of several GB only need their tables to fit.

## SPIKE (branch spike-translate-fragment, experimental, not accepted)
Built on the DRAFT foundation hpeano.mm0 (branch b0-hpeano-draft, not approved).
- `deps.py`: `python3 -m translator.deps build/peano.mmb [--list]` reports which defs and
  theorems depend transitively on `the`, theid/the0 or ax_3.
- `negtrans.py`: the combined negative+Friedman translation with nat terms translated to
  GRAPHS (sets), which removes `the`. A regular nat variable becomes a set variable, a bound
  one stays nat and appears as `sg x = {y | y = x}`; `0, suc, +, *, the` become `sg 0, sucG,
  addG, mulG, theG`; `=` and `e.` become `eqG`, `elG`. Each nat argument a callee needs gets a
  `nsing a^ A` side proof (ns_sg/ns_suc/ns_add/ns_mul/ns_the and generated ns_D_N lemmas), as
  wff arguments get stability proofs.
  `python3 -m translator.negtrans build/peano.mmb build/negtrans-lib.mmb out.mmb --mm0 out.mm0 --pub-all`
  writes the .mmb and a generated spec (hpeano.mm0, the lib and translated defs, and the translated
  theorem statements). Check it with `tools/mm0-c out.mmb < out.mm0`.
  Result on peano.mm1: all 2700 theorems and all 158 defs translate (incl. if/fst/snd/pr/sub/
  div/ns/app); mm0-c exit 0 with every translated theorem public; one flipped byte is rejected.
  Proof bytes 2.03x (median 2.01x, max 3.11x), statements 2.10x, defs 1.65x; 2.02 side
  hypotheses per theorem (3939 nsing, 1512 stability); 35 st_ and 86 ns_ lemmas generated.
  Translation takes about 2 s.
- `spike/gen_lib.py` generates `spike/negtrans-lib.mm1`, which holds the hand-written HA lemmas
  (the graph library: sg, eqG/elG/nsing, sucG/addG/mulG/theG
  and their nsing lemmas, eqG refl/sym/trans/congruence; stability lemmas; all 26 peano axiom
  translations, including theid/the0, proved from the draft hpeano axioms; 253 lemmas). Its lambda proofs are compiled to
  ax_1/ax_2/ax_mp by `spike/lamc.py`. Compile it with
  `tools/mm0-rs compile spike/negtrans-lib.mm1 build/negtrans-lib.mmb`.
- Test: `python3 -m unittest translator.tests.test_negtrans -v`.

## B5: Pi2 recovery (branch b5-recovery)
`python3 b5/gen_b5.py` (test: `python3 -m unittest translator.tests.test_b5`) builds
`b5/b5-src.mm1` (peano.mm1 + the approved bd defs + synthetic tests), translates it, and
recovers the Pi2 statements over hpeano; `tools/mm0-c build/b5-out.mmb < build/b5-out.mm0` exits 0.
- `b5/hand.mm1t`: schemas over hpeano. `dec p := p \/ ~p`, `rel p q A := (p \/ A -> q) /\ (q -> p \/ A)`,
  `isv X a A := nsing X A /\ eqG X (sg a) A`. Decidable equality by induction (`deceq`, via a
  `finds` induction lemma derived from peano5), `<`/`<=` arithmetic, bounded quantifiers over a
  decidable matrix (`bdall_lt/le`, `dec_al_*`, `dec_ex_*`), term graphs (`isv_suc/add/mul`),
  closure of rel/dec under = <= < ~ -> /\ \/ E. and bounded A. (`rel_*`, `dec_*`).
- generated per def of bd_certs (and the support defs d1..d10, ne): `isv_D` (nat defs),
  `rel_D`, `dec_D` (wff defs), each by structural recursion on the body; translated defs are
  supplied by the library exactly as the translator makes them (it checks the bodies).
- recovery: `rec_X` turns the translation of `A. h (D h -> E. w D' w)` at Friedman
  `A := E. w D' w` into the statement itself (renaming via `ren_D`, two instances of `rel_D`).
  Post-step appends `tsig1_H`, `tsig2_H` (synthetic Pi2 theorems proved in peano, translated,
  recovered) and `K215_sigma1_H`, `K215_sigma2_H` (translated statement as hypothesis).

## B6: driver for the K215 Theorem 1 run (branch b6-driver)
`python -B -I b6/b6.py --src IN.mmb --out DIR --tools TOOLS [--repo ROOT] [--rehearsal] [--rebuild-lib]`
translates IN.mmb against the pinned HA library `b6/b6-lib.mmb` (generated by `b6/gen_lib.py`
from sources: the B5 library without test defs; deterministic), appends `K215_sigma1`/`K215_sigma2`
(rec_K215_sigma{1,2} applied to the translated K215_sigma{1,2}; `--rehearsal`: to the translated
K215_sigma{1,2}_of, with the translated hT kept as hypothesis), writes DIR/b6-out.mmb and
DIR/b6-out.mm0 = hpeano.mm0 + bd defs (verbatim) + the approved lines of b4/b4_statements.mm0,
runs mm0-c and an F.-conclusion control, and writes DIR/report.json. Exit 0 iff mm0-c accepts,
the control is rejected and the final statements are the approved text.
Tests: `python3 -m unittest translator.tests.test_b6` (needs `b4/build.sh` and `b5/gen_b5.py` outputs).

Translator changes for real input: every traversal is iterative (K215 proofs exceeded Python's
recursion limit); `stream_to`/`finish_stream` stream statements to the writer's spool (in DIR);
output names are made unique (`renamed` in the report); statement unify streams share repeated
subterms (UTermSave); each emitted statement is checked against mm0-c's fixed per-statement
capacities (`LIMITS`: heap/uheap 65536, store 64 MiB, stack 65536, hyp and unify stacks 256,
55 bound variables) and refused with a reason instead of failing late in mm0-c.
