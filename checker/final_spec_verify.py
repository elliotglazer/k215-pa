"""Verify that an acceptance copy of a frozen spec checks exactly the frozen statements.

    python3 -I checker/final_spec_verify.py FROZEN.mm0 MODULE [--report results/<id>/report.json]
        [--proof PROOF.mm1] [--control THEOREM=LOG ...] [--write] [--pins PINS.json]

check.py only accepts module names [a-z][a-z0-9_]* that live directly in pa-mm0/, so a frozen spec such
as pa-mm0/targets/final.mm0 is checked through a copy pa-mm0/MODULE.mm0. This script defines the copy and
proves it changes nothing that mm0-c reads. Every check below must pass; then it prints "OK".

0. Pins (review items R1, R2). Built in: the frozen file pa-mm0/targets/final.mm0
   (sha256 522671fc...), its closure manifest manifests/final-spec-closure.sha256 (sha256 bd8202cb...,
   added in commit 24e19626 and unchanged since), the capacity2 mm0-c, mm0-rs, check.py and the vendor
   hashes of check.py's expected_vendor. --pins FILE replaces them (only for toy tests): the result line
   then says "OK with NON-DEFAULT pins ..." and is not an acceptance of targets/final.mm0.
1. (R1) The frozen file is the pinned one, and its .mm0 import closure on disk is exactly the manifest:
   the same set of files (vendor peano.mm0 included), every hash equal.
2. The copy is the frozen file byte for byte, except that each import statement's path "../X" becomes
   "X" (with --write it is generated that way). Every import must name a file that both spellings resolve
   to. Nothing else may differ.
3. The joined specs (mm0-rs join, replicated byte-exactly by checker/mm0_join.py, cwd pa-mm0) of the
   frozen file and of the copy are compared. They may differ only in mm0-rs's comment lines that name
   the top file (header line, its "-- * " line, its banner). Every non-comment byte must be equal.
4. With --report (results/<id>/report.json; status.json and reject-false.log are read from the same
   directory):
   - report.json is PASSED for MODULE, and its spec_sha256 equals the SHA-256 of the joined copy, so
     mm0-c checked exactly that text;
   - (R1) report.sources lists the copy at its hash and every other closure file under pa-mm0/ at its
     manifest hash; report.vendor equals the pinned vendor hashes, whose peano.mm0 is the manifest's;
   - (R2) report.checker_sha256 and compiler_sha256 are the pinned mm0-c and mm0-rs; status.json has
     state "done", the pinned checker kind (capacity2) and the pinned check_py_sha256, which is also the
     hash of pa-mm0/check.py on disk;
   - (R4) report.checked_theorems is the frozen file's theorem names, in order;
   - (R3) report.wrong_conclusion_rejected is true, and reject-false.log shows mm0-c's first failure at
     the last frozen theorem with a unify failure (so a crash or a resource failure does not count).
     --control NAME=LOG (optional, repeatable) applies the same test to the log of an extra mm0-c run
     with theorem NAME replaced by F.
5. With --report and --proof PROOF.mm1: rebuilding MODULE.mm1 with checker/make_acceptance_mm1.py from
   FROZEN and PROOF gives exactly the .mm1 whose hash the report lists, i.e. the checked proof input is
   the deterministic localization of PROOF's closure (informational: mm0-c, not this, checks the proofs).
Exit 0 and "OK" only if every check passes.
"""
import argparse, hashlib, json, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mm0_join

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PA = os.path.join(ROOT, 'pa-mm0')

DEFAULT_PINS = {
    'name': 'targets/final.mm0 (built in)',
    'frozen': 'pa-mm0/targets/final.mm0',
    'frozen_sha256': '8f531d23514e962931ba6c041cb15f08045e86d6414863ac249f02f34bd26c5d',
    'manifest': 'manifests/final-spec-closure.sha256',
    'manifest_sha256': 'a7021d3c518993ae6f4f048fd4025138e0bbf872e81bef29a58e18c862d1a911',
    'manifest_commit': 'k215-pa',
    'checker_kind': 'capacity2',
    'checker_sha256': 'bba77622e7540e3f68eb1cc0c202c1cfcdaa2c5bed01754eb0b86d143e4f6371',
    'compiler_sha256': 'c3be4fd028d3590a384f499c1a8e1ac762bcca957f6b20fb1a44794f54479412',
    'check_py_sha256': 'a708f933f94a9ac159a488cbe5b99c897593f0b78b268ac4ee84fc5c311ab750',
    'vendor': {
        'peano.mm0': '463a7d6e4f4791313dedcfd737053dcf2cc07b466371e263c38a994c6fb72052',
        'peano.mm1': '13fd383aa02e434cba1350e9a8f12c440b5114d22f26506fece4aecdf1370079',
        'peano.mmu': '3405aa9f99417850acb766845cc0031651bcaacb7dc9b87e25e6598bdf872cfd',
    },
}
PIN_KEYS = set(DEFAULT_PINS)


def fail(msg):
    raise SystemExit('FAIL: ' + msg)


def sha_file(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def expected_copy(frozen):
    text = open(frozen, 'rb').read().decode('utf-8')
    out, pos = [], 0
    for s, e, f in mm0_join.stmts_imports(text):
        if not f.startswith('../'):
            fail('import %r of the frozen file does not start with ../' % f)
        a = os.path.realpath(os.path.join(os.path.dirname(frozen), f))
        b = os.path.realpath(os.path.join(PA, f[3:]))
        if a != b:
            fail('import %r resolves differently from pa-mm0/' % f)
        stmt = text[s:e]
        out.append(text[pos:s] + stmt.replace('"' + f + '"', '"' + f[3:] + '"', 1))
        pos = e
    out.append(text[pos:])
    return ''.join(out).encode('utf-8')


def code_lines(b):
    return [l for l in b.decode('utf-8').split('\n') if not l.lstrip().startswith('--')]


def closure_of(top):
    """Real paths of the .mm0 import closure of top (top included)."""
    seen = set()
    def walk(p):
        p = os.path.realpath(p)
        if p in seen: return
        seen.add(p)
        t = open(p, 'rb').read().decode('utf-8')
        for _, _, f in mm0_join.stmts_imports(t):
            walk(os.path.join(os.path.dirname(p), f))
    walk(top)
    return seen


def strip_comments_and_math(text):
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j < 0 else j
        elif text[i] == '$':
            j = text.find('$', i + 1)
            if j < 0: fail('unterminated math string in the frozen file')
            out.append(' '); i = j + 1
        else:
            out.append(text[i]); i += 1
    return ''.join(out)


def theorem_names(path):
    code = strip_comments_and_math(open(path, 'rb').read().decode('utf-8'))
    return re.findall(r'(?:^|[;\s])(?:pub\s+)?theorem\s+([A-Za-z_][A-Za-z0-9_]*)', code)


def load_pins(path):
    if path is None:
        return dict(DEFAULT_PINS), True
    p = json.load(open(path, encoding='utf-8'))
    if set(p) != PIN_KEYS:
        fail('pins file %s must have exactly the keys %s' % (path, sorted(PIN_KEYS)))
    return p, p == DEFAULT_PINS


def read_manifest(path):
    m = {}
    for line in open(path, 'rb').read().decode('utf-8').split('\n'):
        if not line.strip() or line.startswith('#'):
            continue
        mo = re.fullmatch(r'([0-9a-f]{64})  (\S+)', line)
        if not mo: fail('malformed manifest line %r' % line)
        if mo.group(2) in m: fail('manifest lists %s twice' % mo.group(2))
        m[mo.group(2)] = mo.group(1)
    return m


def reject_ok(log, name):
    """The first mm0-c failure line in log is 'at NAME: ...unify failure...'."""
    if not os.path.isfile(log):
        fail('reject log %s is missing' % log)
    text = open(log, 'rb').read().decode('utf-8', 'replace')
    hits = re.findall(r'^at ([^\s:]+): (.*)$', text, re.M)
    if not hits:
        fail('%s names no failing statement (crash or resource failure?)' % log)
    who, why = hits[0]
    if who != name or 'unify failure' not in why:
        fail('%s: first failure is "at %s: %s", expected a unify failure at %s' % (log, who, why.strip(), name))
    return why.strip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('frozen')
    ap.add_argument('module')
    ap.add_argument('--report')
    ap.add_argument('--write', action='store_true')
    ap.add_argument('--proof')
    ap.add_argument('--control', action='append', default=[], metavar='THEOREM=LOG')
    ap.add_argument('--pins')
    a = ap.parse_args()
    pins, default = load_pins(a.pins)
    if a.control and not a.report:
        fail('--control needs --report')
    frozen = os.path.realpath(a.frozen)

    # 1. (R1) frozen file and closure against the pinned manifest
    if frozen != os.path.realpath(os.path.join(ROOT, pins['frozen'])):
        fail('frozen file %s is not the pinned %s' % (a.frozen, pins['frozen']))
    if sha_file(frozen) != pins['frozen_sha256']:
        fail('%s has sha256 %s, pinned %s' % (pins['frozen'], sha_file(frozen), pins['frozen_sha256']))
    mpath = os.path.join(ROOT, pins['manifest'])
    if not os.path.isfile(mpath):
        fail('closure manifest %s is missing' % pins['manifest'])
    msha = sha_file(mpath)
    if msha != pins['manifest_sha256']:
        fail('manifest %s has sha256 %s, pinned %s' % (pins['manifest'], msha, pins['manifest_sha256']))
    man = read_manifest(mpath)
    clos = closure_of(frozen)
    rels = {}
    for p in clos:
        if not p.startswith(ROOT + os.sep):
            fail('closure file %s lies outside the repository' % p)
        rels[os.path.relpath(p, ROOT).replace(os.sep, '/')] = p
    if set(rels) != set(man):
        fail('closure and manifest differ: only on disk %s; only in manifest %s'
             % (sorted(set(rels) - set(man))[:5], sorted(set(man) - set(rels))[:5]))
    for k in sorted(rels):
        if sha_file(rels[k]) != man[k]:
            fail('%s does not match the manifest' % k)
    if man.get(pins['frozen']) != pins['frozen_sha256']:
        fail('manifest does not list %s at the pinned hash' % pins['frozen'])
    print('pins: %s' % pins['name'])
    print('manifest %s  sha256 %s (commit %s): %d files, all match on disk'
          % (pins['manifest'], msha, pins['manifest_commit'], len(man)))

    # 2. the copy
    copy = os.path.join(PA, a.module + '.mm0')
    exp = expected_copy(frozen)
    if a.write:
        open(copy, 'wb').write(exp)
    if not os.path.isfile(copy) or open(copy, 'rb').read() != exp:
        fail('%s is not the frozen file with only the import paths rewritten' % copy)

    # 3. joined specs
    jf, jc = mm0_join.join(frozen, PA), mm0_join.join(copy, PA)
    if code_lines(jf) != code_lines(jc):
        fail('joined specs differ outside comment lines')
    lf, lc = jf.decode().split('\n'), jc.decode().split('\n')
    diff = [(x, y) for x, y in zip(lf, lc) if x != y]
    allowed = lambda x, y: x.startswith('--') and y.startswith('--')
    if len(lf) != len(lc) or len(diff) > 5 or not all(allowed(x, y) for x, y in diff):
        fail('joined specs differ in structure')
    print('joined frozen %s  %d bytes' % (hashlib.sha256(jf).hexdigest(), len(jf)))
    print('joined copy   %s  %d bytes' % (hashlib.sha256(jc).hexdigest(), len(jc)))
    for x, y in diff:
        print('  comment line differs: %r -> %r' % (x, y))

    # 4. the host report
    if a.report:
        rdir = os.path.dirname(os.path.abspath(a.report))
        r = json.load(open(a.report, encoding='utf-8-sig'))
        if r.get('status') != 'PASSED' or r.get('module') != a.module:
            fail('report is not a PASSED report for %s' % a.module)
        if r.get('spec_sha256') != hashlib.sha256(jc).hexdigest():
            fail('report spec_sha256 %s is not the joined copy' % r.get('spec_sha256'))
        # R1: sources
        src = r.get('sources', {})
        want = {a.module + '.mm0': hashlib.sha256(exp).hexdigest()}
        for k, p in rels.items():
            if p == frozen or not p.startswith(PA + os.sep):
                continue
            want[os.path.relpath(p, PA).replace(os.sep, '/')] = man[k]
        for k in sorted(want):
            if src.get(k) != want[k]:
                fail('report source hash for %s is %s, pinned %s' % (k, src.get(k), want[k]))
        if r.get('vendor') != pins['vendor']:
            fail('report vendor hashes %s are not the pinned ones' % r.get('vendor'))
        vend = [k for k in man if k.endswith('/peano.mm0')]
        if len(vend) != 1 or man[vend[0]] != pins['vendor']['peano.mm0']:
            fail('the manifest peano.mm0 is not the pinned vendor file')
        print('report: PASSED, spec_sha256 = joined copy, %d spec sources + vendor = manifest' % len(want))
        # R2: tools
        if str(r.get('checker_sha256', '')).lower() != pins['checker_sha256']:
            fail('report checker_sha256 %s is not the pinned mm0-c %s' % (r.get('checker_sha256'), pins['checker_sha256']))
        if str(r.get('compiler_sha256', '')).lower() != pins['compiler_sha256']:
            fail('report compiler_sha256 %s is not the pinned mm0-rs %s' % (r.get('compiler_sha256'), pins['compiler_sha256']))
        spath = os.path.join(rdir, 'status.json')
        if not os.path.isfile(spath):
            fail('status.json missing next to the report')
        st = json.load(open(spath, encoding='utf-8-sig'))
        if st.get('state') != 'done':
            fail('status.json state is %r, not done' % st.get('state'))
        if st.get('checker') != pins['checker_kind']:
            fail('status.json checker is %r, not %s' % (st.get('checker'), pins['checker_kind']))
        if str(st.get('check_py_sha256', '')).lower() != pins['check_py_sha256']:
            fail('status.json check_py_sha256 %s is not the pinned check.py' % st.get('check_py_sha256'))
        if sha_file(os.path.join(PA, 'check.py')) != pins['check_py_sha256']:
            fail('pa-mm0/check.py on disk is not the pinned check.py')
        print('tools: mm0-c %s..., mm0-rs %s..., check.py %s..., checker %s, state done'
              % (pins['checker_sha256'][:8], pins['compiler_sha256'][:8], pins['check_py_sha256'][:8], pins['checker_kind']))
        # R4: theorem names
        names = theorem_names(frozen)
        if not names:
            fail('the frozen file has no theorem')
        if r.get('checked_theorems') != names:
            fail('report checked_theorems %s are not the frozen theorems %s' % (r.get('checked_theorems'), names))
        print('theorems: %s' % ', '.join(names))
        # R3: liveness of the spec comparison
        if r.get('wrong_conclusion_rejected') is not True:
            fail('report does not record wrong_conclusion_rejected = true')
        why = reject_ok(os.path.join(rdir, 'reject-false.log'), names[-1])
        print('reject-false: %s rejected (%s)' % (names[-1], why))
        for c in a.control:
            nm, _, log = c.partition('=')
            if nm not in names or not log:
                fail('--control %r: expected FROZEN_THEOREM=LOG' % c)
            why = reject_ok(log, nm)
            print('control: %s rejected (%s)' % (nm, why))
        if a.proof:
            import make_acceptance_mm1
            data, _ = make_acceptance_mm1.build(frozen, a.proof)
            if src.get(a.module + '.mm1') != hashlib.sha256(data).hexdigest():
                fail('%s.mm1 in the report is not the localization of %s' % (a.module, a.proof))
            print('report: %s.mm1 = make_acceptance_mm1(%s, %s)' % (a.module, a.frozen, a.proof))
    if default:
        print('OK')
    else:
        print('OK with NON-DEFAULT pins (%s): not an acceptance of targets/final.mm0' % pins['name'])


if __name__ == '__main__':
    main()
