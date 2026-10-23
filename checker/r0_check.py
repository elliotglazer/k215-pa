"""Check the R0 receipt (k215_final_thm1) against the acceptance criteria.

    python3 -I checker/r0_check.py receipt/thm1/report.json [--module k215_final_thm1]
        [--map FROZEN_THEOREM=RECEIPT_THEOREM ...] [--host-specs DIR]
    python3 -I checker/r0_check.py --dry-run --module M [--map ...]     (no report: parts 3-4 on the current tree)

R0 is a receipt for the library module k215_final_thm1, not for targets/final.mm0 itself (a check of final.mm0 goes
through an acceptance copy, see checker/final_spec_verify.py). This script checks, read-only, the acceptance criteria
that apply to a library receipt, plus the link to final.mm0's theorem 1:
 1. report PASSED for MODULE, wrong_conclusion_rejected true, and reject-false.log's first mm0-c failure is a unify
    failure at MODULE.mm0's last theorem; status.json state done, checker capacity2;
 2. tools: checker_sha256 = pinned capacity2 mm0-c, compiler_sha256 = pinned mm0-rs, check_py_sha256 = pinned
    check.py (also the file on disk), vendor = pinned (pins from checker/final_spec_verify.py);
 3. spec: spec_sha256 = SHA-256 of mm0-rs join of MODULE.mm0 (byte-exact replica checker/mm0_join.py). Host-only
    .mm0 files of the closure are read from --host-specs (default: the latest results/*-slim-blocks/host-specs
    if present; in this repository every closure .mm0 file is in pa-mm0/, so none are needed);
    every .mm0 of the closure must have the hash the report lists;
 4. the frozen spec link: targets/final.mm0 and its closure match the pinned manifest; every manifest file under
    pa-mm0/ other than final.mm0 itself is in the report's sources at its manifest hash (so the definitions behind
    k215LiteralHalts and zfcInconsistent are the frozen ones); for every --map pair, RECEIPT_THEOREM is in
    checked_theorems and its statement in the joined spec (binders + math text, whitespace-normalized) equals
    FROZEN_THEOREM's in final.mm0. Equal binder text also means the receipt theorem has no hypotheses.
    Default map: K215_halts_iff_ZFC_inconsistent=K215_halts_iff_ZFC_inconsistent_final (theorem 1).
--dry-run checks parts 3 (closure, join) and 4 (frozen closure inside the module's closure at manifest hashes,
statements) on the current tree without a report, to test a candidate root before it is queued.
Exit 0 and "R0 OK" only if all pass. It does not replace the acceptance of targets/final.mm0.
"""
import argparse, glob, hashlib, json, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mm0_join
import final_spec_verify as V

ROOT, PA = V.ROOT, V.PA


def fail(m):
    raise SystemExit('FAIL: ' + m)


def statement(text, name):
    m = re.search(r'(?:^|[;\s])(?:pub\s+)?theorem\s+' + re.escape(name) + r'\b(.*?)\$(.*?)\$\s*;', text, re.S)
    if not m:
        fail('theorem %s not found' % name)
    return ' '.join(m.group(1).split()), ' '.join(m.group(2).split())


DEFAULT_MAP = ['K215_halts_iff_ZFC_inconsistent=K215_halts_iff_ZFC_inconsistent_final']


def check(report, module, maps, host_specs=None, label='R0'):
    pins = V.DEFAULT_PINS
    top = os.path.join(PA, module + '.mm0')
    r = src = None
    if report:
        rdir = os.path.dirname(os.path.abspath(report))
        r = json.load(open(report, encoding='utf-8-sig'))
        st = json.load(open(os.path.join(rdir, 'status.json'), encoding='utf-8-sig'))
        # 1
        if r.get('status') != 'PASSED' or r.get('module') != module:
            fail('report is not PASSED for %s' % module)
        if st.get('state') != 'done' or st.get('checker') != pins['checker_kind']:
            fail('status.json: state %r checker %r' % (st.get('state'), st.get('checker')))
        names = V.theorem_names(top)
        if r.get('wrong_conclusion_rejected') is not True:
            fail('wrong_conclusion_rejected is not true')
        why = V.reject_ok(os.path.join(rdir, 'reject-false.log'), names[-1])
        print('report PASSED; reject-false: %s rejected (%s)' % (names[-1], why))
        # 2
        for k, want in (('checker_sha256', pins['checker_sha256']), ('compiler_sha256', pins['compiler_sha256'])):
            if str(r.get(k, '')).lower() != want:
                fail('%s %s is not pinned %s' % (k, r.get(k), want))
        if str(st.get('check_py_sha256', '')).lower() != pins['check_py_sha256'] or \
                V.sha_file(os.path.join(PA, 'check.py')) != pins['check_py_sha256']:
            fail('check.py hash is not the pinned one')
        if r.get('vendor') != pins['vendor']:
            fail('vendor hashes are not the pinned ones')
        print('tools: capacity2 mm0-c, mm0-rs, check.py, vendor = pins')
        src = r.get('sources', {})
    else:
        print('dry run: no report; parts 3-4 on the current tree')
    # 3: join with host-only specs overlaid (temporary copies, removed afterwards)
    hs = host_specs
    if not hs:
        c = sorted(glob.glob(os.path.join(ROOT, 'results', '*-slim-blocks', 'host-specs')))
        hs = c[-1] if c else None
    added = []
    disk = {}
    try:
        if hs:
            for f in sorted(os.listdir(hs)):
                d = os.path.join(PA, f)
                if not os.path.exists(d):
                    open(d, 'wb').write(open(os.path.join(hs, f), 'rb').read()); added.append(d)
        clos = V.closure_of(top)
        for p in clos:
            if not p.startswith(PA + os.sep):
                continue
            k = os.path.relpath(p, PA).replace(os.sep, '/')
            disk[k] = V.sha_file(p)
            if src is not None and src.get(k) != disk[k]:
                fail('closure file %s: report %s, disk %s' % (k, src.get(k), disk[k]))
        j = mm0_join.join(top, PA)
    finally:
        for d in added:
            os.remove(d)
    jh = hashlib.sha256(j).hexdigest()
    if r is not None and r.get('spec_sha256') != jh:
        fail('spec_sha256 %s != joined %s' % (r.get('spec_sha256'), jh))
    print('spec: %d closure .mm0 files%s; joined %s (%d bytes, %d host-only overlaid)'
          % (len(disk), ' match the report' if r is not None else '', jh[:16], len(j), len(added)))
    # 4
    frozen = os.path.join(ROOT, pins['frozen'])
    if V.sha_file(frozen) != pins['frozen_sha256']:
        fail('targets/final.mm0 is not the pinned file')
    mp = os.path.join(ROOT, pins['manifest'])
    if V.sha_file(mp) != pins['manifest_sha256']:
        fail('manifest is not the pinned one')
    man = V.read_manifest(mp)
    nf = 0
    have = src if src is not None else disk
    for k, h in man.items():
        if k == pins['frozen'] or not k.startswith('pa-mm0/'):
            continue
        if V.sha_file(os.path.join(ROOT, k)) != h:
            fail('%s on disk differs from the manifest' % k)
        if have.get(k[len('pa-mm0/'):]) != h:
            fail('frozen-closure file %s is not in the %s at its manifest hash' % (k, 'report' if src is not None else 'closure'))
        nf += 1
    print('frozen link: %d frozen-closure files in the %s at manifest hashes' % (nf, 'report' if src is not None else 'closure'))
    ftext = open(frozen, 'rb').read().decode()
    jtext = j.decode('utf-8')
    fnames = V.theorem_names(frozen)
    for mpair in maps:
        fn, _, rn = mpair.partition('=')
        if fn not in fnames or not rn:
            fail('--map %r: expected FROZEN_THEOREM=RECEIPT_THEOREM with a theorem of final.mm0' % mpair)
        if r is not None and rn not in r.get('checked_theorems', []):
            fail('%s is not in checked_theorems' % rn)
        sf = statement(ftext, fn)
        sr = statement(jtext, rn)
        if sf != sr:
            fail('statements differ: final.mm0 %s %r vs %s %r' % (fn, sf, rn, sr))
        print('  %s states exactly %s: %s $ %s $' % (rn, fn, sf[0], sf[1]))
    print('%s OK%s' % (label, ' (dry run: no receipt checked)' if r is None else ''))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('report', nargs='?')
    ap.add_argument('--module', default='k215_final_thm1')
    ap.add_argument('--map', action='append')
    ap.add_argument('--host-specs')
    ap.add_argument('--dry-run', action='store_true')
    a = ap.parse_args()
    if not a.report and not a.dry_run:
        fail('give a report.json (e.g. receipt/thm1/report.json), or --dry-run')
    check(None if a.dry_run else a.report, a.module, a.map or DEFAULT_MAP, a.host_specs)


if __name__ == '__main__':
    main()
