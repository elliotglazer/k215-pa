"""Write a synthetic MM0 spec and matching MMB v1 binary to stress mm0-c's name tries.

Usage: synth_mmb.py OUTPREFIX NTERMS NAXIOMS [false]
Spec: provable sort wff; term imp; NTERMS terms `srcLCompactSubsetG<i> (a b: wff): wff`;
NAXIOMS axioms `axL11<i> (a: wff): $ a $`; then `theorem th (a: wff): $ a $` proved from axiom 0.
With `false`, the final theorem's spec statement is replaced by `$ imp a a $` (must be rejected).
"""
import struct
import sys

out, nterms, naxioms = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
false = len(sys.argv) > 4 and sys.argv[4] == 'false'
nterm_total = 1 + nterms
nthm_total = max(naxioms, 1) + 1
naxioms = max(naxioms, 1)

spec = ['provable sort wff;', 'term imp (a b: wff): wff;']
spec += ['term srcLCompactSubsetG%d (a b: wff): wff;' % i for i in range(nterms)]
spec += ['axiom axL11%d (a: wff): $ a $;' % i for i in range(naxioms)]
spec.append('theorem th (a: wff): $ imp a a $;' if false else 'theorem th (a: wff): $ a $;')
with open(out + '.mm0', 'w') as f:
    f.write('\n'.join(spec) + '\n')


def align(buf, n):
    while len(buf) % n:
        buf.append(0)


b = bytearray(40)
b += bytes([4])                          # sort table: wff is provable
align(b, 8)
term_data = len(b); b += bytes(24)      # shared term_data: two wff args, ret wff (all zero)
thm_data = len(b); b += bytes(8)        # shared thm_data: one wff arg
b += bytes([0x32, 0x00])                # unify: URef 0 (conclusion a), END
align(b, 8)
p_terms = len(b)
b += struct.pack('<HBBI', 2, 0, 0, term_data) * nterm_total
align(b, 8)
p_thms = len(b)
b += struct.pack('<HHI', 1, 0, thm_data) * nthm_total
p_proof = len(b)
b += bytes([0x44, 2])                                   # Sort
b += bytes([0x45, 2]) * nterm_total                     # Term statements
b += bytes([0x42, 4, 0x12, 0x00]) * naxioms             # Axiom: Ref 0, END
b += bytes([0x46, 6, 0x12, 0x12, 0x14, 0x00])           # Thm: Ref 0 (arg), Ref 0 (concl), Thm 0, END
b += bytes(8)                                           # END + read-ahead padding
struct.pack_into('<IBBHIIIIIIQ', b, 0, 0x42304D4D, 1, 1, 0, nterm_total, nthm_total,
                 p_terms, p_thms, p_proof, 0, 0)
with open(out + '.mmb', 'wb') as f:
    f.write(b)
print(out, 'terms', nterm_total, 'thms', nthm_total, 'mmb bytes', len(b))
