"""Write the .mm0 spec of a gen7 .mm1 module: imports, comments, defs, pub theorem statements."""
import re, sys

src, dst = sys.argv[1], sys.argv[2]
s = open(src).read()
out, i = [], 0
DEF = re.compile(r'(@_ )?(abstract )?def ')   # matched at i: no copy of s[i:] per line (quadratic on 35 MB)
while i < len(s):
    if s.startswith('import "', i):
        j = s.index(';', i)
        out.append(s[i:j + 1].replace('.mm1"', '.mm0"')); i = j + 1; continue
    if s.startswith('--', i) and (i == 0 or s[i - 1] == '\n'):
        j = s.find('\n', i); j = len(s) if j < 0 else j
        out.append(s[i:j]); i = j; continue
    m = DEF.match(s, i) if (i == 0 or s[i - 1] == '\n') else None
    if m:
        j = s.index('$;', i)
        out.append('def ' + s[m.end():j + 2]); i = j + 2; continue
    if s.startswith('pub theorem ', i) and (i == 0 or s[i - 1] == '\n'):
        k = s.index(':', i)
        # the statement is the last $...$ before ' =' that is not inside a binder
        m2 = re.compile(r'\$\s*=').search(s, k)
        st = s[i + 4:m2.start() + 1]
        out.append(st + ';'); i = m2.end(); continue
    i += 1
open(dst, 'w', newline='\n').write('\n\n'.join(out) + '\n')
