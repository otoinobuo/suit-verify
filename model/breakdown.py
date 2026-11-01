"""Break the draft/truth disagreements down by cause, and list small realistic counterexamples."""
import collections
from suitver import *

V = versions()
cause = collections.Counter()
for m in V:
    mrel, mpre = parse(m)
    for c in V:
        crel, cpre = parse(c)
        d = draft_cmp(m, c)
        for op in OPS:
            k = classify(op, m, c)
            if k == 'agree':
                continue
            if d is None:
                cause[('D undefined: the component array ends first', k)] += 1
            elif len(crel) < 3 or (mpre is not None and len(mrel) < 3):
                cause[('B encoding: fewer than 3 release integers (1.2-beta vs 1.2.0-beta)', k)] += 1
            elif mpre is None and cpre is not None:
                cause[('A prefix: a pre-release compares equal to a full version [M,m,p]', k)] += 1
            elif mpre is not None and cpre is not None:
                cause[('C number of pre-release identifiers (rc vs rc.1)', k)] += 1
            else:
                cause[('other', k)] += 1
for (cz, k), n in sorted(cause.items()):
    print(f'{n:7d}  {cz:60s} {k}')
print()
print('realistic examples (manifest, component, draft result, SemVer truth):')
ex = [('ge', [2,0,0], [2,0,0,-1,1]), ('eq', [2,0,0], [2,0,0,-1,1]), ('lt', [1,10,0], [1,10,0,-1,1]),
      ('eq', [1,2,-2], [1,2,0,-2]), ('gt', [1,2,-2], [1,2,0,-2]), ('eq', [2,0,0,-1], [2,0,0,-1,1]),
      ('gt', [2,0,0,-1], [2,0,0,-1,1]), ('gt', [2,0,0,-1,1], [2,0,0,-1]), ('ge', [1,2,3], [1,2]),
      ('ge', [2,0], [2,0,-1,1]), ('ge', [2,0,0], [2,0,-1,1])]
for op, m, c in ex:
    print(f'  {op:2s} {str(m):18s} {str(c):18s} draft={apply(op, draft_cmp(m, c))!s:5s} truth={truth(op, m, c)!s:5s} fixed={apply(op, fixed_cmp(m, c))}')
