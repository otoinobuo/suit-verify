#!/usr/bin/env python3
"""Model of the encoding proposed by B. Moran on suit@ietf.org (2026-11-01) vs SemVer 2.0.0 Section 11."""
import itertools
END=-24
def enc(v):
    r,st,ids=v
    if st is None: return list(r)+[0]
    return list(r)+[st]+list(ids)+[END]
def semver(a,b):
    """-1 if a<b. Numeric identifiers; class alpha<beta<rc; final above any prerelease; more fields is higher."""
    if a[0]!=b[0]: return -1 if a[0]<b[0] else 1
    if a[1] is None and b[1] is None: return 0
    if a[1] is None: return 1
    if b[1] is None: return -1
    if a[1]!=b[1]: return -1 if a[1]<b[1] else 1
    x,y=a[2],b[2]
    for p,q in zip(x,y):
        if p!=q: return -1 if p<q else 1
    return (len(x)>len(y))-(len(x)<len(y))
def cmp_(m,c):
    """c relative to m. None: the component ends first, which the rule does not define."""
    for i,x in enumerate(m):
        if i>=len(c): return None
        if c[i]!=x: return -1 if c[i]<x else 1
    return 0
OPS={'gt':lambda r:r>0,'ge':lambda r:r>=0,'eq':lambda r:r==0,'le':lambda r:r<=0,'lt':lambda r:r<0}
ids=[()]+[(a,) for a in range(3)]+[(a,b) for a in range(3) for b in range(3)]+[(a,b,c) for a in (0,2) for b in (0,2) for c in (0,2)]
V=[(r,None,()) for r in itertools.product(range(3),repeat=3)]+[(r,s,i) for r in itertools.product(range(3),repeat=3) for s in (-3,-2,-1) for i in ids]
E={v:enc(v) for v in V}
print('versions',len(V),'distinct encodings',len({tuple(e) for e in E.values()}))
pf=sum(1 for a in E.values() for b in E.values() if a!=b and b[:len(a)]==a); print('complete encoding is a prefix of another:',pf)
bad=und=0
for a in V:
    for b in V:
        r=cmp_(E[a],E[b]); s=semver(b,a)
        if r is None: und+=1
        elif (r>0)-(r<0)!=s: bad+=1
print(f'complete manifest x complete component: pairs {len(V)**2}, ops {len(V)**2*5}, disagree with SemVer {bad*1}, undefined {und}')
sel={tuple(e[:k]) for e in E.values() for k in range(1,len(e)+1)}
print('all valid selectors (prefixes)',len(sel))
und2=[]
for s in sel:
    for b in V:
        if cmp_(list(s),E[b]) is None: und2.append((s,E[b]))
print('selector longer than component with no difference:',len(und2),und2[:3])
show=[('reported A Equal [2,0,0] rc.1 (old form as selector)',[2,0,0],enc(((2,0,0),-1,(1,)))),
('A exact Equal 2.0.0',enc(((2,0,0),None,())),enc(((2,0,0),-1,(1,)))),
('A exact Lesser 1.10.0 vs 1.10.0-rc.1',enc(((1,10,0),None,())),enc(((1,10,0),-1,(1,)))),
('B 1.2-beta = 1.2.0-beta',enc(((1,2,0),-2,())),enc(((1,2,0),-2,()))),
('C rc vs rc.1',enc(((2,0,0),-1,())),enc(((2,0,0),-1,(1,)))),
('C beta vs beta.0',enc(((1,2,0),-2,())),enc(((1,2,0),-2,(0,)))),
('D old 1.2.3 vs 1.2',enc(((1,2,3),None,())),enc(((1,2,0),None,()))),
('selector ge [1,2,3] alpha',[1,2,3],enc(((1,2,3),-3,(4,)))),
('selector ge [1,0] 1.0.0-alpha',[1,0],enc(((1,0,0),-3,()))),
('selector lt [1,10] 1.10.0-rc',[1,10],enc(((1,10,0),-1,()))),
('selector lt [1,10] 1.9.9',[1,10],enc(((1,9,9),None,()))),
('selector eq [1,2,0,-2] 1.2.0-beta.3',[1,2,0,-2],enc(((1,2,0),-2,(3,)))),
('generic scheme: manifest [2025,12,6] component [2025,12]',[2025,12,6],[2025,12]),
('old-form component [1,2,3] exact manifest',enc(((1,2,3),None,())),[1,2,3]),]
for n,m,c in show: print(f'  {n:58s} m={m} c={c} -> {cmp_(m,c)}')
print('CBOR one-byte negatives are -1..-24:', -24>=-24)
