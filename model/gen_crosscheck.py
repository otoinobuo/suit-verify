"""Emit lean/CrossCheck.lean: Python results for a fixed sample, re-checked by Lean `decide`."""
import random
from suitver import *
random.seed(20261029)
V = versions()
def arr(a):
    rel, pre = parse(a)
    p = 'none' if pre is None else f'some ⟨{pre[0]},[{",".join(map(str,pre[1]))}]⟩'
    return f'⟨[{",".join(map(str,rel))}], {p}⟩'
def cmpname(r):
    return {-1: '.lt', 0: '.eq', 1: '.gt'}[r]
sample = [([2,0,0],[2,0,0,-1,1]), ([1,10,0],[1,10,0,-1,1]), ([1,2,-2],[1,2,0,-2]), ([1,2,0,-2],[1,2,-2]),
          ([2,0,0,-1],[2,0,0,-1,1]), ([2,0,0,-1,1],[2,0,0,-1]), ([1,2,3],[1,2]), ([2,0],[2,0,-1,1]), ([2,0,0],[2,0,-1,1]),
          ([1],[1,0,0,-3]), ([1,0],[1,0,0,-3]), ([1,0,0],[1,0,0,-3]), ([0],[1,-1]), ([1,2],[1,3,0,-2,5])]
while len(sample) < 80:
    sample.append((random.choice(V), random.choice(V)))
lines = ['import SuitVersion', '', '/-! Results computed by model/suitver.py (gen_crosscheck.py), re-checked by `decide`. -/', '']
for m, c in sample:
    d = draft_cmp(m, c)
    dl = 'none' if d is None else f'some {cmpname(d)}'
    lines.append(f'example : draftCmp [{",".join(map(str,m))}] [{",".join(map(str,c))}] = {dl} := by decide')
    lines.append(f'example : fixedCmp {arr(m)} {arr(c)} = {cmpname(fixed_cmp(m, c))} := by decide')
    # reference semantics: encode the per-operator truth as a Cmp
    r = {('eq',): None}
    t = [truth(op, m, c) for op in OPS]   # gt ge eq le lt
    ref = 1 if t[0] else (0 if t[2] else -1)
    lines.append(f'example : refCmp {arr(m)} {arr(c)} = {cmpname(ref)} := by decide')
open('../lean/CrossCheck.lean', 'w').write('\n'.join(lines) + '\n')
print(len(sample), 'pairs,', 3 * len(sample), 'examples')
