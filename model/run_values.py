"""Same size as the default run, different integer values (release 0,1,7; identifiers 0,3)."""
import collections, time
from suitver import *
t0 = time.time()
V = versions(rel_vals=(0, 1, 7), id_vals=(0, 3), max_ids=2)
cnt = collections.Counter(); fixed_bad = 0
for m in V:
    for c in V:
        fr = fixed_cmp(m, c); d = draft_cmp(m, c)
        for op in OPS:
            t = truth(op, m, c); dd = apply(op, d)
            k = 'undefined' if dd is None else ('agree' if dd == t else ('false_positive' if dd else 'false_negative'))
            cnt[k] += 1
            if apply(op, fr) != t: fixed_bad += 1
print('arrays', len(V), 'pairs x ops', sum(cnt.values()))
for k in ('agree', 'false_positive', 'false_negative', 'undefined'): print(' ', k, cnt[k])
print('fixed rule disagreements:', fixed_bad, ' seconds:', round(time.time() - t0))
