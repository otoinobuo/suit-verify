"""draft-ietf-suit-update-management-16 §4.4 version comparison vs SemVer 2.0.0 §11.

Arrays: [+int]. Release part = 1..3 non-negative ints; optional pre-release = negative class
(-1 rc, -2 beta, -3 alpha) followed by zero or more non-negative ids.
"""
from itertools import product

OPS = ('gt', 'ge', 'eq', 'le', 'lt')

def parse(a):
    """Return (rel, pre) or None if not well-formed per §4.4.1."""
    if not a or a[0] < 0:
        return None
    rel = []
    i = 0
    while i < len(a) and a[i] >= 0:
        rel.append(a[i]); i += 1
    if not 1 <= len(rel) <= 3:
        return None
    if i == len(a):
        return (rel, None)
    cls = a[i]
    if cls not in (-1, -2, -3):
        return None
    ids = a[i+1:]
    if any(x < 0 for x in ids):
        return None
    return (rel, (cls, ids))

def denote(a):
    """SemVer version denoted by the array: (major, minor, patch, pre) with pre=None or (cls, ids)."""
    rel, pre = parse(a)
    rel = rel + [0] * (3 - len(rel))
    return (tuple(rel), pre)

def sgn(x):
    return (x > 0) - (x < 0)

def semver_cmp(v, w):
    """SemVer 2.0.0 §11 precedence: -1 if v<w, 0 equal, 1 if v>w. cls: alpha(-3)<beta(-2)<rc(-1)."""
    (rv, pv), (rw, pw) = v, w
    if rv != rw:
        return -1 if rv < rw else 1
    if pv is None and pw is None:
        return 0
    if pv is None:
        return 1          # normal release > pre-release
    if pw is None:
        return -1
    if pv[0] != pw[0]:
        return sgn(pv[0] - pw[0])
    a, b = pv[1], pw[1]
    for x, y in zip(a, b):
        if x != y:
            return sgn(x - y)
    return sgn(len(a) - len(b))   # larger set of fields is higher

def draft_cmp(m, c):
    """§4.4 as written: compare in sequence; stop after manifest array consumed or first inequality.
    Returns -1 (component lesser), 0 (equal), 1 (component greater), or None (component consumed first: undefined)."""
    for i, x in enumerate(m):
        if i >= len(c):
            return None
        if c[i] != x:
            return sgn(c[i] - x)
    return 0

def apply(op, r):
    if r is None:
        return None
    return {'gt': r > 0, 'ge': r >= 0, 'eq': r == 0, 'le': r <= 0, 'lt': r < 0}[op]

def truth(op, m, c):
    """Reference semantics. A manifest array denotes a set S of SemVer versions: a single version when its
    release part has three integers or a pre-release indicator follows; otherwise the family of all versions
    whose release tuple starts with the given integers (section 4.4: 'Equal [1] matches all version sequences
    starting with 1'). Operators are read against S under SemVer 2.0.0 section 11 precedence: Equal = c in S,
    Greater = c above every member of S, Lesser = c below every member, GE/LE = or-Equal.
    For a family, c is above/below/in S exactly when the prefix of c's release tuple is above/below/equal."""
    rel, pre = parse(m)
    vc = denote(c)
    if pre is not None or len(rel) == 3:
        return apply(op, semver_cmp(vc, denote(m)))
    pc = list(vc[0][:len(rel)])
    r = 0 if pc == rel else (1 if pc > rel else -1)
    return apply(op, r)

def pad_rel(a):
    rel, pre = parse(a)
    rel = rel + [0] * (3 - len(rel))
    return rel + ([] if pre is None else [pre[0]] + list(pre[1]))

def fixed_cmp(m, c):
    """Proposed fix (integer-sequence procedure, one added normalisation and two added stop rules):
    1. pad the component's release part with zeros to three integers; do the same for the manifest's
       release part when a pre-release indicator follows it.
    2. compare integers in sequence; the first inequality decides (as in the draft).
    3. if the manifest's array is consumed without inequality, the result is Equal, except: Lesser when the
       manifest has three release integers and no pre-release indicator while the component has one
       (a pre-release is lower than the release); Greater when both carry a pre-release indicator
       (the component has more pre-release identifiers).
    4. if the component's array is consumed first, the result is Greater when the manifest's next integer is
       negative (the component is the release, the manifest a pre-release of it) and Lesser otherwise
       (fewer pre-release identifiers)."""
    mrel, mpre = parse(m)
    crel, cpre = parse(c)
    c2 = pad_rel(c)
    m2 = pad_rel(m) if mpre is not None else list(mrel)
    n = min(len(m2), len(c2))
    for i in range(n):
        if c2[i] != m2[i]:
            return sgn(c2[i] - m2[i])
    if len(m2) == len(c2):
        return 0
    if len(m2) < len(c2):
        if mpre is not None:
            return 1
        if len(mrel) == 3 and cpre is not None:
            return -1
        return 0
    return 1 if m2[len(c2)] < 0 else -1

# ---------------- enumeration ----------------
def versions(rel_vals=(0, 1, 2), id_vals=(0, 1), max_ids=2):
    out = []
    for k in (1, 2, 3):
        for rel in product(rel_vals, repeat=k):
            out.append(list(rel))
            for cls in (-1, -2, -3):
                for n in range(max_ids + 1):
                    for ids in product(id_vals, repeat=n):
                        out.append(list(rel) + [cls] + list(ids))
    return out

def classify(op, m, c):
    d = apply(op, draft_cmp(m, c))
    t = truth(op, m, c)
    if d is None:
        return 'undefined'
    if d == t:
        return 'agree'
    return 'false_positive' if d and not t else 'false_negative'

if __name__ == '__main__':
    import sys, collections
    V = versions()
    print('arrays:', len(V))
    cnt = collections.Counter()
    cnt_full = collections.Counter()   # manifest denotes a single version (3 release ints or pre-release)
    fixed_bad = 0
    examples = {}
    for m in V:
        mrel, mpre = parse(m)
        full = mpre is not None or len(mrel) == 3
        for c in V:
            fr = fixed_cmp(m, c)
            for op in OPS:
                k = classify(op, m, c)
                cnt[k] += 1
                if full:
                    cnt_full[k] += 1
                if apply(op, fr) != truth(op, m, c):
                    fixed_bad += 1
                if k != 'agree':
                    key = (k, full)
                    size = (len(m) + len(c), len(m), len(c), m, c)
                    if key not in examples or size < examples[key][0]:
                        examples[key] = (size, op, m, c, apply(op, draft_cmp(m, c)), truth(op, m, c))
    tot = sum(cnt.values())
    print('pairs x ops:', tot)
    for k in ('agree', 'false_positive', 'false_negative', 'undefined'):
        print(f'  {k:15s} all: {cnt[k]:8d}   manifest=single version: {cnt_full[k]:8d}')
    print('fixed rule disagreements with truth:', fixed_bad)
    print('minimal examples (class, manifest-is-single-version): op, manifest, component, draft, truth')
    for key in sorted(examples):
        size, op, m, c, d, t = examples[key]
        print(f'  {key}: {op} {m} vs {c}: draft={d} truth={t}')
    # equality-consistency checks of the draft's own Equal relation
    print('draft Equal [1,2] vs [1,2,0]:', draft_cmp([1,2],[1,2,0]), ' Equal [1,2,-2] vs [1,2,0,-2]:', draft_cmp([1,2,-2],[1,2,0,-2]),
          ' Equal [1,2,0,-2] vs [1,2,-2]:', draft_cmp([1,2,0,-2],[1,2,-2]))
    print('GE [2,0] vs [2,0,-1,1]:', draft_cmp([2,0],[2,0,-1,1]), ' GE [2,0,0] vs [2,0,-1,1]:', draft_cmp([2,0,0],[2,0,-1,1]),
          ' Equal [2,0,0] vs [2,0,0,-1,1]:', draft_cmp([2,0,0],[2,0,0,-1,1]), ' [2,0,0,-1] vs [2,0,0,-1,1]:', draft_cmp([2,0,0,-1],[2,0,0,-1,1]))
    print('draft [1,2,3] vs [1,2]:', draft_cmp([1,2,3],[1,2]), ' [2,0,-1,1] vs [2,0,-1]:', draft_cmp([2,0,-1,1],[2,0,-1]))
