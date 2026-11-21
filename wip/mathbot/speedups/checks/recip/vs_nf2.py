"""vs_nf2.py conv -- final variant (canon raw layer + key N) against compscibot's collide2_12.json lists (K19-K23):
which listed NF over-merges the key also merges, which it does not (and why: printed forms), and the NF misses.
Also the K21 union bound: key partition on the K<=21 reference words joined with all 24 listed NF over-merges."""
import sys, json, os
sys.path.insert(0, '.')
from emlcore_recip import *
conv = sys.argv[1]
for cls in (CanonCtx, RecipCtx): cls.size_block = False; cls.r5_mode = 'R6'
CanonCtx.recip = False; RecipCtx.recip = True
d = json.load(open('/workspace/eml-hub/compscibot/integers/collide2_12.json'))
X = Ext(conv, canon=True); Cref = EC.Ctx(conv, 'allowed')
def key(w):
    try: return X.key(EC.eval_tree(X.C0, EC.parse_rpn(w)))
    except EC.Unresolved: return ('U', w)
def ref(w):
    try: return EC.eval_tree(Cref, EC.parse_rpn(w))
    except EC.Unresolved: return ('U', w)
for r in d:
    if r['K'] < 19: continue
    ov, mi = r['over_examples'], r['miss_examples']
    nk = [p for p in ov if key(p[0]) != key(p[1])]
    print(f"[{conv}] K{r['K']}: NF over-merges listed {len(ov)}/{r['overmerges']}: also merged by key {len(ov)-len(nk)}, not merged {len(nk)}; "
          f"NF misses listed {len(mi)}/{r['misses']}: ref-equal {sum(ref(p[0]) == ref(p[1]) for p in mi)}, key-equal {sum(key(p[0]) == key(p[1]) for p in mi)}")
    for p in nk:
        print('    NF merges, key does not:', p[0], p[1])
        for w in p[:2]:
            print('        ', w, ' key form:', X.C1.show(key(w)[1])[:300] if key(w)[0] == 'N' else key(w))
# K21 union
r10 = [r for r in d if r['K'] == 21][0]
_, V, best, _ = raw_dp(11, conv, 'forward', 0, C=EC.Ctx(conv, 'allowed'))
W = [best[k] for n in V for k in V[n] if k[0] == 'F']
par = {}
def find(x):
    while par.setdefault(x, x) != x: x = par[x]
    return x
def union(a, b): par[find(a)] = find(b)
kk = {}
for w in W:
    k = key(w); union(w, ('k', str(k)))
for p in r10['over_examples']:
    union(p[0], p[1])
print(f"[{conv}] K21 classes: key {len(set(str(key(w)) for w in W))}; union of key with all {len(r10['over_examples'])} NF over-merges {len(set(find(w) for w in W))}")
