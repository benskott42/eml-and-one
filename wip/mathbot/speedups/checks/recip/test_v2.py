"""test_v2.py conv [r4max] -- v2 unit checks: K23 two-term pairs, buggybot #7, reviewbot's K33/K45 runaway words."""
import sys, time; sys.path.insert(0, '.')
from emlcore_recip import *
conv = sys.argv[1]
if len(sys.argv) > 2: RecipCtx.r4_max = None if sys.argv[2] == 'None' else int(sys.argv[2])
P = [('11111EEE1E11EEE', '1111111EEE1E11EEEE1EE1E'), ('1111EEE11E11EEE', '111111EEE11E11EEEE1EE1E'),
     ('111E11EEE111EEE', '11111E11EEE111EEEE1EE1E'), ('11111E11EEE11EEE1EE', '11111E1EEEE11E11EEE')]
X = Ext(conv)
k = lambda w: X.key(EC.eval_tree(X.C0, EC.parse_rpn(w)))
for a, b in P:
    print(conv, a, b, 'key', '=' if k(a) == k(b) else '!=', flush=True)
for w in ('11E111EE111E11E11E1EEEE1E11EEEE1E', '11E1111E1E11E1EEEE111EE11EE11EEEE11E1E1E11EEE'):
    t = time.time(); r = k(w)
    print(conv, w, r[0], X.C1.show(r[1])[:200] if r[0] == 'N' else '', f'{time.time()-t:.1f}s', flush=True)
print('stats C1', {k: v for k, v in X.C1.stats.items() if k.startswith(('rule', 'guard', 'R'))}, 'maxdepth', X.C1.__dict__.get('_maxdepth'))
print('unverified', X.unverified)
