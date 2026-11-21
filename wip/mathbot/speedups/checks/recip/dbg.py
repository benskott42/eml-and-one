import sys
sys.path.insert(0, '.')
from emlcore_recip import *
for cls in (CanonCtx, RecipCtx): cls.size_block = False; cls.r5_mode = sys.argv[1]
X = Ext('lower', canon=True)
for w in sys.argv[2:]:
    v = EC.eval_tree(X.C0, EC.parse_rpn(w)); k = X.key(v)
    print(w, '\n  raw', X.C0.show(v), '\n  key', X.C1.show(k[1]) if k[0] == 'N' else k)
