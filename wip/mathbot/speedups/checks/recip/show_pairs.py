"""show_pairs.py -- raw emlcore / layer-0 / key forms for the known two-term-w pairs (K23 x3, K27 x1 up to sign)."""
import sys; sys.path.insert(0, '.')
from emlcore_recip import *
P = [('11111EEE1E11EEE', '1111111EEE1E11EEEE1EE1E'), ('1111EEE11E11EEE', '111111EEE11E11EEEE1EE1E'),
     ('111E11EEE111EEE', '11111E11EEE111EEEE1EE1E')]
conv = sys.argv[1] if len(sys.argv) > 1 else 'lower'
X = Ext(conv); Cr = EC.Ctx(conv, 'allowed')
for a, b in P:
    for w in (a, b):
        v0 = EC.eval_tree(X.C0, EC.parse_rpn(w)); k = X.key(v0)
        print(w, '\n  raw:', Cr.show(EC.eval_tree(Cr, EC.parse_rpn(w)))[:300], '\n  key:', X.C1.show(k[1])[:300] if k[0]=='N' else k)
    print()
