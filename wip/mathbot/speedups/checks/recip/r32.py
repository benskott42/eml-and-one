"""r32.py -- compscibot's R3.2 eight pairs (notes.md:142-) and buggybot's seventh identity under the final key, both cuts."""
import sys; sys.path.insert(0, '.')
from emlcore_recip import *
P = [('11111EEE1E11EEE', '1111111EEE1E11EEEE1EE1E'), ('11111E1E1EEE1EE', '1111E1EE111E1E1EEE11EEE'),
     ('1111E11E1E1E1EEE1EE', '11E111E11E1E1E1EEE11EEE'), ('111E11111EEE1E1EE1EEE', '11111EEE1EE1111EEE11EEE'),
     ('1111E11E1E1E1EEE11EEE', '111E11E11E1E1E1EEE1EE'), ('111E1EE1111E1E1EEE1EE', '11111E1E1EEE111EE1E1EEE'),
     ('111E11E1EE1EE11E1E1EE', '1111E11E1E1E1EEE11EEE1E'), ('11111E11E1E1E1EEE11EEEE', '1111E11E11E1E1E1EEE1EEE'),
     ('11111E11EEE11EEE1EE', '11111E1EEEE11E11EEE')]
for conv in ('lower', 'principal'):
    X = Ext(conv); Cr = EC.Ctx(conv, 'allowed')
    out = []
    for i, (a, b) in enumerate(P):
        k = lambda w: X.key(EC.eval_tree(X.C0, EC.parse_rpn(w)))
        r = lambda w: EC.eval_tree(Cr, EC.parse_rpn(w))
        out.append(f"{'R3.2 #' + str(i) if i < 8 else 'buggybot #7'}: emlcore {'=' if r(a) == r(b) else '!='}, key {'=' if k(a) == k(b) else '!='}")
    print(conv, '; '.join(out))
