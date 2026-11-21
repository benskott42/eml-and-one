import sys
sys.path.insert(0, '.')
from emlcore_recip import *
CanonCtx.size_block = False; CanonCtx.r5_mode = sys.argv[1]
pairs = [p.split(',') for p in sys.argv[2:]]
for p in pairs:
    for w in p:
        for C in (EC.Ctx('lower', 'allowed'), CanonCtx('lower', 'allowed')):
            v = EC.eval_tree(C, EC.parse_rpn(w)); print(type(C).__name__[:5], w, '  ', C.show(v))
    print()
