import sys
sys.path.insert(0, '.')
from emlcore_recip import *
CanonCtx.size_block = False; CanonCtx.r5_mode = sys.argv[1] if len(sys.argv) > 1 else 'dominant'
for w in ['111111EEE111EE1E1EE1EEE', '1111111EEE1EE111EEE1E1EEE']:
    for C in (EC.Ctx('lower', 'allowed'), CanonCtx('lower', 'allowed')):
        v = EC.eval_tree(C, EC.parse_rpn(w)); print(type(C).__name__, w, '\n   ', C.show(v), dict((k, v) for k, v in C.stats.items() if 'R5' in k or 'R3' in k))
