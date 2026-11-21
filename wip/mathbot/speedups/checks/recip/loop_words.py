"""loop_words.py: evaluate the two K25 words on which unmodified emlcore looped (random1 order) in fresh contexts,
in several sub-term evaluation orders, with unmodified emlcore and with the canonical variants."""
import sys, random
sys.path.insert(0, '.')
from emlcore_recip import *
WORDS = ['1111111EEEE11E1EEE11E1EEE', '11111111EEEE11E1EEE1E1EEE']
def subwords(w):
    # all subtrees (as RPN strings) of w, children before parents
    st = []; out = []
    for ch in w:
        if ch == '1': st.append('1')
        else:
            b = st.pop(); a = st.pop(); st.append(a + b + 'E')
        out.append(st[-1])
    return out
for conv in ('lower', 'principal'):
    for w in WORDS:
        subs = list(dict.fromkeys(subwords(w)))
        for name, mk in (('emlcore', lambda: EC.Ctx(conv, 'allowed')), ('canon-akey', None), ('canon-dominant', None)):
            res = []
            for seed in range(12):
                if name == 'emlcore': C = EC.Ctx(conv, 'allowed')
                else:
                    CanonCtx.size_block = False; CanonCtx.r5_mode = name.split('-')[1]; C = CanonCtx(conv, 'allowed')
                order = subs[:-1]
                rng = random.Random(seed)
                if seed: rng.shuffle(order)       # pre-evaluate subterms in a shuffled order (children memoised first)
                try:
                    for s in order:
                        try: EC.eval_tree(C, EC.parse_rpn(s))
                        except EC.Unresolved: pass
                    v = EC.eval_tree(C, EC.parse_rpn(w)); res.append('ok' if not EC.is_special(v) else v)
                except RecursionError:
                    res.append('LOOP')
                except EC.Unresolved:
                    res.append('U')
            print(conv, w, name, ' '.join(res))
