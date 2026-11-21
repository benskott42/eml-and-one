"""show_pairs.py -- emlcore canonical forms of the six K19 field-identity pairs (collide2_12.json) and the
8 K<=23 pairs of compscibot notes.md R3.2, on both cuts, with 2048-bit ball agreement."""
import sys, json
sys.path.insert(0, '/workspace/eml-proofs'); sys.setrecursionlimit(100000)
import emlcore as EC
d = json.load(open('/workspace/eml-hub/compscibot/integers/collide2_12.json'))
six = [tuple(p) for r in d if r['K'] == 19 for p in r['over_examples']]
r32 = [("11111EEE1E11EEE", "1111111EEE1E11EEEE1EE1E"), ("11111E1E1EEE1EE", "1111E1EE111E1E1EEE11EEE"),
       ("1111E11E1E1E1EEE1EE", "11E111E11E1E1E1EEE11EEE"), ("111E11111EEE1E1EE1EEE", "11111EEE1EE1111EEE11EEE"),
       ("1111E11E1E1E1EEE11EEE", "111E11E11E1E1E1EEE1EE"), ("111E1EE1111E1E1EEE1EE", "11111E1E1EEE111EE1E1EEE"),
       ("111E11E1EE1EE11E1E1EE", "1111E11E1E1E1EEE11EEE1E"), ("11111E11E1E1E1EEE11EEEE", "1111E11E11E1E1E1EEE1EEE")]
for conv in ('lower', 'principal'):
    C = EC.Ctx(conv, 'allowed')
    for name, L in (('K19 six', six), ('R3.2 eight', r32)):
        print(f"== {conv}: {name}")
        for i, (w1, w2) in enumerate(L):
            v1 = EC.eval_tree(C, EC.parse_rpn(w1)); v2 = EC.eval_tree(C, EC.parse_rpn(w2))
            if EC.is_special(v1) or EC.is_special(v2):
                print(i, w1, w2, 'special', v1, v2); continue
            b1, b2 = C.ball(v1, 2048), C.ball(v2, 2048)
            agree = b1.overlaps(b2); rad = max(float(b1.rad()), float(b2.rad()))
            print(f"{i}: K{len(w1)}/K{len(w2)} same-form={v1 == v2} balls-overlap(2048b)={agree} |diff mid|={float(abs((b1-b2).mid())):.1e} value~{complex(b1.mid().real, b1.mid().imag) if hasattr(b1.mid(),'real') else b1}")
            if conv == 'lower' and name == 'K19 six':
                print('   A:', C.show(v1)); print('   B:', C.show(v2))
