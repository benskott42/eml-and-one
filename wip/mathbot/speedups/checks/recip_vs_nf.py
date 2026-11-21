"""recip_vs_nf.py -- compare the reciprocal-R4 prototype's merges with compscibot's R1-R5 NF over-merges
(collide2_12.json) at K19, K21 and K23, both cuts."""
import sys, json
sys.argv = ['x', '1']
exec(open('recip_rule.py').read().split("N = int(sys.argv[1])")[0])
d = json.load(open('/workspace/eml-hub/compscibot/integers/collide2_12.json'))
for conv in ('lower', 'principal'):
    C = RCtx(conv, 'allowed'); C0 = _Base(conv, 'allowed')
    def ev(CC, w):
        try: return EC.eval_tree(CC, EC.parse_rpn(w))
        except EC.Unresolved: return ('u', w)
    for r in d:
        if r['K'] < 19: continue
        ov = r['over_examples']; mi = r['miss_examples']
        got = sum(1 for p in ov if ev(C, p[0]) == ev(C, p[1]))
        raw = sum(1 for p in ov if ev(C0, p[0]) == ev(C0, p[1]))
        mi_r = [(ev(C0, p[0]) == ev(C0, p[1]), ev(C, p[0]) == ev(C, p[1])) for p in mi]
        print(f"[{conv}] K{r['K']}: NF over-merge examples listed {len(ov)} (total {r['overmerges']}); merged by recip {got}; by raw emlcore {raw}; "
              f"NF misses listed {len(mi)} (total {r['misses']}): (raw equal, recip equal) = {mi_r}")
        if conv == 'lower':
            for p in ov:
                if ev(C, p[0]) != ev(C, p[1]): print('     NF merges, recip does not:', p)
