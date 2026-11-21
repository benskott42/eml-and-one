"""run_orders2.py NMAX conv -- final variant: raw layer = CanonCtx (canonical, terminating emlcore), key = N into RecipCtx.
Reference = unmodified emlcore (EC.Ctx), forward order.  Orders: forward, reverse, random1..3.
Checks on the reference word set W (one shortest word per reference raw class):
  * criterion 1: ref-equal => canon-equal => key-equal (violations counted), and canon/key never split a ref class;
  * criterion 2: canon partition and key partition identical across all orders; DP counts identical;
  * dumps merges (key classes containing > 1 reference class) for check_merges.py."""
import sys, time, json
sys.path.insert(0, '.')
from emlcore_recip import *
NMAX = int(sys.argv[1]); conv = sys.argv[2]
import os
def _cfg(cls, spec, base):
    d = dict(base)
    for kv in filter(None, spec.split(',')):
        k, v = kv.split('='); d[k] = v
    cls.size_block = d['sb'] == '1'; cls.r5_mode = d['r5']; cls.recip = d['recip'] == '1'
_cfg(CanonCtx, os.environ.get('CANON', ''), dict(sb='0', r5='R6', recip='0'))
_cfg(RecipCtx, os.environ.get('C1', ''), dict(sb='0', r5='R6', recip='1'))
TAG = os.environ.get('TAG', 'v')
print(f"config: canon sb={CanonCtx.size_block} r5={CanonCtx.r5_mode} | C1 sb={RecipCtx.size_block} r5={RecipCtx.r5_mode} recip={RecipCtx.recip}")
t = time.time()
Cref, Vref, bref, uref = raw_dp(NMAX, conv, 'forward', 0, C=EC.Ctx(conv, 'allowed'))
W = [bref[k] for n in Vref for k in Vref[n] if k[0] == 'F']
cum_ref = []; s = 0
for n in range(1, NMAX + 1):
    s += sum(1 for k in Vref[n] if k[0] == 'F'); cum_ref.append(s)
print(f"[{conv}] reference emlcore forward: {cum_ref}  unresolved/loop pairs {uref}  {time.time()-t:.1f}s", flush=True)
ref_lab = list(range(len(W)))   # W has one word per reference class
orders = [('forward', 0), ('reverse', 0), ('random', 1), ('random', 2), ('random', 3)]
res = []
for order, seed in orders:
    t = time.time(); X = Ext(conv, canon=True)
    C, V, best, unres = raw_dp(NMAX, conv, order, seed, C=X.C0)
    cum_c, cum_q, keys, nc = [], [], set(), 0
    for n in range(1, NMAX + 1):
        for k, v in V[n].items():
            if k[0] != 'F': continue
            nc += 1; keys.add(X.key(v))
        cum_c.append(nc); cum_q.append(len(keys))
    lc, lq, dc, dq = [], [], {}, {}
    for w in W:
        try:
            v = EC.eval_tree(X.C0, EC.parse_rpn(w))
            lc.append(dc.setdefault(('F', v), len(dc))); lq.append(dq.setdefault(X.key(v), len(dq)))
        except EC.Unresolved:
            lc.append(('U', w)); lq.append(('U', w))
        except RecursionError:
            lc.append(('LOOP', w)); lq.append(('LOOP', w)); print(f"   [{order}{seed or ''}] canon layer loops on {w}")
    nm = f'{order}{seed or ""}'
    if not res: X0, best0, V0 = X, best, V
    res.append(dict(order=nm, lc=lc, lq=lq, cum_c=cum_c, cum_q=cum_q, unres=sorted(unres)))
    print(f"[{conv}] {nm}: canon raw {cum_c}\n      key       {cum_q}\n      unresolved/loop pairs {sorted(unres)}  N-fallbacks {X.n_fail} key-loops {getattr(X, 'n_loop', 0)}  "
          f"recip={X.C1.stats.get('rule_recip',0)} C1 R3blk={X.C1.stats.get('R3_size_block',0)} R5blk={X.C1.stats.get('R5_size_block',0)} "
          f"C0 R3blk={X.C0.stats.get('R3_size_block',0)} R5blk={X.C0.stats.get('R5_size_block',0)}  {time.time()-t:.1f}s", flush=True)
r0 = res[0]
print(f"[{conv}] on W ({len(W)} ref classes): canon classes {len(set(map(str, r0['lc'])))}, key classes {len(set(map(str, r0['lq'])))}")
lost_canon = len(W) - len(set(map(str, r0['lc'])))
print(f"[{conv}] canon layer vs reference: ref classes merged by canon = {lost_canon} (0 means canon == reference partition on W)")
for r in res[1:]:
    print(f"[{conv}] {r['order']}: canon partition == forward: {r['lc'] == r0['lc']}; key partition == forward: {r['lq'] == r0['lq']}; "
          f"counts == forward: {r['cum_c'] == r0['cum_c'] and r['cum_q'] == r0['cum_q']}; same unresolved: {r['unres'] == r0['unres']}")
f = {}; viol = sum(1 for a, b in zip(r0['lc'], r0['lq']) if f.setdefault(str(a), str(b)) != str(b))
print(f"[{conv}] canon-equal but key-different (refinement violations): {viol}")
# exact criterion-1 check on W u Wc (Wc = canon forward words): ref-equal => key-equal ?
Wc = [best0[k] for n in V0 for k in V0[n] if k[0] == 'F']
Wall = list(dict.fromkeys(W + Wc))
def lab(ctxeval, w):
    try: return ctxeval(w)
    except EC.Unresolved: return ('U', w)
    except RecursionError: return ('LOOP', w)
refl = [lab(lambda w: ('F', EC.eval_tree(Cref, EC.parse_rpn(w))), w) for w in Wall]
keyl = [lab(lambda w: X0.key(EC.eval_tree(X0.C0, EC.parse_rpn(w))), w) for w in Wall]
canl = [lab(lambda w: ('F', EC.eval_tree(X0.C0, EC.parse_rpn(w))), w) for w in Wall]
from collections import defaultdict
byref = defaultdict(set); byref_c = defaultdict(set)
for w, a, b, c in zip(Wall, refl, keyl, canl):
    if a[0] in ('U', 'LOOP'): continue
    byref[a].add(b); byref_c[a].add(c)
lost = [a for a, s in byref.items() if len(s) > 1]; lost_c = [a for a, s in byref_c.items() if len(s) > 1]
print(f"[{conv}] criterion 1 on W u Wc ({len(Wall)} words): ref classes split by key: {len(lost)}; split by canon layer: {len(lost_c)}")
for a in lost[:10]:
    print('    LOST ref merge:', [w for w, x in zip(Wall, refl) if x == a])
print(f"[{conv}] words unresolved/looping in ref: {[w for w, a in zip(Wall, refl) if a[0] in ('U','LOOP')]}; in canon: {[w for w, c in zip(Wall, canl) if c[0] in ('U','LOOP')]}")
groups = {}
for w, b in zip(W, r0['lq']): groups.setdefault(str(b), []).append(w)
merges = [g for g in groups.values() if len(g) > 1]
json.dump({'conv': conv, 'NMAX': NMAX, 'merges': merges, 'cum_ref': cum_ref, 'cum_canon': r0['cum_c'], 'cum_q': r0['cum_q']},
          open(f'merges2_{TAG}_{conv}_{NMAX}.json', 'w'))
print(f"[{conv}] new merge groups vs reference emlcore: {len(merges)} (classes merged away {sum(len(g)-1 for g in merges)})")
