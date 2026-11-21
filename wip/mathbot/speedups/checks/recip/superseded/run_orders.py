"""run_orders.py NMAX conv -- quotient counts and order-independence of 'emlcore + reciprocal rule'.
Runs forward, reverse, random(1), random(2) orders.  For each run: raw DP (unmodified emlcore), then the dedup key N
on every raw class.  Cross-run: the forward run's shortest words (one per raw class) are classified in every run;
raw partitions and N partitions on that word set must be identical."""
import sys, time, json
sys.path.insert(0, '.')
from emlcore_recip import *
NMAX = int(sys.argv[1]); conv = sys.argv[2]
orders = [('forward', 0), ('reverse', 0), ('random', 1), ('random', 2)]
runs = []
for order, seed in orders:
    t = time.time()
    X = Ext(conv)
    C, V, best, unres = raw_dp(NMAX, conv, order, seed, C=X.C0)
    cum_raw = []; cum_q = []; keys = set(); nraw = 0
    for n in range(1, NMAX + 1):
        for k, v in V[n].items():
            if k[0] != 'F': continue
            nraw += 1; keys.add(X.key(v))
        cum_raw.append(nraw); cum_q.append(len(keys))
    runs.append(dict(order=f'{order}{seed or ""}', X=X, V=V, best=best, unres=sorted(unres), cum_raw=cum_raw, cum_q=cum_q, t=time.time() - t))
    print(f"[{conv}] {order}{seed or ''}: raw {cum_raw[-1]}  quotient {cum_q[-1]}  unresolved raw pairs {len([u for u in unres if not u.startswith('LOOP')])}  raw-emlcore LOOPS {[u for u in unres if u.startswith('LOOP')]}  N-fallbacks {X.n_fail}  "
          f"C1 stats recip={X.C1.stats.get('rule_recip',0)} R3blk={X.C1.stats.get('R3_size_block',0)} R5blk={X.C1.stats.get('R5_size_block',0)}  {time.time()-t:.1f}s", flush=True)
    print(f"      cumulative raw   {cum_raw}\n      cumulative quot. {cum_q}", flush=True)
# cross-run classification of the forward run's words
W = [runs[0]['best'][k] for n in runs[0]['V'] for k in runs[0]['V'][n] if k[0] == 'F']
def labels(run, kind):
    X = run['X']; lab = {}; out = []
    for w in W:
        try:
            v = EC.eval_tree(X.C0, EC.parse_rpn(w))
        except EC.Unresolved:
            out.append(('U', w)); continue
        except RecursionError:
            out.append(('LOOP', w)); print(f"   [{run['order']}] raw emlcore loops on forward word {w}"); continue
        k = ('raw', v) if kind == 'raw' else X.key(v)
        out.append(lab.setdefault(k, len(lab)))
    return out
ref_raw, ref_q = labels(runs[0], 'raw'), labels(runs[0], 'q')
print(f"[{conv}] forward word set: {len(W)} words; raw classes on it {len(set(ref_raw))}; quotient classes on it {len(set(ref_q))}")
for r in runs[1:]:
    lr, lq = labels(r, 'raw'), labels(r, 'q')
    print(f"[{conv}] {r['order']}: raw partition identical to forward: {lr == ref_raw};  quotient partition identical: {lq == ref_q};  "
          f"same unresolved raw words: {r['unres'] == runs[0]['unres']}; same counts: {r['cum_q'] == runs[0]['cum_q']}", flush=True)
# criterion 1 (refinement) on the forward run, explicitly: raw label -> quotient label must be a function
f = {}
viol = sum(1 for a, b in zip(ref_raw, ref_q) if f.setdefault(a, b) != b)
print(f"[{conv}] refinement violations (raw-equal words with different quotient class): {viol}")
# dump the new merges (forward run) for the identity checks
groups = {}
for w, a, b in zip(W, ref_raw, ref_q):
    groups.setdefault(b, []).append(w)
merges = [g for g in groups.values() if len(g) > 1]
json.dump({'conv': conv, 'NMAX': NMAX, 'merges': merges, 'cum_raw': runs[0]['cum_raw'], 'cum_q': runs[0]['cum_q']},
          open(f'merges_{conv}_{NMAX}.json', 'w'))
print(f"[{conv}] new merge groups: {len(merges)} (raw classes merged away: {sum(len(g) - 1 for g in merges)})")
