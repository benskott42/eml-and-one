"""pair_stats.py N conv -- pair/hit statistics and time split of the reference class DP (emlcore)."""
import sys, time, cProfile, pstats, io
sys.path.insert(0, '/workspace/eml-hub/mathbot/schanuel/hunt')
from common import *
N = int(sys.argv[1]); conv = sys.argv[2] if len(sys.argv) > 2 else 'principal'
C = EC.Ctx(conv, 'allowed')
V = {1: {('F', C.ONE): C.ONE}}; seen = {('F', C.ONE)}
T = {'exp': 0.0, 'log': 0.0, 'pair': 0.0}
oexp, olog = C.exp_f, C.log_f
D = [0]
def exp_t(f):
    if D[0]: return oexp(f)
    D[0] = 1; t = time.perf_counter()
    try: return oexp(f)
    finally: T['exp'] += time.perf_counter() - t; D[0] = 0
def log_t(f):
    if D[0]: return olog(f)
    D[0] = 1; t = time.perf_counter()
    try: return olog(f)
    finally: T['log'] += time.perf_counter() - t; D[0] = 0
C.exp_f, C.log_f = exp_t, log_t
terms_len = []
for n in range(2, N + 1):
    V[n] = {}; pairs = hits = new = spec = unres = 0
    t0 = time.perf_counter(); T.update(exp=0.0, log=0.0)
    for i in range(1, n):
        for ka, a in V[i].items():
            for kb, b in V[n - i].items():
                pairs += 1
                try: v = EC.eml_val(C, a, b)
                except EC.Unresolved: unres += 1; continue
                if v in ('NAN', 'INVALID'): spec += 1; continue
                k = skey(v)
                if k in seen: hits += 1; continue
                seen.add(k); V[n][k] = v; new += 1
    dt = time.perf_counter() - t0
    fin = [v for k, v in V[n].items() if k[0] == 'F']
    avg = sum(len(C.fkey[v][2]) for v in fin) / max(1, len(fin))
    print(f"n={n} K={2*n-1}: pairs {pairs}, new {new}, dup-hits {hits}, nan/invalid {spec}, unresolved {unres}; "
          f"time {dt:.2f}s (inside exp_f {T['exp']:.2f}s, log_f {T['log']:.2f}s, rest {dt-T['exp']-T['log']:.2f}s); "
          f"avg atoms/form {avg:.2f}; total forms {len(C.fkey)} atoms {len(C.akind)}", flush=True)
