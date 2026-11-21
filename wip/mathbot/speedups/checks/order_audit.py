"""order_audit.py N -- is emlcore's class partition independent of enumeration (interning) order?
Runs the class DP twice per cut: reference order (common.enumerate_values) and a reversed order
(i descending, V iterated in reverse insertion order). Compares per-level finite class counts, and maps classes
across the two runs by shortest-word re-evaluation."""
import sys, time
sys.path.insert(0, '/workspace/eml-hub/mathbot/schanuel/hunt')
from common import *
def enum_rev(NMAX, conv):
    C = EC.Ctx(conv, 'allowed')
    V = {1: {('F', C.ONE): C.ONE}}; best = {('F', C.ONE): '1'}; seen = {('F', C.ONE)}; unres = 0
    for n in range(2, NMAX + 1):
        V[n] = {}
        for i in range(n - 1, 0, -1):
            for ka, a in reversed(list(V[i].items())):
                for kb, b in reversed(list(V[n - i].items())):
                    try: v = EC.eml_val(C, a, b)
                    except EC.Unresolved: unres += 1; continue
                    if v in ('NAN', 'INVALID'): continue
                    k = skey(v)
                    if k in seen: continue
                    seen.add(k); V[n][k] = v; best[k] = best[ka] + best[kb] + 'E'
    return C, V, best, unres
N = int(sys.argv[1])
for conv in ('principal', 'lower'):
    C1, V1, b1, _, u1 = enumerate_values(N, conv, False)
    C2, V2, b2, u2 = enum_rev(N, conv)
    for n in range(1, N + 1):
        f1 = sum(1 for k in V1[n] if k[0] == 'F'); f2 = sum(1 for k in V2[n] if k[0] == 'F')
        print(f"[{conv}] n={n}: finite new ref {f1} rev {f2} {'OK' if f1 == f2 else 'DIFF'}")
    # cross-map: every ref class's word evaluated in C2 must hit a class of run 2 of the same level-or-lower
    fin2 = {v for n in V2 for k, v in V2[n].items() if k[0] == 'F'}
    hits = set(); bad = 0
    for n in V1:
        for k, v in V1[n].items():
            if k[0] != 'F': continue
            w = EC.eval_tree(C2, EC.parse_rpn(b1[k]))
            if w not in fin2: bad += 1
            hits.add(w)
    print(f"[{conv}] ref classes {sum(1 for n in V1 for k in V1[n] if k[0]=='F')} -> distinct run-2 forms {len(hits)}, not-in-run-2 {bad}, unresolved {len(u1)}/{u2}, atoms {len(C1.akind)}/{len(C2.akind)}")
