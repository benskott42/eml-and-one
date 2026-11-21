"""union_bound.py N conv -- join of two sound partitions: raw emlcore classes and the reciprocal-R4 prototype's classes.
Nodes = shortest words of both DPs (every reachable finite value has one in the raw DP); edges = same raw form, or same
prototype form (each edge is a proven equality given the rules' soundness). Components at <= K = 2N-1 are a sound upper bound."""
import sys
sys.argv, N, conv = ['x', '1'], int(sys.argv[1]), sys.argv[2]
exec(open('recip_rule.py').read().split("N = int(sys.argv[1])")[0])
EC.Ctx = RCtx
C, V, best, _, unres = enumerate_values(N, conv, False)
EC.Ctx = _Base
C0, V0, best0, _, unres0 = enumerate_values(N, conv, False)
words = sorted({best0[k] for n in V0 for k in V0[n] if k[0] == 'F'} | {best[k] for n in V for k in V[n] if k[0] == 'F'}, key=lambda w: (len(w), w))
par = {w: w for w in words}
def find(w):
    while par[w] != w: par[w] = par[par[w]]; w = par[w]
    return w
def union(a, b):
    a, b = find(a), find(b)
    if a != b: par[b] = a
unresolved = 0
for CC in (C0, C):
    seen = {}
    for w in words:
        try: v = EC.eval_tree(CC, EC.parse_rpn(w))
        except EC.Unresolved: unresolved += 1; continue
        if EC.is_special(v): continue
        if v in seen: union(seen[v], w)
        else: seen[v] = w
comps = {find(w) for w in words}
print(f"[{conv}] K<={2*N-1}: raw classes {sum(1 for n in V0 for k in V0[n] if k[0]=='F')}, prototype classes {sum(1 for n in V for k in V[n] if k[0]=='F')}, "
      f"join components {len(comps)} (word evaluations unresolved: {unresolved}; DP unresolved raw {len(unres0)}, prototype {len(unres)})")
