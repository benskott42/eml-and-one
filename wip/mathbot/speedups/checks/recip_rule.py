"""recip_rule.py N [conv] -- PROTOTYPE (not part of emlcore): emlcore + one extra linear rule, 'reciprocal R4'.
Identity (exact, no branch condition, needs only w != 0, which holds for every L atom):
    w = c + k*exp(f)  (one E term, k = +-1)   =>   for every form S:
    exp(S + f - Log w) = (exp(S) - c*exp(S - Log w)) / k            [exp(Log w) = w, exp(a+b) = exp(a)exp(b)]
Orientation: along the coset S + Z f pick the representative with the smallest L1 coefficient norm
(ties: smallest |m|, then m > 0), so the rewrite terminates.  Moving 'up' (m < 0) divides by c, so it is
only done when c = +-1; otherwise the atom is left as is (sound: fewer merges, never a wrong merge).
Counts classes with the reference DP and compares with raw emlcore."""
import sys
sys.path.insert(0, '/workspace/eml-hub/mathbot/schanuel/hunt')
import common
from common import *
_Base = EC.Ctx
class RCtx(_Base):
    def _norm(self, key):
        return abs(key[0]) + abs(key[1]) + sum(abs(k) for _, k in key[2])
    def exp_f(self, fid):
        r = self.exp_memo.get(fid)
        if r is not None:
            return r
        cre, cim, terms = self.fkey[fid]
        plain = (cre == 0 and not terms) or (cre == 0 and len(terms) == 1 and terms[0][1] == 1 and self.akind[terms[0][0]] == 'L') \
            or self._r4_atom(terms) is not None
        if not plain:
            for aL, kL in terms:
                if kL != -1 or self.akind[aL] != 'L' or aL in self.__dict__.get('aopaque', ()):
                    continue
                w = self.fkey[self.aarg[aL]]
                if w[1] != 0 or len(w[2]) != 1 or abs(w[2][0][1]) != 1 or self.akind[w[2][0][0]] != 'E':
                    continue
                c, (aj, k) = w[0], w[2][0]
                f = self.fkey[self.aarg[aj]]
                R = (cre, cim, tuple(t for t in terms if t[0] != aL))       # g = R - Log w
                best = None
                for m in range(-4, 5):
                    nm = self._norm(self.add(R, 1, f, -m))
                    key = (nm, abs(m), -m)
                    if best is None or key < best[0]:
                        best = (key, m)
                m = best[1]
                if m == 0 or (m < 0 and abs(c) != 1):
                    continue
                Lw = ((aL, 1),)
                if m > 0:   # g = S + f - Lw with S = R - f:  exp(g) = k*(exp(S) - c*exp(S - Lw))
                    S = self.add(R, 1, f, -1)
                    eS = self.exp_f(self.intern(S))
                    eSL = self.exp_f(self.intern(self.add(S, 1, (0, 0, Lw), -1)))
                    acc = self.add(self.fkey[eS], k, self.fkey[eSL], -k * c)
                else:       # exp(R - Lw) = c*(exp(R) - k*exp(R + f - Lw))   (c = +-1)
                    eR = self.exp_f(self.intern(R))
                    eRf = self.exp_f(self.intern(self.add(self.add(R, 1, f, 1), 1, (0, 0, Lw), -1)))
                    acc = self.add(self.fkey[eR], c, self.fkey[eRf], -c * k)
                self.stats['rule_recip'] = self.stats.get('rule_recip', 0) + 1
                r = self.intern(acc)
                self.exp_memo[fid] = r
                return r
        return _Base.exp_f(self, fid)
    def log_f(self, fid):
        # cycle guard (needed once the rule exists: emlcore's R3 <-> R5 can ping-pong on its output).
        # A re-entered argument gets the plain atom: always sound, possibly fewer merges.
        r = self.log_memo.get(fid)
        if r is not None:
            return r
        act = self.__dict__.setdefault('_active', set())
        if fid in act:
            self.stats['log_cycle_guard'] = self.stats.get('log_cycle_guard', 0) + 1
            if self.freal[fid] and fid not in (self.ZERO, self.ONE) and self.sign(fid) > 0:
                return self.intern((0, 0, ((self.atom('L', fid, True), 1),)))
        act.add(fid)
        try:
            return _Base.log_f(self, fid)
        finally:
            act.discard(fid)
N = int(sys.argv[1]); conv = sys.argv[2] if len(sys.argv) > 2 else 'lower'
EC.Ctx_orig = EC.Ctx
EC.Ctx = RCtx
C, V, best, nofree, unres = enumerate_values(N, conv, False)
EC.Ctx = EC.Ctx_orig
C0, V0, best0, _, _ = enumerate_values(N, conv, False)
cum = cum0 = 0
for n in range(1, N + 1):
    f = sum(1 for k in V[n] if k[0] == 'F'); f0 = sum(1 for k in V0[n] if k[0] == 'F')
    cum += f; cum0 += f0
    print(f"[{conv}] n={n} K={2*n-1}: new finite recip {f} raw {f0}; cumulative recip {cum} raw {cum0} (diff {cum0-cum})")
print('rule_recip applications', C.stats.get('rule_recip', 0), 'log cycle guards', C.stats.get('log_cycle_guard', 0), 'unresolved', len(unres))
# every raw class merged by the rule: list (word pairs) where raw-distinct classes become one recip class
fin0 = [(k, v) for n in V0 for k, v in V0[n].items() if k[0] == 'F']
img = {}
for k, v in fin0:
    w = best0[k]
    try: r = EC.eval_tree(C, EC.parse_rpn(w))
    except EC.Unresolved: r = ('unresolved', w)
    img.setdefault(r, []).append(w)
merged = [ws for ws in img.values() if len(ws) > 1]
print('raw classes merged by the rule:', sum(len(ws) - 1 for ws in merged))
for ws in merged[:40]:
    print('  ', ' = '.join(ws))
# reverse direction: recip classes whose best word lands on a raw class already hit (prototype misses)
inv = {}
for n in V:
    for k, v in V[n].items():
        if k[0] != 'F': continue
        try: r0 = EC.eval_tree(C0, EC.parse_rpn(best[k]))
        except EC.Unresolved: r0 = ('u', best[k])
        inv.setdefault(r0, []).append(best[k])
split = [ws for ws in inv.values() if len(ws) > 1]
print('recip classes sharing one raw form (prototype misses vs raw):', sum(len(ws) - 1 for ws in split))
for ws in split[:10]: print('   split:', ws)
# numeric sanity of every merge: raw balls at 2048 bits must overlap
badn = 0
for ws in merged:
    bs = [C0.ball(EC.eval_tree(C0, EC.parse_rpn(w)), 2048) for w in ws]
    if not all(bs[0].overlaps(b) for b in bs[1:]): badn += 1; print('   NUMERIC MISMATCH', ws)
print('merges checked numerically (2048-bit balls overlap):', len(merged), 'mismatches', badn)
