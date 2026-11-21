"""emlcore_recip.py -- 'emlcore R3-R5 plus reciprocal rule' (mathbot, local, NOT reviewed).
Final design (2026-11-21); see speedups/r5-field-normalisation.md section 9.

  Layer 0  C0 = CanonCtx: emlcore (imported, never edited) with every id-dependent choice made structural:
           * R5 and, for all-exp forms, R3 are replaced by R6 "factor the certified dominant term":
               v = c + sum_j k_j E(f_j) > 0 real, all f_j real, E(f_D) certified strictly dominant
               (Re(f_D - f_j) > 0 and f_D > ln|c|, by balls or emlcore's certified sign()):
               Log v = f_D + Log(u),  u = v e^{-f_D}.  No choice: the strict dominant is unique.
           * R3 on forms with non-exp terms: emlcore's rule, ties broken by structural key, not atom id.
  Layer 1  C1 = RecipCtx: the same plus the reciprocal rule (*) in exp_f:
               w = c + k exp(f) (one E term, k = +-1), L(w) with coefficient -1 in g = R - L(w):
               exp(S + f - Log w) = (exp(S) - c exp(S - Log w)) / k     (needs only w != 0).
           Canonical coset representative: R - m f minimising (L1 norm, structural key); m < 0 only if |c| = 1.
           Among several qualifying L atoms: smallest structural key.
  Key      N : C0 form -> C1 form by structural recursion (N(E g) = C1.exp_f(N g), N(L w) = C1.log_f(N w),
           sums exact).  N preserves value and is a function of the C0 form.
  Superseded switches kept for the record: size_block=True (structural size measure on R3/R5; terminates
  provably but loses emlcore merges), r5_mode='akey'/'dominant'/'domfirst'.  Ext(canon=False) puts unmodified
  emlcore in layer 0 (order dependent: emlcore itself loops on two K25 words in one random order).
"""
import sys, math
sys.path.insert(0, '/workspace/eml-proofs'); sys.setrecursionlimit(20000)
import emlcore as EC
from flint import arb

class RecipCtx(EC.Ctx):
    recip = True          # CanonCtx below = same class with the reciprocal rule switched off
    size_block = False    # (True = structural size measure, superseded variant) on R3/R5 recursive Log arguments
    r5_mode = 'R6'        # final. Others: 'akey': first success in structural-key order; 'dominant': only the certified dominant atom
    # ---- structural keys / sizes (id-independent) ----
    def skey(self, fid):
        m = self.__dict__.setdefault('_skey', {})
        r = m.get(fid)
        if r is None:
            cre, cim, terms = self.fkey[fid]
            r = (cre, cim, tuple(sorted((self.akey(a), k) for a, k in terms)))
            m[fid] = r
        return r
    def skey_of(self, key):
        cre, cim, terms = key
        return (cre, cim, tuple(sorted((self.akey(a), k) for a, k in terms)))
    def akey(self, a):
        m = self.__dict__.setdefault('_akey', {})
        r = m.get(a)
        if r is None:
            r = (self.akind[a], self.skey(self.aarg[a]))
            m[a] = r
        return r
    def size(self, fid):
        m = self.__dict__.setdefault('_size', {})
        r = m.get(fid)
        if r is None:
            cre, cim, terms = self.fkey[fid]
            r = (1 if cre else 0) + (1 if cim else 0) + sum(abs(k) * (1 + self.size(self.aarg[a])) for a, k in terms)
            m[fid] = r
        return r
    def _norm(self, key):
        return abs(key[0]) + abs(key[1]) + sum(abs(k) for _, k in key[2])

    # ---- exp with the reciprocal rule ----
    def exp_f(self, fid):
        r = self.exp_memo.get(fid)
        if r is not None:
            return r
        cre, cim, terms = self.fkey[fid]
        plain = (cre == 0 and not terms) or (cre == 0 and len(terms) == 1 and terms[0][1] == 1 and self.akind[terms[0][0]] == 'L') \
            or self._r4_atom(terms) is not None
        if not plain and self.recip:
            cands = []
            for aL, kL in terms:
                if kL != -1 or self.akind[aL] != 'L' or aL in self.__dict__.get('aopaque', ()):
                    continue
                w = self.fkey[self.aarg[aL]]
                if w[1] != 0 or len(w[2]) != 1 or abs(w[2][0][1]) != 1 or self.akind[w[2][0][0]] != 'E':
                    continue
                c, (aj, k) = w[0], w[2][0]
                f = self.fkey[self.aarg[aj]]
                R = (cre, cim, tuple(t for t in terms if t[0] != aL))
                # canonical coset representative: minimise (L1 norm, structural key) of R - m f over m.  The L1 norm is
                # convex in m, so the minimisers form an integer interval; the search window is checked to contain it.
                allowed = range(-40, 41) if abs(c) == 1 else range(0, 41)   # moving up divides by c: only if |c| = 1
                scored = [(self._norm(self.add(R, 1, f, -mm)), self.skey_of(self.add(R, 1, f, -mm)), mm) for mm in allowed]
                best = min(scored)
                if best[2] in (allowed[0], allowed[-1]) and best[2] != 0:
                    raise AssertionError('coset minimiser at the search-window edge')
                m = best[2]
                if m == 0 or (m < 0 and abs(c) != 1):
                    continue
                cands.append((self.akey(aL), aL, c, k, f, R, m))
            if cands:
                _, aL, c, k, f, R, m = min(cands, key=lambda t: t[0])
                Lw = (0, 0, ((aL, 1),))
                if m > 0:   # g = S + f - Lw, S = R - f:  exp(g) = k (exp S - c exp(S - Lw))
                    S = self.add(R, 1, f, -1)
                    eS = self.exp_f(self.intern(S))
                    eSL = self.exp_f(self.intern(self.add(S, 1, Lw, -1)))
                    acc = self.add(self.fkey[eS], k, self.fkey[eSL], -k * c)
                else:       # exp(R - Lw) = c (exp R - k exp(R + f - Lw)),  |c| = 1
                    eR = self.exp_f(self.intern(R))
                    eRf = self.exp_f(self.intern(self.add(self.add(R, 1, f, 1), 1, Lw, -1)))
                    acc = self.add(self.fkey[eR], c, self.fkey[eRf], -c * k)
                self.stats['rule_recip'] = self.stats.get('rule_recip', 0) + 1
                r = self.intern(acc)
                self.exp_memo[fid] = r
                return r
        return EC.Ctx.exp_f(self, fid)

    # ---- R5 / R3 with canonical candidate order and a size measure ----
    def _r6_applicable(self, fid):
        cre, cim, terms = self.fkey[fid]
        return len(terms) >= 1 and (cre != 0 or len(terms) >= 2) and all(
            self.akind[a] == 'E' and self.freal[self.aarg[a]] for a, _ in terms)

    def _rule_R6(self, fid):
        """'factor the dominant term': REAL v = c + sum_j k_j E(f_j) > 0, all f_j real.  If one exp term D is certified
        strictly larger in modulus than every other term (balls: Re(f_D - f_j) > 0 and f_D > ln|c|), then
             Log v = f_D + Log(u),  u = v e^{-f_D} = k_D + c e^{-f_D} + sum_{j != D} k_j e^{f_j - f_D}   (u > 0 real).
        If the constant is dominant, or no term is certified dominant, no rewrite."""
        cre, cim, terms = self.fkey[fid]
        D = None
        for aD, kD in sorted(terms, key=lambda t: self.akey(t[0])):
            if self._dominant(aD, terms):
                D = (aD, kD); break
        if D is None:
            return None
        aD, kD = D; fD = self.aarg[aD]
        if cre != 0:
            from fractions import Fraction
            lc = (arb(abs(Fraction(cre)).numerator) / arb(abs(Fraction(cre)).denominator)).log()
            if not (any((self.ball(fD, p).real - lc) > 0 for p in EC.PRECS[1:3]) or (abs(cre) == 1 and self._pos(fD))):
                self.stats['R6_const_dominant'] = self.stats.get('R6_const_dominant', 0) + 1
                return None
        acc = (0, 0, ())
        for a, k in terms:
            d = self.intern(self.add(self.fkey[self.aarg[a]], 1, self.fkey[fD], -1))
            acc = self.add(acc, 1, self.fkey[self.exp_f(d)], k)
        if cre != 0:
            acc = self.add(acc, 1, self.fkey[self.exp_f(self.intern(self.neg_key(self.fkey[fD])))], cre)
        u = self.intern(acc)
        if u == self.ZERO or not self.freal[u]:
            return None
        lu = self.log_f(u)
        if not isinstance(lu, int):
            return None
        self.stats['rule_R6'] = self.stats.get('rule_R6', 0) + 1
        return self.intern(self.add(self.fkey[fD], 1, self.fkey[lu], 1))

    def _rule_R5(self, fid):
        if self.r5_mode == 'R6':
            return self._rule_R6(fid) if self._r6_applicable(fid) else None
        cre, cim, terms = self.fkey[fid]
        if cre != 0 or len(terms) < 2:
            return None
        if not all(self.akind[a] == 'E' and self.freal[self.aarg[a]] for a, _ in terms):
            return None
        order = sorted(terms, key=lambda t: self.akey(t[0]))
        if self.r5_mode == 'dominant':
            order = [t for t in order if self._dominant(t[0], terms)][:1]
        elif self.r5_mode == 'domfirst':     # certified dominant atom first, then the rest in structural-key order
            dom = [t for t in order if self._dominant(t[0], terms)][:1]
            order = dom + [t for t in order if t not in dom]
        for aD, _ in order:
            fD = self.aarg[aD]
            acc = (0, 0, ()); ok = True
            for a, k in terms:
                d = self.intern(self.add(self.fkey[self.aarg[a]], 1, self.fkey[fD], -1))
                db = self.ball(d, EC.PRECS[1]).real
                if not (db.is_finite() and db.upper() < 50):
                    ok = False; break
                acc = self.add(acc, 1, self.fkey[self.exp_f(d)], k)
            if not ok:
                continue
            S = self.intern(acc)
            if S == self.ZERO or not self.freal[S]:
                continue
            if self.size_block and self.size(S) >= self.size(fid):          # measure: recursive Log argument must shrink
                self.stats['R5_size_block'] = self.stats.get('R5_size_block', 0) + 1
                continue
            try:
                if self.sign(S) <= 0:
                    continue
            except EC.Unresolved:
                continue
            lS = self.log_f(S)
            if not isinstance(lS, int):
                continue
            self.stats['rule_R5'] = self.stats.get('rule_R5', 0) + 1
            return self.intern(self.add(self.fkey[fD], 1, self.fkey[lS], 1))
        return None

    def _dominant(self, aD, terms):
        """certified: Re(f_D - f_j) > 0 for every other E atom j (balls at PRECS[1], then PRECS[2])."""
        fD = self.aarg[aD]
        for a, _ in terms:
            if a == aD: continue
            d = self.intern(self.add(self.fkey[fD], 1, self.fkey[self.aarg[a]], -1))
            if not self._pos(d):
                return False
        return True

    def _pos(self, d):
        """certified Re(d) > 0: balls at PRECS[1..2]; for exactly real d also emlcore's certified sign() (level-index
        magnitudes, needed for towers whose balls overflow)."""
        if any(self.ball(d, p).real > 0 for p in EC.PRECS[1:3]):
            return True
        if self.freal[d]:
            try:
                return self.sign(d) > 0
            except EC.Unresolved:
                return False
        return False

    def _rule_R3(self, fid):
        if self.r5_mode == 'R6' and self._r6_applicable(fid):
            return None                       # all-exp forms are handled by R6 only
        cre, cim, terms = self.fkey[fid]
        cands = [(a, k) for a, k in terms if k == 1 and self.akind[a] == 'E' and self.freal[self.aarg[a]]]
        if not cands or (cre == 0 and len(terms) == 1):
            return None
        best = None
        for a, k in cands:
            g = self.aarg[a]
            li = self.LI(g)
            if li is None or li[0] <= 0:
                continue
            key = (li[1], float(li[2].upper()))
            if best is None or key > best[0] or (key == best[0] and self.akey(a) < self.akey(best[1])):
                best = (key, a, g)
        if best is None:
            return None
        _, a, g = best
        Rk = (cre, 0, tuple(t for t in terms if t[0] != a))
        R = self.intern(Rk)
        if R == self.ZERO:
            return None
        try:
            sR = self.sign(R)
        except EC.Unresolved:
            return None
        absR = R if sR > 0 else self.intern(self.neg_key(Rk))
        if self.size_block and self.size(absR) >= self.size(fid):
            self.stats['R3_size_block'] = self.stats.get('R3_size_block', 0) + 1
            return None
        lR = self.log_f(absR)
        if lR == 'LOG0' or not isinstance(lR, int):
            return None
        ex = self.exp_f(self.intern(self.add(self.fkey[lR], 1, self.fkey[g], -1)))
        arg = self.intern(self.add((1, 0, ()), 1, self.fkey[ex], sR))
        if self.size_block and self.size(arg) >= self.size(fid):
            self.stats['R3_size_block'] = self.stats.get('R3_size_block', 0) + 1
            return None
        try:
            if self.sign(arg) <= 0:
                return None
        except EC.Unresolved:
            return None
        la = self.log_f(arg)
        if la == 'LOG0':
            return None
        self.stats['rule_R3'] = self.stats.get('rule_R3', 0) + 1
        return self.intern(self.add(self.fkey[g], 1, self.fkey[la], 1))


class CanonCtx(RecipCtx):
    """emlcore with id-independent R3/R5 choices and the size measure, no reciprocal rule ('canonical emlcore')."""
    recip = False

class Ext:
    """C0 (raw layer: EC.Ctx, or CanonCtx if canon=True) + C1 (RecipCtx) + the map N."""
    def __init__(self, conv, canon=True):
        self.C0 = CanonCtx(conv, 'allowed') if canon else EC.Ctx(conv, 'allowed')
        self.C1 = RecipCtx(conv, 'allowed')
        self.nf, self.na = {}, {}
        self.n_fail = 0
    def N(self, f):
        """C1 fid for C0 fid f, or None if a C1 decision is Unresolved (caller falls back to the raw key)."""
        r = self.nf.get(f)
        if r is not None or f in self.nf:
            return r
        C0, C1 = self.C0, self.C1
        cre, cim, terms = C0.fkey[f]
        acc = (cre, cim, ())
        try:
            for a, k in terms:
                g = self.NA(a)
                if g is None:
                    raise EC.Unresolved('atom')
                acc = C1.add(acc, 1, C1.fkey[g], k)
            r = C1.intern(acc)
        except EC.Unresolved:
            r = None
        self.nf[f] = r
        return r
    def NA(self, a):
        if a in self.na:
            return self.na[a]
        C0, C1 = self.C0, self.C1
        self.na[a] = None                    # recursion guard: atom args are strictly smaller, never hit
        x = self.N(C0.aarg[a])
        r = None
        if x is not None:
            try:
                if C0.akind[a] == 'E':
                    r = C1.exp_f(x)
                else:
                    r = C1.log_f(x)
                    if not isinstance(r, int):  # 'LOG0' impossible: value(x) = w != 0
                        raise AssertionError('Log 0 inside N')
            except EC.Unresolved:
                r = None
        if r is None:
            self.n_fail += 1
        self.na[a] = r
        return r
    def key(self, v):
        """dedup key for a C0 value (fid or special)."""
        if EC.is_special(v):
            return skey_special(v)
        try:
            n = self.N(v)
        except RecursionError:
            self.n_loop = getattr(self, 'n_loop', 0) + 1
            return ('LOOP', v)
        return ('N', n) if n is not None else ('R', v)

_sc = [0]
def skey_special(v):
    if isinstance(v, str): return (v,)
    if v[0] in ('P', 'N') and v[2]: return (v[0], 'imag exactly 0')
    _sc[0] += 1
    return ('S', _sc[0])

def raw_dp(NMAX, conv, order='forward', seed=0, C=None):
    """Reference class DP (common.enumerate_values) with a chosen pair order. Returns C, V, best, unres."""
    import random
    rng = random.Random(seed)
    C = C or EC.Ctx(conv, 'allowed')
    V = {1: {('F', C.ONE): C.ONE}}; best = {('F', C.ONE): '1'}; seen = {('F', C.ONE)}; unres = []
    for n in range(2, NMAX + 1):
        V[n] = {}
        splits = list(range(1, n))
        if order == 'reverse': splits.reverse()
        elif order == 'random': rng.shuffle(splits)
        for i in splits:
            A = list(V[i].items()); B = list(V[n - i].items())
            if order == 'reverse': A.reverse(); B.reverse()
            elif order == 'random': rng.shuffle(A); rng.shuffle(B)
            pairs = [(x, y) for x in A for y in B]
            if order == 'random': rng.shuffle(pairs)
            for (ka, a), (kb, b) in pairs:
                try:
                    v = EC.eml_val(C, a, b)
                except EC.Unresolved:
                    unres.append(best[ka] + best[kb] + 'E'); continue
                except RecursionError:
                    # raw emlcore R3<->R5 non-termination (order dependent); recorded, class skipped like Unresolved
                    unres.append('LOOP:' + best[ka] + best[kb] + 'E'); continue
                if v in ('NAN', 'INVALID'): continue
                k = ('F', v) if not EC.is_special(v) else skey_special(v)
                if k in seen: continue
                seen.add(k); V[n][k] = v; best[k] = best[ka] + best[kb] + 'E'
    return C, V, best, unres
