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
from flint import arb, acb, ctx as _fctx
from fractions import Fraction

class Unverified(Exception):
    """Loud guard (breakerbot): a depth, loop, re-entry or measure guard fired.  Never caught inside the rules; the
    caller flags the word UNVERIFIED and counts it separately.  Never a silent fallback to the current form."""

class RecipCtx(EC.Ctx):
    version = 'v2'        # 'v1' = the rule set of doc section 4 (reviewed 2026-11-21); 'v2' = section 11
    multi = True          # v2: multi-term reciprocal rule (*m) for a Log argument with >= 2 E terms
    r4_max = None         # v2: R4 term limit in C1 (emlcore: 3); None = unlimited (decreases ordw, section 11)
    depth_limit = 1500    # v2: nested exp_f/log_f calls; exceeding it raises Unverified
    strict = True         # v2: every rule's recursive exp_f call must strictly decrease mu = (ordw, skey)
    log_atoms = True      # v2: R6a/R3a -- R6 and R3 fire only if every shifted exponential they build is a single
                          # +-atom (and, for R6, c = 0 or |c| >= 1); this is what the log-side termination proof needs
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

    # ================= v2 =================
    # ---- loud depth guard on exp_f / log_f ----
    def _enter(self):
        d = self.__dict__.get('_depth', 0) + 1
        self._depth = d
        if d > self.__dict__.get('_maxdepth', 0):
            self._maxdepth = d
        if d > self.depth_limit:
            self.stats['guard_depth'] = self.stats.get('guard_depth', 0) + 1
            raise Unverified(f'depth guard: {d} nested exp_f/log_f calls')
    def exp_f(self, fid):
        r = self.exp_memo.get(fid)
        if r is not None:
            return r
        if self.version == 'v1':
            return self._exp_f1(fid)
        try:
            self._enter()
            r = self._exp_f2(fid)
        finally:
            self._depth -= 1
        self.exp_memo[fid] = r
        return r
    def log_f(self, fid):
        r = self.log_memo.get(fid)
        if r is not None or self.version == 'v1':
            return r if r is not None else EC.Ctx.log_f(self, fid)
        ip = self.__dict__.setdefault('_log_ip', set())
        if fid in ip:
            self.stats['guard_log_reentry'] = self.stats.get('guard_log_reentry', 0) + 1
            raise Unverified(f'log_f re-entry on fid {fid} (exact cycle)')
        ip.add(fid)
        try:
            self._enter()
            return EC.Ctx.log_f(self, fid)
        finally:
            self._depth -= 1; ip.discard(fid)
    def sign(self, fid, depth=0):
        if self.version == 'v1':
            return EC.Ctx.sign(self, fid, depth)
        try:
            return EC.Ctx.sign(self, fid, depth)
        except EC.Unresolved as e:
            if str(e).startswith('sign recursion depth'):     # emlcore's depth-40 cap: loud in v2
                self.stats['guard_sign_depth'] = self.stats.get('guard_sign_depth', 0) + 1
                raise Unverified('sign recursion depth > 40')
            raise
    # ---- re-entry guards replacing emlcore's silent memo-None guards (emlcore.py:783, 856) ----
    def XC(self, fid):
        if self.version == 'v1':
            return EC.Ctx.XC(self, fid)
        ip = self.__dict__.setdefault('_xc_ip', set())
        if fid in ip:
            self.stats['guard_XC_reentry'] = self.stats.get('guard_XC_reentry', 0) + 1
            raise Unverified(f'XC re-entry on fid {fid}')
        ip.add(fid)
        try:
            return EC.Ctx.XC(self, fid)
        except BaseException:
            self.__dict__.get('xc_memo', {}).pop(fid, None); raise
        finally:
            ip.discard(fid)
    def XA(self, a):
        if self.version == 'v1':
            return EC.Ctx.XA(self, a)
        ip = self.__dict__.setdefault('_xa_ip', set())
        if a in ip:
            self.stats['guard_XA_reentry'] = self.stats.get('guard_XA_reentry', 0) + 1
            raise Unverified(f'XA re-entry on atom {a}')
        ip.add(a)
        try:
            return EC.Ctx.XA(self, a)
        except BaseException:
            self.__dict__.get('xa_memo', {}).pop(a, None); raise
        finally:
            ip.discard(a)
    # ---- ball sums in structural (akey) order, not atom-id order (reviewbot should-fix) ----
    def _ball_from_key(self, key, prec):
        if self.version == 'v1':
            return EC.Ctx._ball_from_key(self, key, prec)
        cre, cim, terms = key
        if len(terms) <= 1:
            return EC.Ctx._ball_from_key(self, key, prec)
        return EC.Ctx._ball_from_key(self, (cre, cim, tuple(sorted(terms, key=lambda t: self.akey(t[0])))), prec)
    # ---- heights and the measure mu = (ordw, skey) ----
    def hgt(self, fid):
        m = self.__dict__.setdefault('_hgt', {})
        r = m.get(fid)
        if r is None:
            r = max((1 + self.hgt(self.aarg[a]) for a, _ in self.fkey[fid][2]), default=0)
            m[fid] = r
        return r
    def ordw(self, key):
        """ordinal weight  sum_h omega^h * n_h  (n_h = sum |coef| of atoms of height h; n_0 = |cre| + |cim|),
        as a tuple of (h, n_h) in decreasing h: Python tuple order = ordinal order."""
        cre, cim, terms = key
        lev = {}
        for a, k in terms:
            h = 1 + self.hgt(self.aarg[a]); lev[h] = lev.get(h, 0) + abs(k)
        n0 = abs(cre) + abs(cim)
        if n0:
            lev[0] = n0
        return tuple(sorted(lev.items(), reverse=True))
    def mu(self, key):
        return (self.ordw(key), self.skey_of(key))
    def _chk(self, parent, child):
        """strict decrease of mu for every recursive exp_f call made by R4, (*) and (*m); loud otherwise."""
        if not self.strict:
            return
        if not (self.mu(child) < self.mu(parent)):
            self.stats['guard_measure'] = self.stats.get('guard_measure', 0) + 1
            raise Unverified('measure did not decrease')
    def _xexp(self, parent, key):
        self._chk(parent, key)
        return self.fkey[self.exp_f(self.intern(key))]
    # ---- R4 with a structural atom choice ----
    def _r4_atom(self, terms):
        if self.version == 'v1':
            return EC.Ctx._r4_atom(self, terms)
        best = None
        for a, k in terms:
            if k == 1 and self.akind[a] == 'L':
                w = self.fkey[self.aarg[a]]
                if w[1] == 0 and (self.r4_max is None or len(w[2]) <= self.r4_max) and all(self.akind[aj] == 'E' for aj, _ in w[2]):
                    if best is None or self.akey(a) < self.akey(best):
                        best = a
        return best
    def _intc(self, c):
        return Fraction(c).denominator == 1
    def _exp_f2(self, fid):
        g = self.fkey[fid]
        cre, cim, terms = g
        if (cre == 0 and not terms) or (cre == 0 and len(terms) == 1 and terms[0][1] == 1 and self.akind[terms[0][0]] == 'L'):
            return EC.Ctx.exp_f(self, fid)
        a4 = self._r4_atom(terms)
        if a4 is not None:        # R4: exp(rest + Log w) = c_w exp(rest) + sum k_j exp(rest + f_j)
            w = self.fkey[self.aarg[a4]]
            rest = (cre, cim, tuple(t for t in terms if t[0] != a4))
            acc = (0, 0, ())
            if w[0]:
                acc = self.add(acc, 1, self._xexp(g, rest), w[0])
            for aj, kj in w[2]:
                acc = self.add(acc, 1, self._xexp(g, self.add(rest, 1, self.fkey[self.aarg[aj]], 1)), kj)
            self.stats['rule_R4'] = self.stats.get('rule_R4', 0) + 1
            return self.intern(acc)
        if self.recip:
            r = self._recip1(g)
            if r is None and self.multi:
                r = self._recipm(g)
            if r is not None:
                return r
        return EC.Ctx.exp_f(self, fid)     # plain atom (emlcore's R4 branch cannot fire: _r4_atom is None)
    def _recip_atoms(self, terms):
        for aL, kL in terms:
            if kL != -1 or self.akind[aL] != 'L' or aL in self.__dict__.get('aopaque', ()):
                continue
            w = self.fkey[self.aarg[aL]]
            if w[1] != 0 or not w[2] or not all(self.akind[aj] == 'E' for aj, _ in w[2]) or not self._intc(w[0]):
                continue
            yield aL, w
    def _recip1(self, g):
        """(*) v2: w = c + k e^f (k = +-1, c integer).  Jump straight to the coset representative minimising
        (ordw, skey) of the FULL exponent; m < 0 (moving up, divides by c) only if |c| = 1."""
        cre, cim, terms = g
        cands = []
        for aL, w in self._recip_atoms(terms):
            if len(w[2]) != 1 or abs(w[2][0][1]) != 1:
                continue
            c, (aj, k) = int(w[0]), w[2][0]
            f = self.fkey[self.aarg[aj]]
            R = (cre, cim, tuple(t for t in terms if t[0] != aL))
            Lw = (0, 0, ((aL, -1),))
            WIN = 40
            allowed = range(-WIN, WIN + 1) if abs(c) == 1 else range(0, WIN + 1)
            sc = {}
            for mm in allowed:
                gm = self.add(self.add(R, 1, f, -mm), 1, Lw, 1)
                sc[mm] = (self.ordw(gm), self.skey_of(gm))
            best = min(allowed, key=lambda mm: (sc[mm], mm))
            # window check (reviewbot should-fix): the ordinal weight must be strictly worse at every window end that is
            # not a genuine boundary, so no plateau of minimisers can run past the window
            ends = [allowed[-1]] + ([allowed[0]] if abs(c) == 1 else [])
            if any(not (sc[e][0] > sc[best][0]) for e in ends):
                self.stats['guard_window'] = self.stats.get('guard_window', 0) + 1
                raise Unverified('(*) coset window: minimiser plateau reaches the window edge')
            if best == 0:
                continue
            cands.append((self.akey(aL), aL, c, k, f, R, Lw, best))
        if not cands:
            return None
        _, aL, c, k, f, R, Lw, m = min(cands, key=lambda t: t[0])
        acc = (0, 0, ()); a = 1; U = R
        if m > 0:      # X(U) = k e^{U-f} - k c X(U-f)
            for _ in range(m):
                U = self.add(U, 1, f, -1)
                acc = self.add(acc, 1, self._xexp(g, U), a * k); a = a * (-k * c)
        else:          # X(U) = c e^U - c k X(U+f),  |c| = 1
            for _ in range(-m):
                acc = self.add(acc, 1, self._xexp(g, U), a * c); a = a * (-c * k)
                U = self.add(U, 1, f, 1)
        acc = self.add(acc, 1, self._xexp(g, self.add(U, 1, Lw, 1)), a)
        self.stats['rule_recip'] = self.stats.get('rule_recip', 0) + 1
        return self.intern(acc)
    def _recipm(self, g):
        """(*m) v2: w = c + sum_i k_i e^{f_i}, >= 2 E terms, c integer.  With f_0 = 0, k_0 = c, X(T) = exp(T - Log w):
             c X(T) + sum_i k_i X(T + f_i) = e^T                       (exp(Log w) = w, w != 0)
        For a pivot p with |k_p| = 1 and T = R - f_p:   X(R) = k_p (e^T - sum_{i != p} k_i X(R - f_p + f_i)).
        Fires only if every output exponent has strictly smaller mu than g (greedy descent; a deterministic strategy,
        not a claimed normal form of the quotient module).  Choice: smallest akey of the L atom, then the pivot whose
        outputs have the smallest sorted-descending mu list, then pivot skey."""
        cre, cim, terms = g
        mu0 = self.mu(g)
        cands = []
        for aL, w in self._recip_atoms(terms):
            if len(w[2]) < 2:
                continue
            c = int(w[0])
            T_terms = ([((0, 0, ()), c)] if c else []) + [(self.fkey[self.aarg[aj]], kj) for aj, kj in w[2]]
            R = (cre, cim, tuple(t for t in terms if t[0] != aL))
            Lw = (0, 0, ((aL, -1),))
            for p, (fp, kp) in enumerate(T_terms):
                if abs(kp) != 1:
                    continue
                T = self.add(R, 1, fp, -1)
                outs = [(self.add(self.add(T, 1, fi, 1), 1, Lw, 1), ki) for i, (fi, ki) in enumerate(T_terms) if i != p]
                mus = [self.mu(o) for o, _ in outs]
                if all(x < mu0 for x in mus):
                    cands.append(((self.akey(aL), sorted(mus, reverse=True), self.skey_of(fp)), kp, T, outs))
        if not cands:
            return None
        _, kp, T, outs = min(cands, key=lambda t: t[0])
        acc = self.add((0, 0, ()), 1, self._xexp(g, T), kp)
        for o, ki in outs:
            acc = self.add(acc, 1, self._xexp(g, o), -kp * ki)
        self.stats['rule_recipm'] = self.stats.get('rule_recipm', 0) + 1
        return self.intern(acc)

    # ================= v1 (doc section 4; kept for reproducibility) =================
    def _exp_f1(self, fid):
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
            def _lc(p):
                old = _fctx.prec; _fctx.prec = p
                try: return (arb(abs(Fraction(cre)).numerator) / arb(abs(Fraction(cre)).denominator)).log()
                finally: _fctx.prec = old
            lcs = {p: _lc(p) if self.version == 'v2' else _lc(_fctx.prec) for p in EC.PRECS[1:3]}
            if not (any((self.ball(fD, p).real - lcs[p]) > 0 for p in EC.PRECS[1:3]) or (abs(cre) == 1 and self._pos(fD))):
                self.stats['R6_const_dominant'] = self.stats.get('R6_const_dominant', 0) + 1
                return None
        ra = self.version == 'v2' and self.log_atoms
        if ra and cre != 0 and abs(cre) < 1:
            self.stats['R6a_block'] = self.stats.get('R6a_block', 0) + 1
            return None
        acc = (0, 0, ())
        for a, k in terms:
            if a == aD:
                acc = self.add(acc, 1, (1, 0, ()), k); continue          # e^{f_D - f_D} = 1 (exact)
            d = self.intern(self.add(self.fkey[self.aarg[a]], 1, self.fkey[fD], -1))
            ed = self.exp_f(d)
            if ra and not self._is_atom(ed):
                self.stats['R6a_block'] = self.stats.get('R6a_block', 0) + 1
                return None
            acc = self.add(acc, 1, self.fkey[ed], k)
        if cre != 0:
            ed = self.exp_f(self.intern(self.neg_key(self.fkey[fD])))
            if ra and not self._is_atom(ed):
                self.stats['R6a_block'] = self.stats.get('R6a_block', 0) + 1
                return None
            acc = self.add(acc, 1, self.fkey[ed], cre)
        u = self.intern(acc)
        if u == self.ZERO or not self.freal[u]:
            return None
        try:
            lu = self.log_f(u)
        except EC.Unresolved:
            if self.version == 'v1':
                raise
            self.stats['R6_log_u_unresolved'] = self.stats.get('R6_log_u_unresolved', 0) + 1
            return None
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

    def _is_atom(self, fid):
        cre, cim, terms = self.fkey[fid]
        return cre == 0 and cim == 0 and len(terms) == 1 and abs(terms[0][1]) == 1 and self.akind[terms[0][0]] == 'E'

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
        if self.version == 'v2':
            # certified choice (reviewbot should-fix): highest LI level; within it the candidate whose ball is certified
            # above all others; if none is certified, the smallest akey.  No radius-dependent float comparison.
            lis = []
            for a, k in cands:
                li = self.LI(self.aarg[a])
                if li is None or li[0] <= 0:
                    continue
                lis.append((a, li))
            if not lis:
                return None
            top = max(li[1] for _, li in lis)
            lis = [(a, li) for a, li in lis if li[1] == top]
            cert = [a for a, li in lis if all(a2 == a or li[2] > li2[2] for a2, li2 in lis)]
            a = cert[0] if cert else min((a for a, _ in lis), key=self.akey)
            if not cert and len(lis) > 1:
                self.stats['R3_akey_fallback'] = self.stats.get('R3_akey_fallback', 0) + 1
            g = self.aarg[a]
            best = (None, a, g)
        else:
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
        if self.version == 'v2' and self.log_atoms and not self._is_atom(ex):
            self.stats['R3a_block'] = self.stats.get('R3a_block', 0) + 1
            return None
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
    multi = False         # layer 0 = canonical emlcore: no reciprocal rules, emlcore's R4 limit
    log_atoms = False     # layer 0: unrestricted R6/R3 (R6a/R3a there lose emlcore merges: 43 at K23)
    r4_max = 3

class Ext:
    """C0 (raw layer: EC.Ctx, or CanonCtx if canon=True) + C1 (RecipCtx) + the map N."""
    def __init__(self, conv, canon=True):
        self.C0 = CanonCtx(conv, 'allowed') if canon else EC.Ctx(conv, 'allowed')
        self.C1 = RecipCtx(conv, 'allowed')
        self.nf, self.na = {}, {}
        self.n_fail = 0; self.n_unverified = 0; self.unverified = []   # loud: counted and listed, never silent
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
        if a in self.__dict__.setdefault('_na_ip', set()):
            raise Unverified(f'N re-entry on atom {a}')   # impossible (atom args are strictly smaller); loud if it happens
        self._na_ip.add(a)
        try:
            x = self.N(C0.aarg[a])
        finally:
            self._na_ip.discard(a)
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
        except (RecursionError, Unverified) as e:
            # loud: the caller must count UNVERIFIED keys separately (they are never merged with anything)
            self.n_loop = getattr(self, 'n_loop', 0) + 1
            self.n_unverified += 1; self.unverified.append((v, type(e).__name__ + ': ' + str(e)[:120]))
            for C in (self.C0, self.C1):
                C._depth = 0; C.__dict__.get('_xc_ip', set()).clear(); C.__dict__.get('_xa_ip', set()).clear()
            self.__dict__.get('_na_ip', set()).clear()
            return ('UNVERIFIED', v)
        if n is None:
            self.n_fallback = getattr(self, 'n_fallback', 0) + 1   # C1 Unresolved: sound raw-form fallback, counted
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
                except (RecursionError, Unverified) as e:
                    # raw emlcore R3<->R5 non-termination (order dependent) or a v2 guard: recorded, class skipped
                    unres.append(('LOOP:' if isinstance(e, RecursionError) else 'UNVERIFIED:') + best[ka] + best[kb] + 'E')
                    if hasattr(C, '_depth'): C._depth = 0
                    continue
                if v in ('NAN', 'INVALID'): continue
                k = ('F', v) if not EC.is_special(v) else skey_special(v)
                if k in seen: continue
                seen.add(k); V[n][k] = v; best[k] = best[ka] + best[kb] + 'E'
    return C, V, best, unres
