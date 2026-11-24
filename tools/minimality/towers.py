"""Second decider for the programs decide.py leaves undecided: towers with phases.

decide.py follows towers only in a few fixed shapes. The programs it leaves open
nest towers inside sums, logs of towers with a phase, and differences of two
towers. This module evaluates a program in two layers, both exact or rigorous:

1. An exact symbolic layer. A finite value is an integer combination of atoms:
   1, i*pi, exp(w), ln(z), and ln1p atoms (below). Equal atoms cancel exactly.
   Sound rewrites only: ln 1 = 0, exp(0) = 1, exp(w + k*pi*i) = (-1)^k exp(w),
   exp(ln z) = z, and ln(c*exp(w)) = w + ln c with the branch fixed by the lower
   cut (Arg in [-pi, pi)). When one term t of a sum v dominates the rest r
   (|r/t| < e^-50, certified), ln v is split as ln t + ln(1 + r/t), with the
   ln(1 + r/t) part a new atom and the 2*pi*i correction decided from the sign
   of Im(r/t). That is how ln(exp(x) - c) - x leaves a tiny atom of known sign
   instead of an interval around 0.

2. A rigorous numerical layer. Each atom and sum carries an enclosure that is
   either a complex rectangle (mpmath.iv) or s*exp(W), with s = +-1 and W itself
   an enclosure: a tower, huge or tiny, with its phase. exp(W) is never 0, so an
   enclosure of that form is certified nonzero. Sums use dominance (a term
   e^50 larger absorbs the other into W with a rigorous bound) or, for two
   comparable exponentials, exp(W1)(1 + exp(W2 - W1)), where W2 - W1 is computed
   from the exact layer when both are exp atoms, so a shared tower cancels.

A tower keeps its phase apart from W when W's own enclosure is too wide for it:
Im w summed atom by atom in the exact layer (T6 - ln z is a tower with imaginary
part -Arg z), or, when PHASE is set (deep.py), Im w mod 2*pi computed at millions of
bits from the subword whose value is w. A branch that depends on a phase nothing
reduces, ln(exp w) with Im w a tower, keeps its exact real part Re w and an unknown
-2*pi*i*n as an atom that is purely imaginary and has no enclosure.

A program is excluded when value - target is a nonempty combination whose
enclosure is a tower (nonzero) or a rectangle that misses 0, or whose real part,
without the purely imaginary atoms, is a tower or a rectangle that misses 0. An empty
combination means the value IS the target, and is reported as such. Anything
else raises Undecided. ln 0 = -inf and infinities follow decide.py.
"""
from mpmath import iv, mpf

THRESH = mpf(10) ** 15  # |Re W| past this: keep exp(W) as a tower
GAP = 50               # dominance margin, in ln
CAP = mpf(10) ** 16    # e^-gap is bounded by e^-CAP for any gap past CAP


class Undecided(Exception):
    pass


# ---------------------------------------------------------------- enclosures

class Ball:
    """re + i*im, both mpmath intervals. im == [0, 0] means exactly real."""
    __slots__ = ("re", "im")

    def __init__(self, re, im=None):
        self.re = re
        self.im = iv.mpf(0) if im is None else im


class Tow:
    """s*exp(W), s = +-1, W an enclosure. Never 0. ph, when set, is a real interval
    with Im W in ph + 2*pi*Z: the phase of the tower, known more tightly than W's
    own imaginary part (from the exact layer, or from deep.py at millions of bits).
    im, when set, is a real interval containing the imaginary part of the value itself,
    summed atom by atom in the exact layer (T6 - ln z is a tower whose imaginary part
    -Arg z no enclosure of the tower alone keeps)."""
    __slots__ = ("W", "s", "ph", "im")

    def __init__(self, W, s, ph=None, im=None):
        self.W, self.s, self.ph, self.im = W, s, ph, im


def zint(x):
    return x.a == 0 and x.b == 0


def isreal(A):
    return zint(A.im) if isinstance(A, Ball) else isreal(A.W)


def is_zero(A):
    return isinstance(A, Ball) and zint(A.re) and zint(A.im)


def pm(r):
    return iv.mpf([-r, r])


def a_neg(A):
    if isinstance(A, Ball):
        return Ball(-A.re, -A.im)
    return Tow(A.W, -A.s, A.ph, None if A.im is None else -A.im)


def sign_iv(x):
    if x.a > 0:
        return 1
    if x.b < 0:
        return -1
    if zint(x):
        return 0
    return None


def phase(A):
    """A real interval congruent to Im W mod 2*pi for a tower A = s*exp(W), or None."""
    if A.ph is not None:
        return A.ph
    imW = a_im(A.W)
    return imW.re if isinstance(imW, Ball) else None


def a_re(A):
    """Real part, as a real enclosure."""
    if isinstance(A, Ball):
        return Ball(A.re)
    if isreal(A.W):
        return A
    ph = phase(A)
    if ph is None:
        return symmetric(A, "tower with a tower phase")
    c = iv.cos(ph)
    sc = sign_iv(c)
    if sc in (None, 0):
        return symmetric(A, "phase of a tower near +-pi/2")
    return mkexp(a_add(a_re(A.W), Ball(iv.log(abs(c)))), A.s * sc)


def a_im(A):
    """Imaginary part, as a real enclosure."""
    if isinstance(A, Ball):
        return Ball(A.im)
    if isreal(A.W):
        return Ball(iv.mpf(0))
    if A.im is not None:
        return Ball(A.im)
    ph = phase(A)
    if ph is None:
        return symmetric(A, "tower with a tower phase")
    sn = iv.sin(ph)
    ss = sign_iv(sn)
    if ss is None:
        return symmetric(A, "phase of a tower near 0 or pi")
    if ss == 0:
        return Ball(iv.mpf(0))
    return mkexp(a_add(a_re(A.W), Ball(iv.log(abs(sn)))), A.s * ss)


def symmetric(A, why):
    """[-|A|, |A|], for a real or imaginary part whose sign the phase does not give."""
    try:
        return Ball(pm(mag_up(A)))
    except Undecided:
        raise Undecided(why)


def real_sign(A):
    """Sign of a real enclosure: 1, -1, 0 or None."""
    if isinstance(A, Ball):
        return sign_iv(A.re)
    return A.s


def is_tiny(A):
    """A tower below e^-5 in modulus."""
    if not isinstance(A, Tow):
        return False
    lA = a_re(A.W)
    return lA.re.b < -5 if isinstance(lA, Ball) else lA.s < 0


def mkexp(W, s=1, ph=None):
    """s*exp(W) as a rectangle when it is in range, else as a tower. ph: see Tow."""
    if isinstance(W, Ball):
        if W.re.a >= -THRESH and W.re.b <= THRESH:
            m = iv.exp(W.re) * s
            if zint(W.im):
                return Ball(m)
            return Ball(m * iv.cos(W.im), m * iv.sin(W.im))
        return Tow(W, s, ph)
    # W is a tower: exp of a tiny W is 1 + O(|W|)
    lW = a_re(W.W)  # ln|W|
    tiny = lW.re.b < -5 if isinstance(lW, Ball) else lW.s < 0
    if tiny:
        m = mag_up(W)
        return Ball(s * (1 + pm(2 * m)), iv.mpf(0) if isreal(W) else pm(2 * m))
    return Tow(W, s, ph)


def mag_up(A):
    """An upper bound (mpf) on |A|."""
    if isinstance(A, Ball):
        return max(abs(A.re.a), abs(A.re.b)) + max(abs(A.im.a), abs(A.im.b))
    L = a_re(A.W)
    if isinstance(L, Ball):
        if L.re.b > THRESH:
            raise Undecided("bounding a huge value")
        if L.re.b < -CAP:
            return iv.exp(-iv.mpf(CAP)).b
        return iv.exp(iv.mpf(L.re.b)).b
    if L.s < 0:
        return iv.exp(-iv.mpf(CAP)).b
    raise Undecided("bounding a huge value")


def lm(A):
    """ln|A| as a real enclosure, or None when A may be 0."""
    if isinstance(A, Ball):
        if isreal(A):
            if sign_iv(A.re) in (None, 0):
                return None
            return Ball(iv.log(abs(A.re)))
        m2 = A.re * A.re + A.im * A.im
        if m2.a <= 0:
            return None
        return Ball(iv.log(m2) / 2)
    return a_re(A.W)


def lm_up(A):
    """A real enclosure containing an upper bound on ln|A|, or None if A == 0."""
    if isinstance(A, Ball):
        m = mag_up(A)
        if m == 0:
            return None
        return Ball(iv.log(iv.mpf(m)).b + iv.mpf(0))
    return a_re(A.W)


def dom_gap(A, B, need=GAP):
    """A lower bound >= need on ln|A| - ln|B|, or None."""
    la = lm(A)
    if la is None:
        return None
    ub = lm_up(B)
    if ub is None:
        return CAP
    try:
        G = a_add(la, a_neg(ub))
    except Undecided:
        return None
    if isinstance(G, Ball):
        return min(G.re.a, CAP) if G.re.a >= need else None
    if G.s < 0:
        return None
    lG = a_re(G.W)  # ln G: a tower G may be huge or tiny
    if isinstance(lG, Ball):
        return CAP if lG.re.a > 40 else None  # G > e^40 > CAP
    return CAP if lG.s > 0 else None


def absorb(A, B, g):
    real = isreal(A) and isreal(B)
    if isinstance(A, Ball):
        r = mag_up(B)
        return Ball(A.re + pm(r), A.im + (iv.mpf(0) if real else pm(r)))
    # s*exp(W) + B = s*exp(W + ln(1 + x)), x = B/A, |x| <= e^-g
    try:
        x = a_mul(B, a_inv(A))
        P = ln1p_enc(x, g)
    except Undecided:
        r = 2 * iv.exp(-iv.mpf(g)).b
        P = Ball(pm(r), iv.mpf(0) if real else pm(r))
    W = a_add(A.W, P)
    if isinstance(W, Tow) and W.im is None and not isreal(W):
        # Im(W + P) = Im W + Im P, kept when the sum is a tower too
        try:
            iA = A.W.im if isinstance(A.W, Ball) else (0 if isreal(A.W) else A.W.im)
            if iA is not None:
                W = Tow(W.W, W.s, W.ph, iA + im_bound(P))
        except Undecided:
            pass
    return mkexp(W, A.s, ph_add(A.ph, P))


def im_bound(A):
    """A real interval containing Im A."""
    if isinstance(A, Ball):
        return A.im
    if isreal(A):
        return iv.mpf(0)
    return pm(mag_up(A))


def ph_add(ph, P):
    """The phase ph shifted by Im P, or None."""
    if ph is None:
        return None
    try:
        return ph + im_bound(P)
    except Undecided:
        return None


def ln1p_enc(u, g):
    """An enclosure of ln(1 + u), given |u| <= e^-g with g >= 1."""
    m = iv.exp(-iv.mpf(g)).b
    if isinstance(u, Ball):
        m = min(m, mag_up(u))
        if m < mpf(2) ** -30:
            # |ln(1 + u) - u| <= 2|u|^2 for |u| <= 1/2
            r = 2 * m * m
            return Ball(u.re + pm(r), u.im + (iv.mpf(0) if isreal(u) else pm(r)))
        return a_log(Ball(1 + u.re, u.im))  # Re(1 + u) > 0: no cut
    # ln(1 + u) = u(1 + t) with |t| <= |u|, and |ln(1 + t)| <= 2|t|
    return mkexp(a_add(u.W, Ball(pm(2 * m), iv.mpf(0) if isreal(u) else pm(2 * m))), u.s)


def logform(A):
    """(W, s) with A = s*exp(W)."""
    if isinstance(A, Tow):
        return A.W, A.s
    if isreal(A):
        sg = sign_iv(A.re)
        if sg in (None, 0):
            raise Undecided("log of an interval around 0")
        return Ball(iv.log(abs(A.re))), sg
    m2 = A.re * A.re + A.im * A.im
    if m2.a <= 0:
        raise Undecided("log of a rectangle around 0")
    if A.re.a > 0 or A.im.a > 0 or A.im.b < 0:
        return Ball(iv.log(m2) / 2, iv.atan2(A.im, A.re)), 1
    # straddles the negative axis: use -A
    return Ball(iv.log(m2) / 2, iv.atan2(-A.im, -A.re)), -1


def a_add(A, B):
    if is_zero(A):
        return B
    if is_zero(B):
        return A
    if isinstance(A, Ball) and isinstance(B, Ball):
        return Ball(A.re + B.re, A.im + B.im)
    g = dom_gap(A, B)
    if g is not None:
        return absorb(A, B, g)
    g = dom_gap(B, A)
    if g is not None:
        return absorb(B, A, g)
    W1, s1 = logform(A)
    W2, s2 = logform(B)
    return combine(W1, s1, W2, s2, a_add(W2, a_neg(W1)))


def combine(W1, s1, W2, s2, D):
    """s1*exp(W1) + s2*exp(W2), given an enclosure D of W2 - W1."""
    if is_tiny(D):
        # |D| <= m < e^-5: 1 + e^D = 2 + O(m); 1 - e^D = -D(1 + t) with |t| <= |D|
        m = mag_up(D)
        if s1 * s2 == 1:
            q = Ball(2 + pm(2 * m), iv.mpf(0) if isreal(D) else pm(2 * m))
            Wq, sq = logform(q)
        else:
            Wq = a_add(D.W, Ball(pm(2 * m), iv.mpf(0) if isreal(D) else pm(2 * m)))
            sq = -D.s
        return mkexp(a_add(W1, Wq), s1 * sq)
    if not isinstance(D, Ball) or D.re.b > 60 or D.re.a < -60:
        raise Undecided("comparable towers")
    m = mag_up(D)
    if s1 * s2 == -1 and m < mpf(2) ** -10:
        # 1 - e^D = -(D + rho), |rho| <= |D|^2 for |D| <= 1/2
        r = m * m
        q = Ball(-(D.re + pm(r)), -(D.im + (iv.mpf(0) if isreal(D) else pm(r))))
    else:
        e = mkexp(D, s1 * s2)
        q = Ball(1 + e.re, e.im)
    Wq, sq = logform(q)
    return mkexp(a_add(W1, Wq), s1 * sq)


def logph(A, W):
    """A phase of s*exp(W) = A: A's own ph for a tower, else Im W when it is a rectangle."""
    if isinstance(A, Tow) and A.ph is not None:
        return A.ph
    return W.im if isinstance(W, Ball) else None


def a_mul(A, B):
    if isinstance(A, Ball) and isinstance(B, Ball):
        if isreal(A) and isreal(B):
            return Ball(A.re * B.re)
        return Ball(A.re * B.re - A.im * B.im, A.re * B.im + A.im * B.re)
    W1, s1 = logform(A)
    W2, s2 = logform(B)
    p1, p2 = logph(A, W1), logph(B, W2)
    return mkexp(a_add(W1, W2), s1 * s2, None if p1 is None or p2 is None else p1 + p2)


def a_inv(A):
    W, s = logform(A)
    p = logph(A, W)
    return mkexp(a_neg(W), s, None if p is None else -p)


def a_scale(A, c):
    if c == 1:
        return A
    if c == -1:
        return a_neg(A)
    return a_mul(A, Ball(iv.mpf(c)))


def ifloor(t):
    """Exact integer floors of both endpoints of an interval. (mpmath.floor would round
    a huge endpoint to 53 bits first, so two different endpoints could share a floor.)"""
    out = []
    for raw in t._mpi_:
        sign, man, exp, _ = raw
        if man == 0:
            if exp != 0:
                raise Undecided("infinite or nan endpoint")
            out.append(0)
            continue
        if exp >= 0:
            q = man << exp
            out.append(-q if sign else q)
        else:
            q = man >> -exp
            exact = (q << -exp) == man
            out.append(q if not sign else -q - (0 if exact else 1))
    return out[0], out[1]


def cell_range(y, neg):
    """(lo, hi): every n with y + (pi if neg) - 2*pi*n in [-pi, pi) for some y in the
    interval. With neg, n = 1 + floor(y / 2pi): y is not shifted by pi first, so a tiny
    y keeps its sign."""
    if not neg:
        return ifloor((y + iv.pi) / (2 * iv.pi))
    lo, hi = ifloor(y / (2 * iv.pi))
    return lo + 1, hi + 1


def cell(y, neg):
    """The n of cell_range when it is unique, else None."""
    lo, hi = cell_range(y, neg)
    return lo if lo == hi else None


def floor_cell(Y):
    """n with Y + pi in [2*pi*n, 2*pi*(n+1)) for all Y in the interval, else None."""
    t = (Y + iv.pi) / (2 * iv.pi)
    lo, hi = ifloor(t)
    return lo if lo == hi else None


def a_log(A):
    """Principal log on the lower cut (Arg in [-pi, pi))."""
    if isinstance(A, Ball):
        if isreal(A):
            sg = sign_iv(A.re)
            if sg == 1:
                return Ball(iv.log(A.re))
            if sg == -1:
                return Ball(iv.log(-A.re), -iv.pi)
            raise Undecided("log of a real interval around 0")
        m2 = A.re * A.re + A.im * A.im
        if m2.a <= 0:
            raise Undecided("log of a rectangle around 0")
        if A.re.a > 0 or A.im.a > 0 or A.im.b < 0:
            return Ball(iv.log(m2) / 2, iv.atan2(A.im, A.re))
        # The rectangle touches the cut, so the branch is unknown, but Arg is in
        # [-pi, pi) and ln|z| is still enclosed.
        return Ball(iv.log(m2) / 2, iv.mpf([-iv.pi.b, iv.pi.b]))
    W, s = A.W, A.s
    if isreal(W):
        return W if s > 0 else a_add(W, Ball(iv.mpf(0), -iv.pi))
    Y = a_im(W)
    if isinstance(Y, Ball):
        n = cell(Y.re, s < 0)
        if n is not None:
            return a_add(W, Ball(iv.mpf(0), (iv.pi if s < 0 else 0) - 2 * iv.pi * n))
    if A.ph is None:
        raise Undecided("tower phase" if not isinstance(Y, Ball) else "tower phase on the cut")
    # Im W is known only mod 2*pi, through ph: ln A = Re W + i*Arg A
    n = cell(A.ph, s < 0)
    if n is None:
        raise Undecided("tower phase on the cut")
    return a_add(a_re(W), Ball(iv.mpf(0), A.ph + (iv.pi if s < 0 else 0) - 2 * iv.pi * n))


# ---------------------------------------------------------------- exact layer

class Inf:
    """Real part s*inf; imaginary part exactly k*pi (k int) or in the interval im."""
    __slots__ = ("s", "k", "im")

    def __init__(self, s, k, im=None):
        self.s, self.k = s, k
        self.im = im if im is not None else (iv.pi * k if k is not None else None)


NAN = "nan"
CINF = "cinf"  # exp(+inf + i*theta) with theta unknown: infinite modulus, unknown direction

ATOMS = {}    # key -> dict(A=enclosure, real=bool, warg=lin for exp atoms)
LN_OF = {}    # key of L minus its i*pi part -> (k, z) with L = ln z and k the i*pi coefficient of L
APPROX = {}   # key of a combination -> its enclosure


def reset():
    ATOMS.clear()
    LN_OF.clear()
    APPROX.clear()
    ATOMS["1"] = dict(A=Ball(iv.mpf(1)), real=True, warg={})  # 1 = exp(0)
    ATOMS["ipi"] = dict(A=Ball(iv.mpf(0), iv.pi), real=False)


def key(lin):
    return "+".join(f"{c}*{a}" for a, c in sorted(lin.items())) or "0"


def lsub(a, b):
    out = dict(a)
    for t, c in b.items():
        out[t] = out.get(t, 0) - c
        if out[t] == 0:
            del out[t]
    return out


def lneg(a):
    return {t: -c for t, c in a.items()}


def lin_real(lin):
    return all(ATOMS[a]["real"] for a in lin)


def exact_k(lin):
    """k when Im(lin) is exactly k*pi, else None."""
    rest = [a for a in lin if a != "ipi"]
    return lin.get("ipi", 0) if lin_real(rest) else None


def new_atom(k, A, **kw):
    if k not in ATOMS:
        ATOMS[k] = dict(A=A, real=isreal(A), **kw)
    return k


def approx(lin):
    """Rigorous enclosure of a combination."""
    k = key(lin)
    if k in APPROX:
        return APPROX[k]
    if any(ATOMS[a]["A"] is None for a in lin):
        raise Undecided("imaginary part is a tower")
    terms = list(lin.items())
    # merge pairs of comparable exp atoms through the exact difference of their arguments
    pieces = []
    exps = [(a, c) for a, c in terms if "warg" in ATOMS[a]]
    others = [(a, c) for a, c in terms if "warg" not in ATOMS[a]]
    used = set()
    for i, (a1, c1) in enumerate(exps):
        if a1 in used:
            continue
        for a2, c2 in exps[i + 1:]:
            if a2 in used or abs(c1) != 1 or abs(c2) != 1:
                continue
            try:
                D = approx(lsub(ATOMS[a2]["warg"], ATOMS[a1]["warg"]))
            except Undecided:
                continue
            if is_tiny(D) or (isinstance(D, Ball) and -60 < D.re.a and D.re.b < 60):
                W1 = approx(ATOMS[a1]["warg"])
                W2 = approx(ATOMS[a2]["warg"])
                pieces.append(combine(W1, c1, W2, c2, D))
                used |= {a1, a2}
                break
    for a, c in exps:
        if a not in used:
            pieces.append(a_scale(ATOMS[a]["A"], c))
    for a, c in others:
        pieces.append(a_scale(ATOMS[a]["A"], c))
    pieces.sort(key=rough, reverse=True)
    out = Ball(iv.mpf(0))
    for p in pieces:
        out = a_add(out, p)
    if isinstance(out, Tow) and out.im is None and not isreal(out.W):
        try:
            Y = im_sum(lin)
            if isinstance(Y, Ball):
                out = Tow(out.W, out.s, out.ph, Y.re)
        except Undecided:
            pass
    APPROX[k] = out
    return out


def rough(A):
    """A float-ish size used only to order a sum (no effect on soundness)."""
    lvl = 0
    while isinstance(A, Tow):
        A = A.W
        lvl += 1
    try:
        x = float(abs(A.re.mid)) + float(abs(A.im.mid))
    except Exception:
        x = 0.0
    return (lvl, x)


def mk_exp(v, src=None):
    if v is NAN:
        return NAN
    if isinstance(v, Inf):
        if v.s < 0:
            return {}
        if v.k is not None:
            return Inf(1 if v.k % 2 == 0 else -1, 0)
        return CINF  # |exp(+inf + i*theta)| = inf whatever theta is
    if v is CINF:
        raise Undecided("exp of a complex infinity")
    if not v:
        return {"1": 1}
    k = v.get("ipi", 0)
    w = {a: c for a, c in v.items() if a != "ipi"}
    if key(w) in LN_OF:
        # v = ln z + (k - k0)*pi*i, so exp(v) = (-1)^(k - k0) z
        k0, z = LN_OF[key(w)]
        sz = 1 if (k - k0) % 2 == 0 else -1
        return {a: sz * c for a, c in z.items()}
    sign = 1 if k % 2 == 0 else -1
    if not w:
        return {"1": sign}
    kk = f"E[{key(w)}]"
    atom = kk if kk in ATOMS else new_atom(kk, a_exp_lin(w, src, k), warg=w)
    return {atom: sign}


PHASE = None  # deep.py's phase oracle: PHASE(word) -> a real interval congruent to Im(word) mod 2*pi


def a_exp_lin(w, src=None, k=0):
    """exp(w). A tower keeps the phase Im w when its enclosure is wide: from the exact layer
    (Im w summed atom by atom), else, with deep.py, from the subword src whose value is w + k*pi*i."""
    A = mkexp(approx(w), 1)
    if not isinstance(A, Tow) or A.ph is not None or isreal(A.W):
        return A
    def reduces(Y):
        # narrow first: a wide interval may have endpoints far too large to floor
        return isinstance(Y, Ball) and Y.re.b - Y.re.a < 1 and cell(Y.re, False) is not None
    try:
        if reduces(a_im(A.W)):
            return A
    except Undecided:
        pass
    try:
        Y = im_sum(w)
        if reduces(Y):
            return Tow(A.W, A.s, Y.re)
    except Undecided:
        pass
    if PHASE is not None and src is not None:
        ph = PHASE(src)
        if ph is not None:
            return Tow(A.W, A.s, ph - k * iv.pi)
    return A


def im_of(lin):
    """Im(lin) as a rectangle's real interval part (Ball), else Undecided."""
    Y = im_sum(lin)
    if not isinstance(Y, Ball):
        Y2 = a_im(approx(lin))
        if not isinstance(Y2, Ball):
            raise Undecided("imaginary part is a tower")
        return Y2
    return Y


def im_sign(lin):
    """Sign of Im(lin): 1, -1, 0 or None. An atom whose imaginary part is too small for
    its enclosure to carry a sign (a phase below e^-(10^15)) counts with the sign the
    exact layer recorded for it (ln(1 + u) has the sign of Im u), within its modulus."""
    known, tiny = [], []
    for a, c in lin.items():
        info = ATOMS[a]
        if info["real"]:
            continue
        if info["A"] is None:
            return None
        try:
            Y = a_scale(a_im(info["A"]), c)
            if real_sign(Y) is not None or info.get("imsign") is None:
                known.append(Y)
                continue
        except Undecided:
            if info.get("imsign") is None:
                return None
        try:
            tiny.append((c * info["imsign"], abs(c) * mag_up(info["A"])))
        except Undecided:
            return None
    known.sort(key=rough, reverse=True)
    S = Ball(iv.mpf(0))
    for p in known:
        S = a_add(S, p)
    sS = real_sign(S)
    if not tiny:
        return sS
    signs = {t[0] for t in tiny}
    if sS == 0:
        return signs.pop() if len(signs) == 1 and 0 not in signs else None
    if sS is None:
        return None
    bound = sum(t[1] for t in tiny)
    lS = lm(S)
    if lS is None or bound == 0:
        return sS if bound == 0 else None
    lb = iv.log(iv.mpf(bound)).b
    G = a_add(lS, Ball(-iv.mpf(lb)))
    if real_sign(G) == 1:
        return sS  # |S| > sum of the tiny terms
    return None


def im_sum(lin):
    """Im(lin) summed atom by atom, so a tiny phase is not swamped by the real parts."""
    pieces = []
    for a, c in lin.items():
        if ATOMS[a]["real"]:
            continue
        if ATOMS[a]["A"] is None:
            raise Undecided("imaginary part is a tower")
        pieces.append(a_scale(a_im(ATOMS[a]["A"]), c))
    pieces.sort(key=rough, reverse=True)
    out = Ball(iv.mpf(0))
    for p in pieces:
        out = a_add(out, p)
    return out


def ln_single(a, c):
    """ln(c*a) for one atom a, as a combination."""
    if a == "1":
        if c == 1:
            return {}
        if c > 0:
            return {new_atom(f"L[{c}*1]", Ball(iv.log(iv.mpf(c)))): 1}
        return lsub(ln_single("1", -c), {"ipi": 1})
    info = ATOMS[a]
    if "warg" in info and abs(c) == 1:
        w = info["warg"]
        if lin_real(w):
            return dict(w) if c > 0 else lsub(w, {"ipi": 1})
        try:
            Y = im_of(w)
        except Undecided:
            # Im w is a tower: ln(c*exp(w)) = w (+ i*pi) - 2*pi*i*n for some integer n that
            # nothing bounds. The real part is still exactly Re w; the rest is an atom that
            # is purely imaginary and has no enclosure.
            out = dict(w)
            if c < 0:
                out["ipi"] = out.get("ipi", 0) + 1
                if out["ipi"] == 0:
                    del out["ipi"]
            ATOMS.setdefault(f"N[{key({a: c})}]", dict(A=None, real=False, imonly=True))
            out[f"N[{key({a: c})}]"] = 1
            return out
        lo, hi = cell_range(Y.re, c < 0)
        if lo == hi:
            kk = (1 if c < 0 else 0) - 2 * lo
            out = dict(w)
            if kk:
                out["ipi"] = out.get("ipi", 0) + kk
            return out
        # The branch is not known: ln(c*exp(w)) = w (+ i*pi) - 2*pi*i*n for some integer n
        # in [lo, hi]. The real part is still exactly Re w; the unknown -2*pi*i*n is an
        # atom of its own, purely imaginary, that cancels with nothing else.
        out = dict(w)
        if c < 0:
            out["ipi"] = out.get("ipi", 0) + 1
            if out["ipi"] == 0:
                del out["ipi"]
        nk = new_atom(f"N[{key({a: c})}]", Ball(iv.mpf(0), -2 * iv.pi * iv.mpf([lo, hi])), imonly=True)
        out[nk] = 1
        return out
    return ln_generic({a: c})


def ln_generic(v):
    A = approx(v)
    if isreal(A):
        sg = real_sign(A)
        if sg == 1:
            return {new_atom(f"L[{key(v)}]", a_log(A)): 1}
        if sg == -1:
            nv = lneg(v)
            return {new_atom(f"L[{key(nv)}]", a_log(a_neg(A))): 1, "ipi": -1}
        raise Undecided("log of a real interval around 0")
    return {new_atom(f"L[{key(v)}]", a_log(A)): 1}


def mk_ln(v):
    if v is NAN:
        return NAN
    if v is CINF:
        raise Undecided("log of a complex infinity")
    if isinstance(v, Inf):
        if v.s > 0:
            return Inf(1, 0)
        if v.k is not None:
            side = -1 if v.k <= 0 else 1
        elif v.im.a > 0:
            side = 1
        elif v.im.b < 0:
            side = -1
        else:
            raise Undecided("log of -inf with an unknown side")
        return Inf(1, side)
    if not v:
        return Inf(-1, 0)
    out = ln_raw(v)
    LN_OF.setdefault(key({a: c for a, c in out.items() if a != "ipi"}), (out.get("ipi", 0), dict(v)))
    return out


def ln_raw(v):
    if len(v) == 1:
        (a, c), = v.items()
        return ln_single(a, c)
    # a dominant term t: ln v = ln t + ln(1 + r/t)
    for a, c in sorted(v.items()):
        t = {a: c}
        r = lsub(v, t)
        At = a_scale(ATOMS[a]["A"], c)
        try:
            Ar = approx(r)
            g = dom_gap(At, Ar, 1)
        except Undecided:
            continue
        if g is None:
            continue
        base = ln_single(a, c)
        u = a_mul(Ar, a_inv(At))
        m = iv.exp(-iv.mpf(g)).b  # |u| <= m <= e^-1
        P = ln1p_enc(u, g)
        # Im ln(1 + u) has the sign of Im u (Re(1 + u) > 0)
        if isreal(u):
            su = 0
        elif isreal(At):
            sr = im_sign(r)
            su = None if sr is None else sr * real_sign(At)
        else:
            su = real_sign(a_im(u))
        kb = exact_k(base)
        unknown = None  # (lo, hi): the correction is -2*pi*i*n for an unknown n in [lo, hi]
        if kb is not None:
            if su is None and kb == -1:
                wrap, unknown = 0, (-1, 0)
            else:
                wrap = 2 if (kb == -1 and su == -1) else 0
        else:
            Yb = im_of(base)
            YP = a_im(P)
            lo, hi = ifloor((Yb.re + (YP.re if isinstance(YP, Ball) else pm(m)) + iv.pi) / (2 * iv.pi))
            if lo == hi:
                wrap = -2 * lo
            else:
                wrap, unknown = 0, (lo, hi)
        atom = new_atom(f"P[{key(v)}]", P, imsign=su)
        out = dict(base)
        out[atom] = out.get(atom, 0) + 1
        if unknown is not None:
            nk = new_atom(f"N[{key(v)}]", Ball(iv.mpf(0), -2 * iv.pi * iv.mpf(list(unknown))), imonly=True)
            out[nk] = 1
        if wrap:
            out["ipi"] = out.get("ipi", 0) + wrap
            if out["ipi"] == 0:
                del out["ipi"]
        return out
    return ln_generic(v)


def sub(a, b):
    if a is NAN or b is NAN:
        return NAN
    if isinstance(a, dict) and isinstance(b, dict):
        return lsub(a, b)
    def fin_im(f):
        kk = exact_k(f)
        return kk, (iv.pi * kk if kk is not None else im_of(f).re)
    if CINF in (a, b):
        if isinstance(a, Inf) or isinstance(b, Inf) or a is b:
            raise Undecided("complex infinity beside an infinity")
        return CINF
    if isinstance(a, Inf) and isinstance(b, dict):
        kb, ib = fin_im(b)
        return Inf(a.s, a.k - kb if a.k is not None and kb is not None else None, a.im - ib)
    if isinstance(b, Inf) and isinstance(a, dict):
        ka, ia = fin_im(a)
        return Inf(-b.s, ka - b.k if b.k is not None and ka is not None else None, ia - b.im)
    if a.s == -b.s:
        return Inf(a.s, a.k - b.k if a.k is not None and b.k is not None else None, a.im - b.im)
    return NAN


def evaluate(word):
    reset()
    st = []
    for ch in word:
        if ch == "1":
            st.append(({"1": 1}, "1"))
        else:
            y, wy = st.pop()
            x, wx = st.pop()
            st.append((sub(mk_exp(x, wx), mk_ln(y)), wx + wy + "E"))
    return st[0][0]


def excludes(word, tre, tk=0):
    """True: certainly not tre + tk*pi*i. False: equal (exact). Raises Undecided."""
    v = evaluate(word)
    if v is NAN or v is CINF or isinstance(v, Inf):
        return True
    target = {}
    if tre:
        target["1"] = tre
    if tk:
        target["ipi"] = tk
    d = lsub(v, target)
    if not d:
        return False
    why = "enclosure of value - target contains 0"
    try:
        A = approx(d)
        if isinstance(A, Tow):
            return True
        if sign_iv(A.re) in (1, -1) or sign_iv(A.im) in (1, -1):
            return True
    except Undecided as e:
        why = str(e)
    try:
        if im_sign(d) in (1, -1):
            return True
    except Undecided:
        pass
    # The real part alone: purely imaginary atoms (the unknown -2*pi*i*n of a branch) drop out.
    dr = {a: c for a, c in d.items() if not ATOMS[a].get("imonly") and a != "ipi"}
    if dr and len(dr) < len(d):
        R = a_re(approx(dr))
        if isinstance(R, Tow) or sign_iv(R.re) in (1, -1):
            return True
    raise Undecided(why)


def decide(word, tre, tk=0):
    """(True, None) excluded, (False, None) equal, (None, reason) undecided."""
    reason = None
    for bits in (128, 512):
        iv.prec = bits
        try:
            return excludes(word, tre, tk), None
        except Undecided as why:
            reason = str(why)
        except (ZeroDivisionError, ValueError, OverflowError) as why:
            reason = f"{type(why).__name__}: {why}"
    return None, reason
