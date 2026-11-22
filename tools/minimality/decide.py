"""Independent check of the minimality claims in docs/minimality.md.

Every constant EML program with at most K tokens is evaluated rigorously, on the
lower cut (Arg in [-pi, pi)) with ln 0 = -inf, and is EXCLUDED as a candidate for
the target only when that is certain:

- its value is +-inf, an invalid inf - inf, or a tower far outside float range, or
- the target lies outside the interval rectangle (mpmath.iv) that encloses it.

Three devices keep the enclosures decisive:

- An exact tag k when the imaginary part is exactly k*pi, so exp(x + k*pi*i) is
  (-1)^k e^x exactly and ln of a negative real takes arg -pi symbolically.
- A canonical symbolic form per value with sound rewrites: ln 1 = 0, a - 0 = a,
  ln(exp x) = x for a real x, exp(ln z) = z, and a - a = 0 when both sides have the
  same form. That is how e - ln(exp e) is an exact 0, not an interval around 0.
- Towers: a real past exp(10^6) is kept as +-exp(L), and one below exp(-10^6) as
  exp(-L), with L itself an interval or a tower. ln(+-exp L) = L (- i*pi), and adding a
  value far smaller widens L by a rigorous bound.

Anything else is UNDECIDED and reported, never assumed. Undecided programs are
retried at higher precision before they are reported.

usage: python decide.py [max_K]     the claims in docs/minimality.md (default 17)
       python decide.py --open      +i*pi at K 21 and -2 at K 25 (README: shortest known)
"""
import sys
from mpmath import iv, mpf

LIMIT = mpf(10) ** 6  # past exp(LIMIT), a real is kept as a tower


class Undecided(Exception):
    pass


class V:
    """kind: fin | inf | big | small | nan.
    fin:   re, im intervals; k = exact multiple of pi in im (or None)
    inf:   s = +1/-1 (real part s*inf); im, k as for fin
    big:   s*exp(L), L a real V (fin with L > 10^6, or big)
    bigk:  s*exp(L) + k*pi*i, a tower with an exact phase (excluded, never reused)
    huge:  any complex value with ln|value| >= lm > 10^6 (excluded; only sums with far
           smaller finite values are followed)
    small: s*exp(-L), L a real V (fin with L > 10^6, or big)
    """

    __slots__ = ("kind", "re", "im", "k", "s", "L", "sym", "prov", "lin", "off", "lm")

    def __init__(self, kind, sym, re=None, im=None, k=None, s=None, L=None, prov=None, lin=None):
        self.kind, self.sym, self.re, self.im, self.k, self.s, self.L, self.prov = kind, sym, re, im, k, s, L, prov
        # A finite value's form as an integer combination of atoms ("1", "exp(..)", "ln(..)").
        self.lin = lin if lin is not None else {sym: 1}
        # off: the value is its form plus an infinitesimal delta (|delta| < 1e-1000) of
        # this sign. Set where exp(L) - c is rewritten as exp(L + delta).
        self.off = None
        # huge: lm is a lower bound on ln|value| (None: a tower of towers, beyond any bound)
        self.lm = None


def key_of(lin):
    if len(lin) == 1:
        (atom, c), = lin.items()
        if c == 1:
            return atom
    return "+".join(f"{c}*{a}" for a, c in sorted(lin.items())) or "0"


# atom -> its argument, so ln(exp x) = x and exp(ln z) = z fire on any value whose
# form is that single atom, not only on the object exp or ln returned.
EXP_ARG = {}
LN_ARG = {}


def single_atom(v):
    """The atom when v's form is exactly that one atom (coefficient 1, no offset)."""
    if v.kind in ("fin", "big", "small") and len(v.lin) == 1 and v.off is None:
        (atom, c), = v.lin.items()
        if c == 1:
            return atom
    return None


def combine_off(o1, o2):
    """Net sign of two infinitesimal offsets (None = none, "mixed" = unknown)."""
    if o1 is None:
        return o2
    if o2 is None or o1 == o2:
        return o1
    return "mixed"


def neg_off(o):
    return -o if o in (1, -1) else o


def eff_lin(v):
    """A tiny value contributes no atom, only an offset."""
    return {} if v.kind == "small" else v.lin


def eff_off(v):
    return v.s if v.kind == "small" else v.off


def tag(sym, off):
    """Atoms of a value with an offset must differ from those of the exact form."""
    return sym if off is None else f"{sym}~{'+' if off == 1 else '-' if off == -1 else '?'}"


def zero():
    return V("fin", "0", iv.mpf(0), iv.mpf(0), 0, lin={})


def is_zero(v):
    return v.kind == "fin" and v.k == 0 and v.re.a == 0 and v.re.b == 0


def real(v):
    return v.kind in ("big", "small") or (v.kind == "fin" and v.k == 0)


def cexp(v):
    out = cexp_raw(v)
    if out.kind in ("fin", "big", "small") and out.sym.startswith("exp("):
        EXP_ARG.setdefault(out.sym, v)
    return out


def cexp_raw(v):
    sym = f"exp({v.sym})"
    if v.kind == "bigk":
        # exp(s*exp(L) + k*pi*i) = (-1)^k exp(s*exp(L)), exactly (k is an integer)
        sign = 1 if v.k % 2 == 0 else -1
        tower = V("big", f"exp({v.L.sym})", s=1, L=v.L)
        return V("big", sym, s=sign, L=tower) if v.s > 0 else V("small", sym, s=sign, L=tower)
    if v.kind == "huge":
        raise Undecided("exp of a huge value")
    if v.kind == "fin" and v.k is None and v.re.a > LIMIT:
        return huge(sym, v.re.a)  # |exp(L + i theta)| = exp(L)
    if v.kind == "fin" and v.prov and v.prov[0] == "nudge" and v.prov[1] == 0 and v.k is not None:
        # exp(k*pi*i + delta) = (-1)^k e^delta: within 1e-999 of (-1)^k, on the side
        # given by the sign of (-1)^k * delta.
        sign = 1 if v.k % 2 == 0 else -1
        d = iv.mpf([-1e-999, 1e-999])
        out = V("fin", sym + "~", iv.mpf(sign) + d, iv.mpf(0), 0, prov=("nudge", mpf(sign), sign * v.prov[2]), lin={"1": sign})
        out.off = sign * v.prov[2]
        return out
    if v.kind == "fin" and v.k is not None and v.off in (1, -1) and v.re.b < LIMIT and v.re.a > -LIMIT:
        # exp(X + k*pi*i + delta) = (-1)^k exp(X) (1 + delta), X the exact real part
        xlin = {a: c for a, c in v.lin.items() if a != "ipi"}
        X = V("fin", key_of(xlin), v.re, iv.mpf(0), 0, lin=xlin)
        atom = f"exp({X.sym})"
        EXP_ARG.setdefault(atom, X)
        sign = 1 if v.k % 2 == 0 else -1
        out = V("fin", tag(atom if sign == 1 else f"-{atom}", sign * v.off), iv.exp(v.re) * sign, iv.mpf(0), 0, lin={atom: sign})
        out.off = sign * v.off
        return out
    if is_zero(v):
        return V("fin", "1", iv.mpf(1), iv.mpf(0), 0)  # exp(0) = 1
    if v.prov and v.prov[0] == "ln" and v.off is None:
        return v.prov[1]  # exp(ln z) = z
    atom = single_atom(v)
    if atom in LN_ARG:
        return LN_ARG[atom]  # exp(ln z) = z
    if v.kind == "nan":
        return v
    if v.kind == "inf":
        if v.s < 0:
            return V("fin", "0", iv.mpf(0), iv.mpf(0), 0)
        if v.k is not None:
            return V("inf", sym, im=iv.mpf(0), k=0, s=1 if v.k % 2 == 0 else -1)
        raise Undecided("exp of a directed infinity")
    if v.kind == "big":
        if v.s > 0:
            return V("big", sym, s=1, L=v, prov=("exp", v))
        return V("small", sym, s=1, L=V("big", f"-({v.sym})", s=1, L=v.L), prov=("exp", v))
    if v.kind == "small":
        d = iv.mpf([-1e-1000, 1e-1000])
        return V("fin", sym, 1 + d, iv.mpf(0), 0, prov=("exp", v))
    re, im, k = v.re, v.im, v.k
    sign = None if k is None else (1 if k % 2 == 0 else -1)
    if re.a > LIMIT:
        if sign is None:
            raise Undecided("tower with a phase")
        return V("big", sym, s=sign, L=V("fin", v.sym, re, iv.mpf(0), 0), prov=("exp", v))
    if re.b < -LIMIT:
        if sign is None:
            raise Undecided("tiny value with a phase")
        return V("small", sym, s=sign, L=V("fin", f"-({v.sym})", -re, iv.mpf(0), 0), prov=("exp", v))
    m = iv.exp(re)
    if sign is not None:
        return V("fin", sym, m * sign, iv.mpf(0), 0, prov=("exp", v))
    return V("fin", sym, m * iv.cos(im), m * iv.sin(im), None, prov=("exp", v))


def neg_of(L):
    """-L for a real V."""
    if L.kind == "fin":
        return V("fin", f"-({L.sym})", -L.re, iv.mpf(0), 0)
    if L.kind == "big":
        return V("big", f"-({L.sym})", s=-L.s, L=L.L)
    raise Undecided("negating a tiny value")


def clog(v):
    out = clog_raw(v)
    if out.kind in ("fin", "big", "small", "inf") and out.sym.startswith("ln("):
        LN_ARG.setdefault(out.sym, v)
    return out


def clog_raw(v):
    sym = f"ln({v.sym})"
    if v.kind == "huge":
        raise Undecided("log of a huge value")
    if v.kind == "bigk":
        # ln(s*exp(L) + k*pi*i) = L + ln(s + k*pi*i*e^-L): the real part moves by less than
        # 1e-1000, and Arg sits within 1e-1000 of 0 (s = +1) or of +-pi (s = -1) on the side of k.
        t = iv.mpf([0, 1e-1000])
        if v.s > 0:
            theta = iv.mpf(0) if v.k == 0 else (t if v.k > 0 else -t)
        else:
            theta = -iv.pi if v.k == 0 else (iv.pi - t if v.k > 0 else -iv.pi + t)
        L = v.L
        if L.kind == "fin":
            return V("fin", sym, L.re + iv.mpf([-1e-1000, 1e-1000]), theta, None)
        return huge(sym, tower_lm(L.L) if L.L is not None and L.L.kind == "fin" else None)
    if v.prov and v.prov[0] == "exp" and real(v.prov[1]) and v.off is None:
        return v.prov[1]  # ln(exp x) = x for a real x
    atom = single_atom(v)
    if atom in EXP_ARG and real(EXP_ARG[atom]):
        return EXP_ARG[atom]  # ln(exp x) = x for a real x
    if v.kind == "fin" and v.prov and v.prov[0] == "nudge" and v.prov[1] in (1, -1) and v.k == 0:
        # ln(c + delta) with c = +-1: real part delta/c (signed infinitesimal), Arg 0 or -pi exactly
        c, sgn = v.prov[1], v.prov[2]
        k = 0 if c > 0 else -1
        off = sgn * (1 if c > 0 else -1)
        d = iv.mpf([-1e-1000, 1e-1000])
        out = V("fin", tag(f"ln({c})", off), d, iv.pi * k, k, prov=("nudge", mpf(0), off), lin=({"ipi": k} if k else {}))
        out.off = off
        return out
    if v.kind == "fin" and v.k == 0 and len(v.lin) == 1 and v.off in (1, -1):
        (atom, c), = v.lin.items()
        X = EXP_ARG.get(atom)
        if X is not None and X.kind == "fin" and X.k == 0 and c in (1, -1) and X.off is None:
            # ln(c*exp(X) + delta) = X + ln(1 + c*delta*e^-X) (- i*pi when c = -1):
            # the real part moves by a tiny amount of sign c*sign(delta).
            off = c * v.off
            d = iv.mpf([-1e-1000, 1e-1000])
            lin = dict(X.lin)
            if c == -1:
                lin["ipi"] = lin.get("ipi", 0) - 1
            out = V("fin", tag(key_of(lin), off), X.re + d, iv.mpf(0) if c == 1 else -iv.pi, 0 if c == 1 else -1, lin=lin)
            out.off = off
            return out
    if v.off is not None and v.prov and v.prov[0] == "exp":
        pass  # the provenance rewrite below would drop the offset
    if v.kind == "fin" and v.lin == {"1": 1}:
        return zero()
    if v.kind == "nan":
        return v
    if v.sym == "1":
        return zero()
    if is_zero(v):
        return V("inf", sym, im=iv.mpf(0), k=0, s=-1, prov=("ln", v))
    if v.kind == "inf":
        # The real part is infinite and the imaginary part finite, so Arg tends to 0
        # (+inf) or to +-pi by the sign of the imaginary part (-inf); an exact 0 there
        # takes the lower bank, -pi. reachable-values.md states the same rules.
        if v.s > 0:
            return V("inf", sym, im=iv.mpf(0), k=0, s=1, prov=("ln", v))
        if v.k is not None:
            side = -1 if v.k <= 0 else 1
        elif v.im.a > 0:
            side = 1
        elif v.im.b < 0:
            side = -1
        else:
            raise Undecided("log of -inf with an unknown side")
        return V("inf", sym, im=iv.pi * side, k=side, s=1, prov=("ln", v))
    if v.kind == "big":
        L = v.L
        if v.s > 0:
            return L
        if L.kind == "fin":
            lin = dict(L.lin)
            lin["ipi"] = lin.get("ipi", 0) - 1
            out = V("fin", sym, L.re, -iv.pi, -1, prov=("ln", v), lin=lin)
            out.off = L.off
            return out
        return V("bigk", sym, s=L.s, L=L, k=-1)  # L - i*pi with L a tower
    if v.kind == "small":
        mL = neg_of(v.L)
        if v.s > 0:
            return mL
        if mL.kind == "fin":
            return V("fin", sym, mL.re, -iv.pi, -1, prov=("ln", v))
        raise Undecided("log of a negative tiny tower")
    re, im, k = v.re, v.im, v.k
    if k == 0:
        if re.a > 0:
            return V("fin", sym, iv.log(re), iv.mpf(0), 0, prov=("ln", v))
        if re.b < 0:
            return V("fin", sym, iv.log(-re), -iv.pi, -1, prov=("ln", v))
        raise Undecided("real interval contains 0")
    mag2 = re * re + im * im
    if mag2.a <= 0:
        raise Undecided("modulus interval contains 0")
    if re.a > 0 or im.a > 0 or im.b < 0:
        return V("fin", sym, iv.log(mag2) / 2, iv.atan2(im, re), None, prov=("ln", v))
    raise Undecided("rectangle touches the cut")


def huge(sym, lm):
    out = V("huge", sym)
    out.lm = lm
    return out


def tower_lm(L):
    """A lower bound on ln|exp(L)| = L for a real V L, or None for a tower of towers."""
    return L.re.a if L.kind == "fin" else None


def magnitude_log(v):
    """An upper bound on ln|v| for a fin value (None if v may be 0)."""
    m = max(abs(v.re.a), abs(v.re.b)) + max(abs(v.im.a), abs(v.im.b))
    return iv.log(iv.mpf(m) + 1).b


def widen(L, rel):
    """L + [-rel, rel] for a real V L (rel an mpf)."""
    if L.kind == "fin":
        return V("fin", L.sym + "~", L.re + iv.mpf([-rel, rel]), iv.mpf(0), 0)
    return L  # a tower of towers is not moved by a relative change this small


def sub_raw(a, b):
    sym = f"({a.sym}-{b.sym})"
    if a.kind == "nan" or b.kind == "nan":
        return V("nan", "nan")
    if is_zero(b):
        return a
    if a.kind in ("fin", "big", "small") and b.kind in ("fin", "big", "small") and not (a.kind == "small" and b.kind == "small"):
        lin = dict(eff_lin(a))
        for atom, c in eff_lin(b).items():
            lin[atom] = lin.get(atom, 0) - c
            if lin[atom] == 0:
                del lin[atom]
        # Offsets only add information: when their net sign is unknown the interval
        # below (which already includes +-1e-1000) decides, or nothing does.
        oa, ob = eff_off(a), eff_off(b)
        net = None
        if "mixed" not in (oa, ob):
            if oa is not None and ob is None:
                net = oa
            elif ob is not None and oa is None:
                net = -ob
            elif oa is not None and ob is not None and oa == -ob:
                net = oa
        unknown_offset = (oa is not None or ob is not None) and net is None
        if set(lin) <= {"1", "ipi"}:
            c = lin.get("1", 0)
            kpi = lin.get("ipi", 0)
            if net is None and not unknown_offset:
                return V("fin", key_of(lin), iv.mpf(c), iv.pi * kpi, kpi, lin=lin)  # exact c + k*pi*i
            if net is None:
                d = iv.mpf([-1e-1000, 1e-1000])
                return V("fin", key_of(lin) + "~", iv.mpf(c) + d, iv.pi * kpi, kpi)  # within 1e-1000, sign unknown
            d = iv.mpf([-1e-1000, 1e-1000])
            out = V("fin", key_of(lin) + "~", iv.mpf(c) + d, iv.pi * kpi, kpi, prov=("nudge", mpf(c), net))
            return out  # exact form plus a nonzero infinitesimal of known sign
        sym = key_of(lin)
    else:
        lin = None
    # towers and tiny values beside finite ones
    if a.kind == "huge" or b.kind == "huge":
        h, f = (a, b) if a.kind == "huge" else (b, a)
        if f.kind != "fin":
            raise Undecided("huge value beside a non-finite one")
        if h.lm is None or h.lm - magnitude_log(f) >= 100:
            return huge(sym, h.lm)
        raise Undecided("huge value beside a comparable one")
    if a.kind == "big" and b.kind == "fin" and b.k is None:
        lm = tower_lm(a.L)
        if lm is None or lm - magnitude_log(b) >= 100:
            return huge(sym, lm)
        raise Undecided("tower beside a comparable value")
    if b.kind == "big" and a.kind == "fin" and a.k is None:
        lm = tower_lm(b.L)
        if lm is None or lm - magnitude_log(a) >= 100:
            return huge(sym, lm)
        raise Undecided("tower beside a comparable value")
    if a.kind == "bigk" or b.kind == "bigk":
        # a tower with an exact phase k*pi, minus or from a finite value: still a tower
        if a.kind == "bigk" and b.kind == "fin" and b.k is not None:
            return V("bigk", sym, s=a.s, L=a.L, k=a.k - b.k)
        if b.kind == "bigk" and a.kind == "fin" and a.k is not None:
            return V("bigk", sym, s=-b.s, L=b.L, k=a.k - b.k)
        raise Undecided("tower with a phase in a sum")
    if a.kind == "big" and b.kind == "fin" and b.k not in (0, None):
        gap = a.L.re.a - magnitude_log(b) if a.L.kind == "fin" else LIMIT
        if gap < 100:
            raise Undecided("tower beside a comparable value")
        return V("bigk", sym, s=a.s, L=a.L, k=-b.k)  # exp(L) - (c + k*pi*i): a tower with phase -k*pi
    if a.kind in ("big", "small") or b.kind in ("big", "small"):
        if a.kind == "big" and b.kind in ("fin", "small"):
            if b.kind == "fin" and b.k not in (0,):
                raise Undecided("tower minus a complex value")
            bound = 0 if b.kind == "small" else magnitude_log(b)
            gap = a.L.re.a - bound if a.L.kind == "fin" else LIMIT
            if gap < 100:
                raise Undecided("tower beside a comparable value")
            L2 = widen(a.L, 2 * iv.exp(-iv.mpf(gap)).b)
            # s*exp(L) - c = s*exp(L + ln(1 - c*s*e^-L)): delta has the sign of -c*s.
            csign = (1 if b.re.a > 0 else -1 if b.re.b < 0 else 0) if b.kind == "fin" else b.s
            if L2.kind == "fin" and csign != 0:
                L2.lin = dict(a.L.lin)
                d = -csign * a.s
                L2.off = d if a.L.off in (None, d) else "mixed"
            return V("big", sym, s=a.s, L=L2)
        if b.kind == "big" and a.kind in ("fin", "small"):
            if a.kind == "fin" and a.k not in (0,):
                raise Undecided("complex value minus a tower")
            bound = 0 if a.kind == "small" else magnitude_log(a)
            gap = b.L.re.a - bound if b.L.kind == "fin" else LIMIT
            if gap < 100:
                raise Undecided("tower beside a comparable value")
            L2 = widen(b.L, 2 * iv.exp(-iv.mpf(gap)).b)
            # c - s*exp(L) = -s*exp(L + ln(1 - c*s*e^-L)): delta has the sign of -c*s.
            csign = (1 if a.re.a > 0 else -1 if a.re.b < 0 else 0) if a.kind == "fin" else a.s
            if L2.kind == "fin" and csign != 0:
                L2.lin = dict(b.L.lin)
                d = -csign * b.s
                L2.off = d if b.L.off in (None, d) else "mixed"
            return V("big", sym, s=-b.s, L=L2)
        if a.kind == "small" and b.kind == "fin":
            # s*tiny - b with 0 < tiny < exp(-10^6): within 1e-1000 of -b, and never
            # equal to an exact -b, because exp of a finite value is never 0.
            d = iv.mpf([-1e-1000, 1e-1000])
            k = None if b.k is None else -b.k
            nudge = ("nudge", -b.re.a, a.s) if b.k == 0 and b.re.a == b.re.b else None
            return V("fin", sym, -b.re + d, -b.im, k, prov=nudge)
        if b.kind == "small" and a.kind == "fin":
            d = iv.mpf([-1e-1000, 1e-1000])
            nudge = ("nudge", a.re.a, -b.s) if a.k == 0 and a.re.a == a.re.b else None
            return V("fin", sym, a.re + d, a.im, a.k, prov=nudge)
        if a.kind in ("big", "small") and b.kind == "inf":
            return V("inf", sym, im=-b.im, k=(-b.k if b.k is not None else None), s=-b.s)
        if b.kind in ("big", "small") and a.kind == "inf":
            return V("inf", sym, im=a.im, k=a.k, s=a.s)
        raise Undecided("tower minus tower")
    if a.kind == "fin" and b.kind == "fin":
        k = a.k - b.k if a.k is not None and b.k is not None else None
        out = V("fin", sym, a.re - b.re, a.im - b.im, k)
        # an exact point plus a signed infinitesimal, minus an exact real point (or the reverse)
        exact = lambda x: x.k == 0 and x.re.a == x.re.b and not (x.prov and x.prov[0] == "nudge")
        if a.prov and a.prov[0] == "nudge" and exact(b):
            out.prov = ("nudge", a.prov[1] - b.re.a, a.prov[2])
        elif b.prov and b.prov[0] == "nudge" and exact(a):
            out.prov = ("nudge", a.re.a - b.prov[1], -b.prov[2])
        return out
    k = a.k - b.k if a.k is not None and b.k is not None else None
    im = a.im - b.im
    if a.kind == "fin":
        return V("inf", sym, im=im, k=k, s=-b.s)
    if b.kind == "fin":
        return V("inf", sym, im=im, k=k, s=a.s)
    if a.s == -b.s:
        return V("inf", sym, im=im, k=k, s=a.s)
    return V("nan", "nan")


def sub(a, b):
    out = sub_raw(a, b)
    if out is a or out is b or out.kind not in ("fin", "big", "small") or not out.lin or out.sym in ("0",):
        return out
    if a.kind in ("fin", "big", "small") and b.kind in ("fin", "big", "small") and out.kind in ("fin", "big"):
        lin = dict(eff_lin(a))
        for atom, c in eff_lin(b).items():
            lin[atom] = lin.get(atom, 0) - c
            if lin[atom] == 0:
                del lin[atom]
        out.lin = lin
        out.off = combine_off(eff_off(a), neg_off(eff_off(b)))
        out.sym = tag(key_of(lin), out.off)
    return out


def eml(x, y):
    return sub(cexp(x), clog(y))


ONE = None


def evaluate(word):
    st = []
    for ch in word:
        if ch == "1":
            st.append(V("fin", "1", iv.mpf(1), iv.mpf(0), 0))
        else:
            y = st.pop()
            x = st.pop()
            st.append(eml(x, y))
    return st[0]


def excludes(v, tre, tk=0):
    """True when the value is certainly not tre + tk*pi*i (tre rational, tk an integer)."""
    if tk != 0:
        if v.kind in ("nan", "inf", "big", "bigk", "small", "huge"):
            return True
        if v.prov and v.prov[0] == "nudge" and v.prov[1] == tre:
            return True  # real part is tre plus a nonzero infinitesimal
        if v.k is not None:
            return v.k != tk or tre < v.re.a or tre > v.re.b
        t_im = iv.pi * tk
        return t_im.b < v.im.a or t_im.a > v.im.b or tre < v.re.a or tre > v.re.b
    if v.kind in ("nan", "inf", "big", "bigk", "huge"):
        return True
    if v.kind == "small":
        return tre != 0  # |value| < exp(-10^6), and it is not exactly 0
    if v.prov and v.prov[0] == "nudge" and v.prov[1] == tre:
        return True  # exact point plus a nonzero tiny term
    if v.k is not None and v.k != 0:
        return True  # imaginary part is a nonzero multiple of pi
    if v.k is None and (v.im.a > 0 or v.im.b < 0):
        return True
    return tre < v.re.a or tre > v.re.b


def programs(n):
    out = []

    def gen(w, h, ones):
        if len(w) == 2 * n - 1:
            if h == 1:
                out.append(w)
            return
        if ones < n:
            gen(w + "1", h + 1, ones + 1)
        if h >= 2:
            gen(w + "E", h - 1, ones)

    gen("", 0, 0)
    return out


def uses_ln0(word):
    """Whether some gate takes ln of an exact 0."""
    st = []
    for ch in word:
        if ch == "1":
            st.append(V("fin", "1", iv.mpf(1), iv.mpf(0), 0))
        else:
            y = st.pop()
            x = st.pop()
            if is_zero(y):
                return True
            try:
                st.append(eml(x, y))
            except Undecided:
                return None  # unknown: counts against a "needs ln 0" claim
    return False


def decide(word, tre, tk=0):
    reason = None
    for bits in (128, 1024, 8192):
        iv.prec = bits
        EXP_ARG.clear()
        LN_ARG.clear()
        try:
            return excludes(evaluate(word), tre, tk), None
        except Undecided as why:
            reason = str(why)
    return None, reason


CLAIMS = [("0", 0, 5), ("-1", -1, 13), ("2", 2, 17)]


def prove(label, tre, tk, upto):
    """Exclude every program with K <= upto. Returns (proved, undecided, not excluded)."""
    undecided, equal, checked = [], [], 0
    for n in range(1, (upto + 1) // 2 + 1):
        for w in programs(n):
            checked += 1
            verdict, reason = decide(w, tre, tk)
            if verdict is None:
                undecided.append((w, reason))
            elif verdict is False:
                equal.append(w)
    status = "PROVED" if not undecided and not equal else "NOT PROVED"
    print(f"{label}: no program with K <= {upto} equals {label}: {status}  ({checked} programs, {len(equal)} not excluded, {len(undecided)} undecided)", flush=True)
    for w in equal[:10]:
        print(f"   not excluded: {w}")
    for w, r in undecided[:12]:
        print(f"   undecided: {w}  ({r})")
    return status == "PROVED"


def only_ln0(label, tre, tk, k):
    """Every program of length k that is not excluded must take ln of an exact 0."""
    n = (k + 1) // 2
    left = []
    for w in programs(n):
        verdict, reason = decide(w, tre, tk)
        if verdict is not True:
            left.append((w, verdict, reason))
    strict = [x for x in left if uses_ln0(x[0]) is not True]
    status = "PROVED" if not strict else "NOT PROVED"
    print(f"{label} without ln 0 needs more than K {k}: {status}  ({len(left)} K {k} programs not excluded, {len(strict)} of them without ln 0)", flush=True)
    for w, verdict, reason in strict[:10]:
        print(f"   {w}  {'undecided: ' + reason if verdict is None else 'not excluded'}")
    return not strict


# Words whose value is known to equal the target. The decider must never exclude
# them: an unsound rule would show up here first. Towers, ln 0 and k*pi tags all occur.
SELF_TEST = [
    ("111E1EE", 0, 0), ("11111E1EEEE11EE", -1, 0), ("11111EEE1EE11E1EE", -1, 0),
    ("111111EEE1EE11EE1EE", 2, 0), ("111111E1EEEE11E1E1EEE", 0, 1), ("111111E1E1EEE1EE11E1EEE", 0, 1),
    ("111111E1EEEE11E1E1EEE11EE", -2, 0), ("1111111EEE1EE11EEE1EE11E1EE", -2, 0),
    ("11111111EEE1EE11EEE1EE11EE1EE", 3, 0), ("111E11111E1EEEE11E1E1EE1EEE1E", mpf(1) / 2, 0),
    ("1111111E1EEEE11EEE11E1E1EEE1E", -mpf(1) / 2, 0), ("1111111EEE1EE11E1EEE11E1E1EEE1E", -mpf(1) / 2, 0),
    ("11111E1E1EEEE11111E1EEEE11111E1E1EEEE1E1E1EEE", 0, -1),
    ("11111E1E1EEEE11111111E1E1EEEE1E1E1EEE1EE11E1EEE", 0, -1),
    ("1111111111EEE1EE11EEE1EE11EEE1EE11EE1EE", 4, 0), ("11111111EEE1EE11EE1EEE11E1E1EEE11EE", -3, 0),
    ("1111111E1EEEE11EEE11E1E1EEE11EE", -mpf(3) / 2, 0),
    ("1111111E1EEEE11EEE1EE11111111EEE1EE11EEE1EE11EE1EE1EE", -4, 0),
]


def self_test():
    bad = [w for w, tre, tk in SELF_TEST if decide(w, tre, tk)[0] is True]
    print(f"self-test: {len(SELF_TEST) - len(bad)}/{len(SELF_TEST)} known words not excluded for their own value")
    for w in bad:
        print(f"   UNSOUND: excluded {w}")
    return not bad


def main():
    if not self_test():
        sys.exit(2)
    if len(sys.argv) > 1 and sys.argv[1] == "--open":
        # Records the README calls shortest known: +i*pi on this cut at K 21 (K 23 without
        # ln 0), and -2 at K 25 (K 27 without ln 0).
        ok = prove("+i*pi", 0, 1, 19)
        ok = only_ln0("+i*pi", 0, 1, 21) and ok
        ok = prove("-2", -2, 0, 23) and ok
        ok = only_ln0("-2", -2, 0, 25) and ok
        sys.exit(0 if ok else 1)
    max_k = int(sys.argv[1]) if len(sys.argv) > 1 else 17
    words = []
    for n in range(1, (max_k + 1) // 2 + 1):
        words += programs(n)
    print(f"{len(words)} programs with K <= {max_k}")
    ok = True
    for label, tre, upto in CLAIMS:
        undecided, equal, checked = [], [], 0
        for w in words:
            if len(w) > upto:
                continue
            checked += 1
            verdict, reason = decide(w, tre)
            if verdict is None:
                undecided.append((w, reason))
            elif verdict is False:
                equal.append(w)
        status = "PROVED" if not undecided and not equal else "NOT PROVED"
        ok = ok and status == "PROVED"
        print(f"{label}: no program with K <= {upto} equals {label}: {status}  ({checked} programs, {len(equal)} not excluded, {len(undecided)} undecided)")
        for w in equal[:10]:
            print(f"   not excluded: {w}")
        for w, r in undecided[:12]:
            print(f"   undecided: {w}  ({r})")
    k15 = [w for w in words if len(w) == 15]
    hits = [(w,) + decide(w, -1) for w in k15]
    hits = [h for h in hits if h[1] is not True]
    strict = [h for h in hits if not uses_ln0(h[0])]
    print(f"-1 at K 15: {len(hits)} programs not excluded, {len(strict)} of them without ln 0 (claim: only ln 0 words)")
    for h in hits[:10]:
        print(f"   {h[0]}  ln0={uses_ln0(h[0])}  {'undecided: ' + h[2] if h[1] is None else 'not excluded'}")
    ok = ok and not strict
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
