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
retried at higher precision, and then by towers.py, a second decider with an exact
combination layer and tower enclosures that carry their phase (see its docstring),
before they are reported. Programs whose value depends on the phase of a tower such as
exp(T4 / z), and so on every digit of T4 = e^(e^(e^e)), are decided only with deep.py,
which gives towers.py that phase at up to 5.5 million bits.

usage: python decide.py [max_K]       the claims in docs/minimality.md (default 17)
       python decide.py --open        +i*pi at K 21 and K 23 without ln 0, -2 at K 25 and
                                      K 27 without ln 0
       python decide.py --open --deep the same, with deep.py for the programs left open
       python decide.py --word WORD --upto K --expect NAME [--strict] [--witness WORD]
                                      WORD is the target. --expect is required.
                                      Exclude every program with K <= upto. --strict
                                      allows a hit that takes ln 0. NAME is ln2, -e,
                                      1/e, e+1, e^2, 2, ipi, or -2, and the witness has
                                      to be that constant. A missing phase of exp(e^W)
                                      is used only when arb's cos of it is strictly signed.
"""
import sys
import time
from mpmath import iv, mpf

import towers

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

    __slots__ = ("kind", "re", "im", "k", "s", "L", "sym", "prov", "lin", "off", "off_bound", "lm")

    def __init__(self, kind, sym, re=None, im=None, k=None, s=None, L=None, prov=None, lin=None):
        self.kind, self.sym, self.re, self.im, self.k, self.s, self.L, self.prov = kind, sym, re, im, k, s, L, prov
        # A finite value's form as an integer combination of atoms ("1", "exp(..)", "ln(..)").
        self.lin = lin if lin is not None else {sym: 1}
        # off: the value is its form plus a nonzero perturbation delta of this sign,
        # rigorously bounded by |delta| <= off_bound (an iv-rounded upper bound mpf).
        self.off = None
        self.off_bound = None
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


def eff_off_bound(v):
    if v.kind == "small":
        return iv.exp(-iv.mpf(LIMIT)).b
    return v.off_bound


def add_bounds(b1, b2):
    if b1 is None:
        return b2
    if b2 is None:
        return b1
    return (iv.mpf(b1) + iv.mpf(b2)).b


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
        # Docstring contract: bigk is excluded and never reused; delegate to towers.py.
        raise Undecided("exp of a tower with a phase")
    if v.kind == "huge":
        raise Undecided("exp of a huge value")
    if v.kind == "fin" and v.k is None and v.re.a > LIMIT:
        return huge(sym, v.re.a)  # |exp(L + i theta)| = exp(L)
    if v.kind == "fin" and v.prov and v.prov[0] == "nudge" and v.prov[1] == 0 and v.k is not None:
        # exp(k*pi*i + delta) = (-1)^k e^delta: |e^delta - 1| <= 2*|delta| for |delta| <= 1/2.
        b = v.off_bound
        if b is None or b > mpf("0.25"):
            raise Undecided("exp of unbounded nudge")
        sign = 1 if v.k % 2 == 0 else -1
        rad = (2 * iv.mpf(b)).b
        d = iv.mpf([-rad, rad])
        out = V("fin", sym + "~", iv.mpf(sign) + d, iv.mpf(0), 0, prov=("nudge", mpf(sign), sign * v.prov[2]), lin={"1": sign})
        out.off = sign * v.prov[2]
        out.off_bound = rad
        return out
    if v.kind == "fin" and v.k is not None and v.off in (1, -1) and v.re.b < LIMIT and v.re.a > -LIMIT:
        # exp(X + k*pi*i + delta) = (-1)^k exp(X) (1 + O(delta)); check magnified bound rigorously.
        b = v.off_bound
        if b is not None and b <= mpf("0.25"):
            mag_err = (2 * iv.exp(iv.mpf(v.re.b)) * iv.mpf(b)).b
            if mag_err <= mpf("0.25"):
                xlin = {a: c for a, c in v.lin.items() if a != "ipi"}
                X = V("fin", key_of(xlin), v.re, iv.mpf(0), 0, lin=xlin)
                atom = f"exp({X.sym})"
                EXP_ARG.setdefault(atom, X)
                sign = 1 if v.k % 2 == 0 else -1
                out = V("fin", tag(atom if sign == 1 else f"-{atom}", sign * v.off), iv.exp(v.re) * sign, iv.mpf(0), 0, lin={atom: sign})
                out.off = sign * v.off
                out.off_bound = mag_err
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
        rad = (2 * iv.exp(-iv.mpf(LIMIT))).b
        d = iv.mpf([-rad, rad])
        return V("fin", sym, 1 + d, iv.mpf(0), 0, prov=("exp", v))
    re, im, k = v.re, v.im, v.k
    sign = None if k is None else (1 if k % 2 == 0 else -1)
    if re.a > LIMIT:
        if sign is None:
            raise Undecided("tower with a phase")
        xlin = {a: c for a, c in v.lin.items() if a != "ipi"} if k else dict(v.lin)
        L = V("fin", key_of(xlin), re, iv.mpf(0), 0, lin=xlin)
        L.off, L.off_bound = v.off, v.off_bound
        return V("big", sym, s=sign, L=L, prov=("exp", v))
    if re.b < -LIMIT:
        if sign is None:
            raise Undecided("tiny value with a phase")
        xlin = {a: -c for a, c in v.lin.items() if a != "ipi"} if k else {a: -c for a, c in v.lin.items()}
        L = V("fin", key_of(xlin), -re, iv.mpf(0), 0, lin=xlin)
        L.off, L.off_bound = neg_off(v.off), v.off_bound
        return V("small", sym, s=sign, L=L, prov=("exp", v))
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
        raise Undecided("log of a tower with a phase")
    if v.prov and v.prov[0] == "exp" and real(v.prov[1]) and v.off is None:
        return v.prov[1]  # ln(exp x) = x for a real x
    atom = single_atom(v)
    if atom in EXP_ARG and real(EXP_ARG[atom]):
        return EXP_ARG[atom]  # ln(exp x) = x for a real x
    if v.kind == "fin" and v.prov and v.prov[0] == "nudge" and v.prov[1] in (1, -1) and v.k == 0:
        # ln(c + delta) with c = +-1: |ln(1 +- delta)| <= 2*|delta| for |delta| <= 1/2.
        b = v.off_bound
        if b is None or b > mpf("0.25"):
            raise Undecided("log of unbounded nudge")
        c, sgn = v.prov[1], v.prov[2]
        k = 0 if c > 0 else -1
        off = sgn * (1 if c > 0 else -1)
        rad = (2 * iv.mpf(b)).b
        d = iv.mpf([-rad, rad])
        out = V("fin", tag(f"ln({c})", off), d, iv.pi * k, k, prov=("nudge", mpf(0), off), lin=({"ipi": k} if k else {}))
        out.off = off
        out.off_bound = rad
        return out
    if v.kind == "fin" and v.k == 0 and len(v.lin) == 1 and v.off in (1, -1) and v.off_bound is not None:
        (atom, c), = v.lin.items()
        X = EXP_ARG.get(atom)
        if X is not None and X.kind == "fin" and X.k == 0 and c in (1, -1) and X.off is None and X.re.a > -LIMIT:
            # ln(c*exp(X) + delta) = X + ln(1 + c*delta*e^-X) (- i*pi when c = -1).
            # Verify |delta|*e^-X <= 1/4 so the sign and branch cut cannot flip.
            rel = (iv.mpf(v.off_bound) * iv.exp(-iv.mpf(X.re.a))).b
            if rel <= mpf("0.25"):
                off = c * v.off
                rad = (2 * iv.mpf(rel)).b
                d = iv.mpf([-rad, rad])
                lin = dict(X.lin)
                if c == -1:
                    lin["ipi"] = lin.get("ipi", 0) - 1
                out = V("fin", tag(key_of(lin), off), X.re + d, iv.mpf(0) if c == 1 else -iv.pi, 0 if c == 1 else -1, lin=lin)
                out.off = off
                out.off_bound = rad
                return out
    if v.off is not None and v.prov and v.prov[0] == "exp":
        pass  # the provenance rewrite below would drop the offset
    if v.kind == "fin" and v.lin == {"1": 1} and v.off is None:
        return zero()
    if v.kind == "nan":
        return v
    if v.sym == "1" and v.off is None:
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
            out.off_bound = L.off_bound
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
    """An upper bound on ln|v| for a fin value computed in outward iv arithmetic."""
    return iv.log(abs(v.re) + abs(v.im) + 1).b


def widen(L, rel):
    """L + [-rel, rel] for a real V L (rel an mpf). Never silently drop perturbations on big towers."""
    if L.kind == "fin":
        return V("fin", L.sym + "~", L.re + iv.mpf([-rel, rel]), iv.mpf(0), 0)
    raise Undecided("perturbation of a tower of towers")


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
        oa, ob = eff_off(a), eff_off(b)
        obound = add_bounds(eff_off_bound(a), eff_off_bound(b))
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
            if obound is not None:
                d = iv.mpf([-obound, obound])
                if net is None:
                    out = V("fin", key_of(lin) + "~", iv.mpf(c) + d, iv.pi * kpi, kpi)
                    out.off_bound = obound
                    return out
                out = V("fin", key_of(lin) + "~", iv.mpf(c) + d, iv.pi * kpi, kpi, prov=("nudge", mpf(c), net))
                out.off_bound = obound
                return out
        sym = key_of(lin)
    else:
        lin = None
    # towers and tiny values beside finite ones
    if a.kind == "huge" or b.kind == "huge":
        h, f = (a, b) if a.kind == "huge" else (b, a)
        if f.kind != "fin":
            raise Undecided("huge value beside a non-finite one")
        if h.lm is None:
            return huge(sym, None)
        if (iv.mpf(h.lm) - iv.mpf(magnitude_log(f))).a >= 100:
            return huge(sym, (iv.mpf(h.lm) - 1).a)
        raise Undecided("huge value beside a comparable one")
    if a.kind == "big" and b.kind == "fin" and b.k is None:
        lm = tower_lm(a.L)
        if lm is None:
            return huge(sym, None)
        if (iv.mpf(lm) - iv.mpf(magnitude_log(b))).a >= 100:
            return huge(sym, (iv.mpf(lm) - 1).a)
        raise Undecided("tower beside a comparable value")
    if b.kind == "big" and a.kind == "fin" and a.k is None:
        lm = tower_lm(b.L)
        if lm is None:
            return huge(sym, None)
        if (iv.mpf(lm) - iv.mpf(magnitude_log(a))).a >= 100:
            return huge(sym, (iv.mpf(lm) - 1).a)
        raise Undecided("tower beside a comparable value")
    if a.kind == "bigk" or b.kind == "bigk":
        raise Undecided("tower with a phase in a sum")
    if a.kind == "big" and b.kind == "fin" and b.k not in (0, None):
        gap = (iv.mpf(a.L.re.a) - iv.mpf(magnitude_log(b))).a if a.L.kind == "fin" else LIMIT
        if gap < 100:
            raise Undecided("tower beside a comparable value")
        return V("bigk", sym, s=a.s, L=a.L, k=-b.k)  # exp(L) - (c + k*pi*i): excluded, never reused
    if a.kind in ("big", "small") or b.kind in ("big", "small"):
        if a.kind == "big" and b.kind in ("fin", "small"):
            if b.kind == "fin" and b.k not in (0,):
                raise Undecided("tower minus a complex value")
            bound = 0 if b.kind == "small" else magnitude_log(b)
            gap = (iv.mpf(a.L.re.a) - iv.mpf(bound)).a if a.L.kind == "fin" else LIMIT
            if gap < 100:
                raise Undecided("tower beside a comparable value")
            rel = (2 * iv.exp(-iv.mpf(gap))).b
            L2 = widen(a.L, rel)
            # s*exp(L) - c = s*exp(L + ln(1 - c*s*e^-L)): delta has the sign of -c*s.
            csign = (1 if b.re.a > 0 else -1 if b.re.b < 0 else 0) if b.kind == "fin" else b.s
            if L2.kind == "fin" and csign != 0:
                L2.lin = dict(a.L.lin)
                d = -csign * a.s
                L2.off = d if a.L.off in (None, d) else "mixed"
                L2.off_bound = add_bounds(a.L.off_bound, rel)
            return V("big", sym, s=a.s, L=L2)
        if b.kind == "big" and a.kind in ("fin", "small"):
            if a.kind == "fin" and a.k not in (0,):
                raise Undecided("complex value minus a tower")
            bound = 0 if a.kind == "small" else magnitude_log(a)
            gap = (iv.mpf(b.L.re.a) - iv.mpf(bound)).a if b.L.kind == "fin" else LIMIT
            if gap < 100:
                raise Undecided("tower beside a comparable value")
            rel = (2 * iv.exp(-iv.mpf(gap))).b
            L2 = widen(b.L, rel)
            # c - s*exp(L) = -s*exp(L + ln(1 - c*s*e^-L)): delta has the sign of -c*s.
            csign = (1 if a.re.a > 0 else -1 if a.re.b < 0 else 0) if a.kind == "fin" else a.s
            if L2.kind == "fin" and csign != 0:
                L2.lin = dict(b.L.lin)
                d = -csign * b.s
                L2.off = d if b.L.off in (None, d) else "mixed"
                L2.off_bound = add_bounds(b.L.off_bound, rel)
            return V("big", sym, s=-b.s, L=L2)
        if a.kind == "small" and b.kind == "fin":
            rad = iv.exp(-iv.mpf(LIMIT)).b
            d = iv.mpf([-rad, rad])
            k = None if b.k is None else -b.k
            nudge = ("nudge", -b.re.a, a.s) if b.k == 0 and b.re.a == b.re.b else None
            out = V("fin", sym, -b.re + d, -b.im, k, prov=nudge)
            out.off_bound = add_bounds(rad, b.off_bound)
            return out
        if b.kind == "small" and a.kind == "fin":
            rad = iv.exp(-iv.mpf(LIMIT)).b
            d = iv.mpf([-rad, rad])
            nudge = ("nudge", a.re.a, -b.s) if a.k == 0 and a.re.a == a.re.b else None
            out = V("fin", sym, a.re + d, a.im, a.k, prov=nudge)
            out.off_bound = add_bounds(a.off_bound, rad)
            return out
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
        out.off_bound = add_bounds(eff_off_bound(a), eff_off_bound(b))
        out.sym = tag(key_of(lin), out.off)
    return out


def eml(x, y):
    return sub(cexp(x), clog(y))


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
    saved = iv.prec
    iv.prec = 128
    EXP_ARG.clear()
    LN_ARG.clear()
    try:
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
    finally:
        iv.prec = saved


def decide(word, tre, tk=0):
    k = (word, tre, tk)
    if k not in VERDICT:
        VERDICT[k] = decide_once(word, tre, tk)
    return VERDICT[k]


def decide_once(word, tre, tk=0):
    reason = None
    for bits in (128, 1024, 8192):
        iv.prec = bits
        EXP_ARG.clear()
        LN_ARG.clear()
        try:
            return excludes(evaluate(word), tre, tk), None
        except Undecided as why:
            reason = str(why)
    verdict, why = towers.decide(word, tre, tk)
    if verdict is not None:
        STATS["towers"] += 1
        return verdict, None
    return None, f"{reason}; towers.py: {why}"


_TARGET_BOX = {}


def target_enclosure(target_word, bits):
    """Outward enclosure of an EML word at this precision, or None if the pass cannot build one."""
    key = (target_word, bits)
    if key in _TARGET_BOX:
        return _TARGET_BOX[key]
    saved = iv.prec
    iv.prec = bits
    EXP_ARG.clear()
    LN_ARG.clear()
    try:
        _TARGET_BOX[key] = evaluate(target_word)
    except Undecided:
        _TARGET_BOX[key] = None
    finally:
        iv.prec = saved
    return _TARGET_BOX[key]


def modest_finite(box):
    """A finite enclosure inside (-10^6, 10^6) on both axes."""
    if box is None or box.kind != "fin" or box.re is None or box.im is None:
        return False
    bound = mpf(10) ** 6
    return box.re.a > -bound and box.re.b < bound and box.im.a > -bound and box.im.b < bound


def excludes_against_box(v, box):
    """True when v's enclosure is disjoint from a modest finite target enclosure.

    Rectangles are outward, so a miss is certain. A real tower past exp(10^6), an
    infinity, or a value below exp(-10^6) is disjoint from that box too.
    """
    if not modest_finite(box):
        return False
    if v.kind in ("nan", "inf", "big", "bigk", "huge"):
        return True
    if v.kind == "small":
        try:
            rad = iv.exp(-iv.mpf(LIMIT)).b
        except (OverflowError, ValueError):
            return False
        if box.re.a > rad or box.re.b < -rad or box.im.a > rad or box.im.b < -rad:
            return True
        return False
    if v.kind != "fin" or v.re is None or v.im is None:
        return False
    if box.re.b < v.re.a or box.re.a > v.re.b:
        return True
    if box.im.b < v.im.a or box.im.a > v.im.b:
        return True
    return False


def decide_word_once(word, target_word):
    """Interval separation, then towers.decide_word in one shared reset() scope."""
    reason = None
    for bits in (128, 1024):
        iv.prec = bits
        EXP_ARG.clear()
        LN_ARG.clear()
        box = target_enclosure(target_word, bits)
        try:
            v = evaluate(word)
        except Undecided as why:
            # A structural refusal (a tower the interval layer will not follow)
            # does not get cheaper at more bits; 1024-bit iv.exp on it can run
            # for minutes. The exact layer is the next step.
            reason = str(why)
            break
        if excludes_against_box(v, box):
            return True, None
        reason = "interval overlaps the target"
        if not (v.kind == "fin" and box is not None and box.kind == "fin"):
            break
    verdict, why = towers.decide_word(word, target_word)
    if verdict is not None:
        STATS["towers"] += 1
        return verdict, None
    return None, f"{reason}; towers.py: {why}"


def decide_word(word, target_word):
    k = ("W", word, target_word)
    if k not in VERDICT:
        VERDICT[k] = decide_word_once(word, target_word)
    return VERDICT[k]


def signed_phase(word):
    """towers.PHASE: Im(word) mod 2*pi, or None unless arb's cos of it is strictly signed.

    For a value ±exp(e^W) whose only gap is θ = Im W mod 2*pi, a positive cos makes
    the value huge and excludes a modest target, and a negative cos makes it tiny and
    excludes a nonzero target. An enclosure of cos that is not strictly signed is not
    a phase: the word stays undecided.

    The per-word alarm stays off for the call. A phase is a shared multi-minute arb
    computation, and killing it would leave the word undecided and (before the lock
    was dropped) cache that failure for every other worker.
    """
    import signal
    import deep
    remaining = signal.alarm(0)
    try:
        th = deep.phase(word)
    finally:
        if remaining:
            signal.alarm(remaining)
    if th is None or deep.arb_cos_sign(th) is None:
        return None
    return th


def _form(build):
    """Exact towers form from build(), with the phase oracle off."""
    saved = towers.PHASE
    towers.PHASE = None
    towers.reset()
    try:
        return build()
    finally:
        towers.PHASE = saved


def canonical_form(name):
    """The exact-layer form of a named constant, built from 1, exp and ln, not from a word."""
    if name == "ln 2":
        return _form(lambda: towers.ln_single("1", 2))
    if name == "-e":
        return _form(lambda: {a: -c for a, c in towers.mk_exp({"1": 1}).items()})
    if name == "1/e":
        return _form(lambda: towers.mk_exp({"1": -1}))
    if name == "e + 1":
        def e1():
            e = towers.mk_exp({"1": 1})
            e["1"] = e.get("1", 0) + 1
            return e
        return _form(e1)
    if name == "e^2":
        return _form(lambda: towers.mk_exp({"1": 2}))
    if name == "2":
        return {"1": 2}
    if name == "+iπ":
        return {"ipi": 1}
    if name == "-2":
        return {"1": -2}
    raise KeyError(name)


NAMED = ("ln 2", "-e", "1/e", "e + 1", "e^2", "2", "+iπ", "-2")

# Tokens for --expect. Each one is a constant built above, not a word.
EXPECT = {
    "ln2": "ln 2",
    "-e": "-e",
    "1/e": "1/e",
    "e+1": "e + 1",
    "e^2": "e^2",
    "2": "2",
    "ipi": "+iπ",
    "-2": "-2",
}

def _program_counts(max_leaves=13):
    """Cumulative counts through K = 2*leaves - 1, from the Catalan recurrence.

    programs(n) has length C_{n-1}. An even bound adds no programs, so K and K+1
    share a total. Checked against programs() through K 25 (290512).
    """
    c = 1
    total = 0
    counts = {}
    for n in range(max_leaves):
        total += c
        k = 2 * (n + 1) - 1
        counts[k] = total
        counts[k + 1] = total
        c = c * (4 * n + 2) // (n + 2)
    return counts


# Every K <= 26. A scan at any other K refuses to print PROVED.
PROGRAM_COUNTS = _program_counts()


def constant_name(word):
    """Which named constant word's exact form is, or None."""
    got = _form(lambda: towers._eval(word))
    if not isinstance(got, dict):
        return None
    for name in NAMED:
        if got == canonical_form(name):
            return name
    return None


STATS = {"towers": 0, "deep": 0}
VERDICT = {}    # (word, tre, tk) -> (verdict, reason)
PENDING = []    # undecided programs whose verdict a claim needs, for deep.py
QUIET = False


def run_deep():
    """Retry PENDING with deep.py's phase oracle (in parallel) and record the verdicts."""
    import deep
    jobs = [j for j in dict.fromkeys(PENDING) if VERDICT[j][0] is None]
    print(f"deep.py: {len(jobs)} programs left open go to towers.py with deep.py's phases", flush=True)
    for j, (verdict, why) in deep.run(jobs).items():
        if verdict is not None:
            STATS["deep"] += 1
            VERDICT[j] = (verdict, None)
        else:
            VERDICT[j] = (None, f"{VERDICT[j][1]}; with deep.py: {why}")


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
                PENDING.append((w, tre, tk))
            elif verdict is False:
                equal.append(w)
    status = "PROVED" if not undecided and not equal else "NOT PROVED"
    if QUIET:
        return status == "PROVED"
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
    PENDING.extend((w, tre, tk) for w, verdict, _ in strict if verdict is None)
    status = "PROVED" if not strict else "NOT PROVED"
    if QUIET:
        return not strict
    print(f"{label} without ln 0 needs more than K {k}: {status}  ({len(left)} K {k} programs not excluded, {len(strict)} of them without ln 0)", flush=True)
    for w, verdict, reason in strict[:20]:
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


def word_target_test():
    """Word targets agree with an exact numeric target, and decide a value a float cannot.

    2 is an integer coefficient of the atom 1, so both forms apply. e is not: a rounded
    point sits outside the enclosure of exp(1), and towers.decide then excludes the word
    that is e. The word target cancels that atom exactly. The reset between the two
    evaluations is the KeyError the snapshot exists for: ATOMS loses E[1*1] until
    restore_scope registers it again with the enclosure from the target.
    """
    from mpmath import exp as mexp
    two = "111111EEE1EE11EE1EE"
    e = "11E"
    also_e = "11111EE1EEE"  # another word whose exact form is exp(1)
    bad = []
    for prog in ("1", e, two):
        num = decide(prog, 2)[0]
        word = decide_word(prog, two)[0]
        tnum = towers.decide(prog, 2, 0)[0]
        tword = towers.decide_word(prog, two)[0]
        if len({num, word, tnum, tword}) != 1:
            bad.append(f"{prog}: decide {num}, word {word}, towers {tnum}, towers-word {tword}")
    if decide_word(also_e, e)[0] is not False or towers.decide_word(also_e, e)[0] is not False:
        bad.append(f"word target did not accept {also_e} as e")
    if towers.decide(also_e, mexp(1), 0)[0] is False:
        bad.append("numeric approximation of e reported equality")
    if decide_word("1", e)[0] is not True:
        bad.append("word target did not exclude 1 as e")
    iv.prec = 128
    towers.reset()
    target = towers._eval(e)
    atoms, lnof = towers.scope_snapshot()
    towers.reset()
    if "E[1*1]" in towers.ATOMS:
        bad.append("reset did not drop the target atom")
    towers.restore_scope(atoms, lnof)
    info = towers.ATOMS.get("E[1*1]")
    if info is None or info.get("A") is None:
        bad.append("restore did not register the target atom with its enclosure")
    else:
        value = towers._eval(also_e)
        towers.restore_scope(atoms, lnof)
        try:
            if towers.excludes_value(value, target) is not False:
                bad.append("restored target atom did not cancel the other word for e")
        except (towers.Undecided, KeyError) as why:
            bad.append(f"restored comparison failed: {why}")
        towers.reset()
        towers.restore_scope(atoms, lnof)
        one = towers._eval("1")
        towers.restore_scope(atoms, lnof)
        try:
            if towers.excludes_value(one, target) is not True:
                bad.append("restored target atom did not exclude 1")
        except (towers.Undecided, KeyError) as why:
            bad.append(f"restored exclusion failed: {why}")
    hard = "11E1E1111E1E1EEEE1E1E1E"
    ln2 = "11111111EEE1EE11EE1EEE1EE"
    saved_phase = towers.PHASE
    towers.PHASE = None
    verdict, why = towers.decide_word(hard, ln2)
    if verdict is False or (verdict is None and why and "KeyError" in why):
        bad.append(f"T4-phase word against ln 2: {verdict} {why}")
    named = {
        ln2: "ln 2",
        "11111E1EEEE11E1EE": "-e",
        "1111E11E1EEE1EE11E1E1EE": "-e",
        "11111E1EEEE11EE1E": "1/e",
        "11111EEE1EE11E1EE1E": "1/e",
        "111111E1EEEE11EE1EE": "e + 1",
        "111111EEE1EE11E1EE1EE": "e + 1",
        "111111EEE1EE11EE1EE1E": "e^2",
        "111111EEE1EE11EE1EE": "2",
        "111111E1EEEE11E1E1EEE": "+iπ",
        "111111E1E1EEE1EE11E1EEE": "+iπ",
        "111111E1EEEE11E1E1EEE11EE": "-2",
    }
    for word, name in named.items():
        got = constant_name(word)
        if got != name:
            bad.append(f"{word} is {got}, not {name}")
    if constant_name("1") is not None:
        bad.append("the word 1 was accepted as a named constant")
    import io
    import contextlib
    held = io.StringIO()
    with contextlib.redirect_stdout(held):
        pinned = prove_word("swap", "11111E1EEEE11E1EE", 15, expect="ln 2")
    if pinned or "witness is -e, not ln 2" not in held.getvalue():
        bad.append("a -e word passed --expect ln 2")
    if PROGRAM_COUNTS.get(13) != 197 or PROGRAM_COUNTS.get(16) != 626 or PROGRAM_COUNTS.get(25) != 290512:
        bad.append("program-count table does not match the Catalan totals")
    distinct = [str(i) for i in range(626)]
    try:
        require_program_count(15, distinct[:625])
    except AssertionError:
        pass
    else:
        bad.append("a short K <= 15 count was accepted")
    try:
        require_program_count(16, distinct[:625])
    except AssertionError:
        pass
    else:
        bad.append("K <= 16 with a dropped program was accepted")
    try:
        require_program_count(15, distinct[:625] + ["0"])
    except AssertionError:
        pass
    else:
        bad.append("a duplicate program was accepted")
    try:
        require_program_count(15, distinct)
    except AssertionError as why:
        bad.append(f"626 distinct programs raised: {why}")
    try:
        require_program_count(27, ["only"])
    except AssertionError:
        pass
    else:
        bad.append("K <= 27 with no count check was accepted")
    import deep
    iv.prec = 128
    got = deep.exp_iv(iv.mpf("-2.5"), 128)
    ref = iv.exp(iv.mpf("-2.5"))
    if not (got.a <= ref.a and got.b >= ref.b):
        bad.append("arb exp missed exp(-2.5)")
    span = iv.mpf(["2", "3"])
    logged = deep.log_iv(span)
    ref = iv.log(span)
    if not (logged.a <= ref.a and logged.b >= ref.b):
        bad.append("arb log missed log([2, 3])")
    slope = iv.mpf(["-2", "0.5"])
    at = deep.atan_iv(slope)
    ref = iv.atan2(slope, iv.mpf(1))
    if not (at.a <= ref.a and at.b >= ref.b):
        bad.append("arb atan missed atan([-2, 0.5])")
    hump = iv.mpf(["-0.1", "0.1"])
    covered = deep._range_iv("cos", hump, 128)
    ref = iv.cos(hump)
    if not (covered.a <= ref.a and covered.b >= ref.b and covered.a <= 1 <= covered.b):
        bad.append("arb cos of an interval around 0 missed the maximum")
    positive = iv.mpf(["-5.395310643879352", "-5.395310643879351"])
    negative = iv.mpf(["3.141592653589793", "3.141592653589794"])
    straddle = iv.mpf(["1.0", "2.0"])
    if deep.arb_cos_sign(positive) != 1 or deep.arb_cos_sign(negative) != -1 or deep.arb_cos_sign(straddle) is not None:
        bad.append("arb cos sign is not strict exactly when the enclosure is")
    w_of = "11E1E1111E1E1EEEE1E"
    towers.PHASE = lambda word: positive if word == w_of else None
    try:
        if towers.excludes_word(hard, ln2) is not True:
            bad.append("strictly positive cos did not exclude ln 2")
    except towers.Undecided as why:
        bad.append(f"strictly positive cos stayed undecided: {why}")
    towers.PHASE = lambda word: straddle if word == w_of else None
    try:
        bad.append(f"unsigned cos decided ln 2: {towers.excludes_word(hard, ln2)}")
    except towers.Undecided:
        pass
    towers.PHASE = None
    if signed_phase("11E1E1111E1E1EEEE1E1E") is not None:
        bad.append("phase of exp(W) should be refused")
    towers.PHASE = saved_phase
    print(f"word-target: {'ok' if not bad else 'FAILED'}  ({len(bad)} problems)")
    for line in bad:
        print(f"   {line}")
    return not bad


def self_test():
    bad = [w for w, tre, tk in SELF_TEST if decide(w, tre, tk)[0] is True]
    bad += [w for w, tre, tk in SELF_TEST if towers.decide(w, tre, tk)[0] is True and w not in bad]
    if "--deep" in sys.argv:  # and with deep.py's phases
        import deep
        towers.PHASE = deep.phase
        bad += [w for w, tre, tk in SELF_TEST if towers.decide(w, tre, tk)[0] is True and w not in bad]
        towers.PHASE = None
    print(f"self-test: {len(SELF_TEST) - len(bad)}/{len(SELF_TEST)} known words not excluded for their own value")
    for w in bad:
        print(f"   UNSOUND: excluded {w}")
    return word_target_test() and not bad


class _Alarm(Exception):
    pass


def _on_alarm(signum, frame):
    raise _Alarm()


def _word_batch(payload):
    """Exclude a batch of programs. Returns the ones that are not certainly excluded.

    The pool does not inherit the parent's globals when the start method is spawn
    or forkserver, which is what the CI runner uses. The phase oracle and the
    shared-exp directory are installed in this process.
    """
    import signal
    import deep
    target_word, words, strict, share = payload
    deep.SHARE = share
    towers.PHASE = signed_phase
    signal.signal(signal.SIGALRM, _on_alarm)
    bad = []
    before = STATS["towers"]
    seen = 0
    for w in words:
        seen += 1
        signal.alarm(1200)
        try:
            verdict, reason = decide_word(w, target_word)
            if verdict is not True and not (strict and uses_ln0(w) is True):
                bad.append((w, verdict, reason))
        except _Alarm:
            bad.append((w, None, "timeout"))
        finally:
            signal.alarm(0)
    return bad, STATS["towers"] - before, seen


def require_program_count(upto, words):
    """Fail unless this K has its Catalan total, and the programs are distinct."""
    n = len(words)
    if upto not in PROGRAM_COUNTS:
        raise AssertionError(f"K <= {upto}: no program-count check, refusing to prove")
    if n != PROGRAM_COUNTS[upto]:
        raise AssertionError(
            f"K <= {upto}: counted {n} programs, expected {PROGRAM_COUNTS[upto]}"
        )
    distinct = len(set(words))
    if distinct != n:
        raise AssertionError(
            f"K <= {upto}: {n} programs, only {distinct} distinct"
        )


def prove_word(label, target_word, upto, strict=False, witness=None, expect=None):
    """Exclude every program with K <= upto. With strict, a program that takes ln 0 may hit.

    expect is the named constant the witness has to be. Returns True when nothing
    undecided and no counterexample remains.
    """
    import os
    import concurrent.futures
    import multiprocessing
    wit = witness if witness is not None else target_word
    name = constant_name(wit)
    if name is None:
        print(f"{label}: witness is not a named constant", flush=True)
        return False
    if expect is not None and name != expect:
        print(f"{label}: witness is {name}, not {expect}", flush=True)
        return False
    if witness is not None and constant_name(target_word) != name:
        print(f"{label}: target word is not {name}", flush=True)
        return False
    print(f"{label}: witness equals {name}", flush=True)
    if strict and uses_ln0(wit) is True:
        print(f"{label}: strict witness takes ln 0", flush=True)
        return False
    words = []
    for n in range(1, (upto + 1) // 2 + 1):
        words.extend(programs(n))
    batches = [words[i:i + 400] for i in range(0, len(words), 400)]
    require_program_count(upto, words)
    print(f"{label}: {len(words)} programs with K <= {upto}", flush=True)
    bad = []
    towers_n = 0
    scanned = 0
    import tempfile
    import shutil
    import deep
    share = tempfile.mkdtemp(prefix="eml-phase-")
    payloads = [(target_word, batch, strict, share) for batch in batches]
    saved_share, deep.SHARE = deep.SHARE, share
    saved_phase = towers.PHASE
    towers.PHASE = signed_phase
    try:
        if len(words) >= 800:
            workers = os.cpu_count() or 2
            # forkserver, not fork: a worker must not inherit a half-mutated parent,
            # and Python 3.14 (the CI runner) no longer forks by default.
            ctx = multiprocessing.get_context("forkserver")
            with concurrent.futures.ProcessPoolExecutor(max_workers=workers, mp_context=ctx) as pool:
                futures = [pool.submit(_word_batch, payload) for payload in payloads]
                done = 0
                for fut in concurrent.futures.as_completed(futures):
                    found, n, seen = fut.result()
                    bad.extend(found)
                    towers_n += n
                    scanned += seen
                    done += 1
                    if done % 10 == 0 or done == len(futures):
                        print(f"   {done}/{len(futures)} batches, {len(bad)} open", flush=True)
        else:
            for payload in payloads:
                found, _n, seen = _word_batch(payload)
                bad.extend(found)
                scanned += seen
    finally:
        towers.PHASE = saved_phase
        deep.SHARE = saved_share
        shutil.rmtree(share, ignore_errors=True)
    if scanned != len(words):
        raise AssertionError(
            f"{label}: workers scanned {scanned} programs, not {len(words)}"
        )
    if len(words) >= 800:
        STATS["towers"] += towers_n
    equal = [w for w, verdict, _ in bad if verdict is False]
    undecided = [(w, reason) for w, verdict, reason in bad if verdict is not False]
    status = "PROVED" if not equal and not undecided else "NOT PROVED"
    print(f"{label}: {status}  ({len(words)} programs, {len(equal)} not excluded, {len(undecided)} undecided)", flush=True)
    for w in equal[:10]:
        print(f"   not excluded: {w}")
    for w, reason in undecided[:12]:
        print(f"   undecided: {w}  ({reason})")
    return status == "PROVED"


def main():
    if not self_test():
        sys.exit(2)
    args = sys.argv[1:]
    if "--expect" in args:
        at = args.index("--expect")
        if at + 1 >= len(args) or args[at + 1].startswith("--"):
            print("usage: --expect needs a value", flush=True)
            sys.exit(2)
    if "--word" in args:
        target = args[args.index("--word") + 1]
        upto = int(args[args.index("--upto") + 1]) if "--upto" in args else len(target) - 2
        witness = args[args.index("--witness") + 1] if "--witness" in args else None
        if "--expect" not in args:
            print("usage: --word requires --expect NAME", flush=True)
            sys.exit(2)
        token = args[args.index("--expect") + 1]
        expect = EXPECT.get(token)
        if expect is None:
            print(f"unknown --expect {token}", flush=True)
            sys.exit(1)
        t0 = time.time()
        ok = prove_word(target, target, upto, strict="--strict" in args, witness=witness, expect=expect)
        print(f"decided by towers.py: {STATS['towers']}  ({time.time() - t0:.0f} s)", flush=True)
        sys.exit(0 if ok else 1)
    if "--open" in args:
        # +i*pi on this cut at K 21 (K 23 without ln 0), and -2 at K 25 (K 27 without ln 0).
        global QUIET
        t0 = time.time()

        def claims():
            ok = prove("+i*pi", 0, 1, 19)
            ok = only_ln0("+i*pi", 0, 1, 21) and ok
            ok = prove("-2", -2, 0, 23) and ok
            return only_ln0("-2", -2, 0, 25) and ok
        if "--deep" in args:
            QUIET = True
            claims()
            print(f"first pass: {time.time() - t0:.0f} s", flush=True)
            run_deep()
            QUIET = False
        ok = claims()
        print(f"decided by towers.py: {STATS['towers']}, by deep.py: {STATS['deep']}  ({time.time() - t0:.0f} s)")
        sys.exit(0 if ok else 1)
    pos = [a for a in args if not a.startswith("--")]
    max_k = int(pos[0]) if pos else 17
    words = []
    for n in range(1, (max_k + 1) // 2 + 1):
        words += programs(n)
    print(f"{len(words)} programs with K <= {max_k}")
    ok = True
    for label, tre, upto in CLAIMS:
        if upto > max_k:
            print(f"{label}: skipped (needs K <= {upto}, ran max_k={max_k})")
            continue
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
    if max_k >= 15:
        k15 = [w for w in words if len(w) == 15]
        hits = [(w,) + decide(w, -1) for w in k15]
        hits = [h for h in hits if h[1] is not True]
        strict = [h for h in hits if uses_ln0(h[0]) is not True]
        print(f"-1 at K 15: {len(hits)} programs not excluded, {len(strict)} of them without ln 0 (claim: only ln 0 words)")
        for h in hits[:10]:
            print(f"   {h[0]}  ln0={uses_ln0(h[0])}  {'undecided: ' + h[2] if h[1] is None else 'not excluded'}")
        ok = ok and not strict
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
