"""Programs whose value turns on the phase of W = T4 / z, which needs 5.5 million bits.

T2 = e^e, T3 = e^T2, T4 = e^T3 (about 10^1656520), and z = e - ln(e - T2), which is
e - ln(T2 - e) + i*pi on the lower cut. The word 11E1E1111E1E1EEEE is T3 - ln z,
and exp(T3 - ln z) = T4 / z = W exactly. |W| is about
10^1656519 and Re W = T4 * Re(1/z) > 10^1656000 > 0, so the phase of exp(W),
theta = Im W mod 2*pi, depends on every digit of T4. This script encloses theta with
mpmath interval arithmetic at enough bits for Im W to keep about 200 bits after
the point, and then decides:

- 11E1E1111E1E1EEEE1E1E1E (K 23) is exp(exp(W)). It is -2 only if its modulus
  exp(Re exp(W)) = exp(e^(Re W) cos theta) is 2, that is cos theta = ln 2 * e^-(Re W),
  below 10^-1000. Excluded when |cos theta| > 10^-6.
- 111E1E1111E1E1EEEE1E1E1EE (K 25, no ln 0) is e - ln(exp(exp(W))). Whatever branch
  that ln takes, its real part is Re exp(W) = e^(Re W) cos theta, so the value has real
  part -2 only if cos theta = (e + 2) e^-(Re W). Excluded when |cos theta| > 10^-6.

usage: python deep.py   (5.5 million bits; about 90 minutes)
"""
import sys
import time
from mpmath import iv, mp, mpf, nstr
from mpmath.libmp import mpf_log, round_ceiling, round_floor

PRECISION = 5_503_000 + 256  # log2(T4) is about 5502820
K23 = "11E1E1111E1E1EEEE1E1E1E"
K25 = "111E1E1111E1E1EEEE1E1E1EE"
_THETA = {}


def newton_exp(x, prec):
    """exp(x) to about prec bits by Newton's method on ln (not rigorous by itself).
    mpmath's ln is much faster than its exp at millions of bits."""
    p = 2000
    with mp.workprec(p):
        y = mp.exp(x)
    while p < prec:
        p = min(2 * p, prec)
        with mp.workprec(p + 64):
            y = y * (1 + x - mp.log(y))
    return y


def exp_iv(X, prec):
    """An interval containing exp(X) for a real interval X, made rigorous by checking
    ln(lower) <= X.a and ln(upper) >= X.b with directed-rounding logs."""
    with mp.workprec(X._mpi_[0][3] + X._mpi_[1][3] + prec + 64):  # exact endpoints
        xa, xb = mpf(X._mpi_[0]), mpf(X._mpi_[1])
    with mp.workprec(prec + 64):
        y = newton_exp((xa + xb) / 2, prec + 32)
        d = (xb - xa) / 2  # exp(x) = y * exp(x - mid), |x - mid| <= d
        lo = y * (1 - 2 * d - mpf(2) ** -prec)
        hi = y * (1 + 2 * d + mpf(2) ** -prec)
    from mpmath.libmp import mpf_cmp
    if not (mpf_cmp(mpf_log(lo._mpf_, prec + 64, round_ceiling), xa._mpf_) <= 0
            and mpf_cmp(mpf_log(hi._mpf_, prec + 64, round_floor), xb._mpf_) >= 0):
        raise ArithmeticError("exp enclosure check failed")
    return iv.mpf([lo, hi])


def theta(bits=PRECISION):
    """(cos theta, Re W > 0) as a 128-bit interval and a bool. Cached per bits."""
    if bits in _THETA:
        return _THETA[bits]
    t0 = time.time()
    saved = iv.prec
    iv.prec = bits
    e = iv.exp(iv.mpf(1))
    T2 = exp_iv(e, bits)
    T3 = exp_iv(T2, bits)
    print(f"deep.py: T3 done ({time.time() - t0:.0f} s)", flush=True)
    T4 = exp_iv(T3, bits)
    print(f"deep.py: T4 done ({time.time() - t0:.0f} s)", flush=True)
    a = e - iv.log(T2 - e)  # z = a + i*pi
    b = iv.pi
    m2 = a * a + b * b
    reW = T4 * a / m2       # W = T4 / z = T4 * (a - i*pi) / |z|^2
    imW = -T4 * b / m2
    twopi = 2 * iv.pi
    k = imW / twopi
    # any integer n near Im W / 2pi will do: theta = Im W - 2*pi*n
    sign, man, exp_, _ = k._mpi_[0]
    n = (man << exp_) if exp_ >= 0 else (man >> -exp_)
    n = -n if sign else n
    th = imW - twopi * iv.mpf(n)
    iv.prec = 128
    th = +th
    c = iv.cos(th)
    print(f"deep.py: Re W > 0: {reW.a > 0}; width of Im W: {nstr(mpf(imW.delta._mpi_[1]), 5)}")
    print(f"deep.py: theta in {th}")
    print(f"deep.py: cos(theta) in {c}  ({time.time() - t0:.0f} s)", flush=True)
    iv.prec = saved
    _THETA[bits] = (c, bool(reW.a > 0))
    return _THETA[bits]


def check(word, bits=PRECISION):
    """True when the program is certainly not -2."""
    c, re_pos = theta(bits)
    eps = mpf(10) ** -6
    if not re_pos:
        return False
    if word in (K23, K25):
        return bool(c.a > eps or c.b < -eps)
    return False


if __name__ == "__main__":
    bits = int(sys.argv[1]) if len(sys.argv) > 1 else PRECISION  # smaller: testing only
    ok23, ok25 = check(K23, bits), check(K25, bits)
    print(f"{K23} (K 23) is not -2: {ok23}")
    print(f"{K25} (K 25) is not -2: {ok25}")
    sys.exit(0 if ok23 else 1)
