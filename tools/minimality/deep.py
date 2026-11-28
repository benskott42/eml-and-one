"""Phases that only millions of bits settle: the oracle behind towers.py's exp(W).

When W is huge, as W = T4 / z with T4 = exp(exp(exp(e))) (about 10^1656520) and
z = e - ln(e - T2) = e - ln(T2 - e) + i*pi on the lower cut, the phase of exp(W) is
Im W mod 2*pi, and that depends on every digit of T4. towers.py keeps exp(W) as a
tower and asks phase(word) for that phase, where word is the subword whose value is W.

phase() evaluates the word with mpmath interval arithmetic at about log2|Im W| + 512
bits (rounded up to a multiple of 65536), so Im W is known to far better than 2*pi,
and returns Im W - 2*pi*n for an integer n, as a 128-bit interval. The evaluation
uses only identities that hold exactly: exp(x - ln y) = exp(x) / y, so T4 / z is
exp(T3) / z and T4 is shared; ln(exp x) = x when Im x is in [-pi, pi); ln 1 = 0; and
the principal log on the lower cut (Arg in [-pi, pi)), refused when the enclosure
touches the cut. Past 50000 bits, exp, ln, atan, cos and sin are python-flint arb balls whose
endpoints are rounded outward into an mpmath interval. exp, ln and atan are
monotone, so each endpoint is evaluated on its own. cos and sin are one ball
over the whole interval. A word
whose value needs exp of something beyond 2^31 (a phase that is a tower itself,
such as Im exp(T4 / z)) is refused: no precision reaches it.

run() decides a list of words in parallel worker processes. The workers share every
result above 50000 bits through files in a temporary directory, so T2, T3 and T4 are
computed once, by whichever worker needs them first, while the others wait.

usage: python deep.py [word ...]   (default: the K 23 and K 25 programs that need it;
                                    5.5 million bits, one arb.exp of T3)
"""
import hashlib
import os
import pickle
import shutil
import sys
import tempfile
import time
from mpmath import iv, mp, mpf
from mpmath.libmp import from_man_exp, round_ceiling, round_floor

STEP = 1 << 16          # precisions are multiples of this, so words share their exps
MAX_BITS = 6_000_000    # T4 / z needs about 5.5 million
BIG = 50_000            # above this: arb, and results shared between workers
HUGE = mpf(2) ** 31     # exp of anything larger is refused
SHARE = None            # directory shared by the workers of run()
MEMO = {}
PHASES = {}
WORDS = ["11E1E1111E1E1EEEE1E1E1E", "111E1E1111E1E1EEEE1E1E1EE"]


class Refused(Exception):
    pass


def _raw_to_arb(raw):
    """Exact arb for an mpmath raw mpf (sign, man, exp, bc). man * 2^exp, no rounding."""
    import flint
    sign, man, exp, bc = raw
    if not man:
        return flint.arb(0)
    saved = flint.ctx.prec
    # The power of two has |exp| + 1 bits, and man has bc bits. Both have to be exact.
    flint.ctx.prec = max(saved, int(bc) + abs(int(exp)) + 64, 64)
    try:
        a = flint.arb(int(man))
        if exp > 0:
            a = a * flint.arb(1 << int(exp))
        elif exp < 0:
            a = a / flint.arb(1 << int(-exp))
        if sign:
            a = -a
        if not a.is_exact():
            raise ArithmeticError("endpoint did not convert exactly")
        return a
    finally:
        flint.ctx.prec = saved


def _exact_bound(ball, prec, downward):
    """Outward raw mpf for an exact arb endpoint, rounded to prec bits."""
    if not ball.is_exact():
        ball = ball.lower() if downward else ball.upper()
    if not ball.is_exact():
        raise ArithmeticError("arb bound did not resolve")
    man, exp = ball.man_exp()
    rnd = round_floor if downward else round_ceiling
    return from_man_exp(int(man), int(exp), prec, rnd)


def _mono_iv(method, X, prec):
    """An interval containing method(X) for a monotone arb function (exp, log, atan).

    Each endpoint is evaluated on its own, and that ball's outward endpoint is
    rounded outward again into an mpmath interval.
    """
    import flint
    saved = flint.ctx.prec
    flint.ctx.prec = prec + 64
    try:
        lo = getattr(_raw_to_arb(X._mpi_[0]), method)().lower()
        hi = getattr(_raw_to_arb(X._mpi_[1]), method)().upper()
        return iv.make_mpf((_exact_bound(lo, prec, True), _exact_bound(hi, prec, False)))
    finally:
        flint.ctx.prec = saved


def _range_iv(method, X, prec):
    """An interval containing method(X). One ball covers X, so this stays valid
    for cos and sin, which are not monotone."""
    import flint
    saved = flint.ctx.prec
    flint.ctx.prec = prec + 64
    try:
        ball = _raw_to_arb(X._mpi_[0]).union(_raw_to_arb(X._mpi_[1]))
        ball = getattr(ball, method)()
        return iv.make_mpf((_exact_bound(ball.lower(), prec, True),
                            _exact_bound(ball.upper(), prec, False)))
    finally:
        flint.ctx.prec = saved


def exp_iv(X, prec):
    """An interval containing exp(X)."""
    return _mono_iv("exp", X, prec)


def arb_cos_sign(th):
    """+1 if an arb enclosure of cos(th) is > 0, -1 if < 0, else None.

    th is a real iv interval. The sign is returned only when that ball lies
    entirely on one side of 0. A ball that contains 0, or whose comparison with
    0 is not decided, is not a sign.
    """
    import flint
    saved = flint.ctx.prec
    flint.ctx.prec = max(256, saved)
    try:
        ball = _raw_to_arb(th._mpi_[0]).union(_raw_to_arb(th._mpi_[1]))
        c = ball.cos()
        if c > 0:
            return 1
        if c < 0:
            return -1
        return None
    finally:
        flint.ctx.prec = saved


def log_iv(X):
    """An interval containing ln(X), X > 0."""
    return _mono_iv("log", X, iv.prec)


def atan_iv(X):
    """An interval containing atan(X)."""
    return _mono_iv("atan", X, iv.prec)


# ---------------------------------------------------------------- shared primitives

def _digest(op, args):
    h = hashlib.sha256(f"{op}:{iv.prec}".encode())
    for x in args:
        for sign, man, exp, bc in x._mpi_:
            h.update(f"|{sign},{exp},{bc},".encode())
            h.update(int(man).to_bytes((int(man).bit_length() + 7) // 8, "little"))
    return h.hexdigest()


def _prim(op, fn, *args):
    """fn(*args) at the current precision, memoized; past BIG bits, shared with the other
    workers through SHARE (one computes, the rest wait for its file)."""
    k = _digest(op, args)
    if k in MEMO:
        return MEMO[k]
    if SHARE is None or iv.prec < BIG:
        MEMO[k] = fn(*args)
        return MEMO[k]
    res, lock = os.path.join(SHARE, k + ".pkl"), os.path.join(SHARE, k + ".lock")
    while True:
        if os.path.exists(res):
            with open(res, "rb") as f:
                kind, raw = pickle.load(f)
            if kind != "ok":
                raise Refused(f"{op} failed in another worker: {raw}")
            MEMO[k] = iv.make_mpf(raw)
            return MEMO[k]
        try:
            os.close(os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY))
        except FileExistsError:
            time.sleep(1)
            continue
        try:
            out = ("ok", fn(*args)._mpi_)
        except (Refused, ArithmeticError, ZeroDivisionError, ValueError, OverflowError) as why:
            # A mathematical refusal is the same for every worker. Publish it so the others
            # stop waiting. An alarm or interrupt is not: drop the lock and let the next
            # worker compute, instead of caching a failure of a value that can be computed.
            out = ("error", f"{type(why).__name__}: {why}")
            with open(res + ".tmp", "wb") as f:
                pickle.dump(out, f)
            os.replace(res + ".tmp", res)
            raise Refused(out[1]) from why
        except BaseException:
            try:
                os.remove(lock)
            except OSError:
                pass
            raise
        with open(res + ".tmp", "wb") as f:
            pickle.dump(out, f)
        os.replace(res + ".tmp", res)
        MEMO[k] = iv.make_mpf(out[1])
        return MEMO[k]


def rexp(x):
    if x.a < -HUGE or x.b > HUGE:
        raise Refused("exp of a tower")
    if iv.prec >= BIG:
        p = iv.prec
        return _prim("exp", lambda y: exp_iv(y, p), x)
    return _prim("exp", iv.exp, x)


def rlog(x):
    if x.a <= 0:
        raise Refused("log of an interval that is not positive")
    return _prim("log", log_iv if iv.prec >= BIG else iv.log, x)


def rarg(y, x):
    """Arg(x + iy) in (-pi, pi), for a rectangle off the negative real axis."""
    if iv.prec < BIG:
        return _prim("atan2", iv.atan2, y, x)
    if x.a > 0:
        return _prim("atan", atan_iv, y / x)
    if y.a > 0:
        return iv.pi / 2 - _prim("atan", atan_iv, x / y)
    if y.b < 0:
        return -iv.pi / 2 - _prim("atan", atan_iv, x / y)
    raise Refused("argument on the cut")


def rcos(x):
    if iv.prec >= BIG:
        p = iv.prec
        return _prim("cos", lambda y: _range_iv("cos", y, p), x)
    return _prim("cos", iv.cos, x)


def rsin(x):
    if iv.prec >= BIG:
        p = iv.prec
        return _prim("sin", lambda y: _range_iv("sin", y, p), x)
    return _prim("sin", iv.sin, x)


# ---------------------------------------------------------------- the evaluator


def zint(x):
    return x.a == 0 and x.b == 0


def split(w):
    """(x, y) with w = x + y + "E"."""
    st = []
    for i, ch in enumerate(w):
        if ch == "1":
            st.append(i)
        else:
            y = st.pop()
            x = st.pop()
            if i == len(w) - 1 and x == 0:
                return w[:y], w[y:-1]
            st.append(x)
    raise ValueError(f"not a program: {w}")


def memo(tag, w, fn):
    k = (tag, w, iv.prec)
    if k not in MEMO:
        MEMO[k] = fn()
    return MEMO[k]


def val(w):
    """The value of the word w on the lower cut, as (re, im) intervals."""
    def go():
        if w == "1":
            return iv.mpf(1), iv.mpf(0)
        x, y = split(w)
        B = L(y)  # first: the logs do not wait for the long exps
        A = E(x)
        return A[0] - B[0], A[1] - B[1]
    return memo("val", w, go)


def E(w):
    """exp(value of w). exp(exp(x) - ln y) = exp(exp(x)) / y exactly, for any branch."""
    def go():
        if w == "1":
            return rexp(iv.mpf(1)), iv.mpf(0)
        x, y = split(w)
        if y == "1":
            return cexp(E(x))
        B = val(y)
        return cdiv(cexp(E(x)), B)
    return memo("exp", w, go)


def L(w):
    """ln(value of w), lower cut."""
    def go():
        if w == "1":
            return iv.mpf(0), iv.mpf(0)
        x, y = split(w)
        if y == "1":
            X = val(x)  # ln(exp X) = X when Im X is in [-pi, pi)
            if zint(X[1]) or (X[1].a >= -iv.pi.a and X[1].b < iv.pi.a):
                return X
        return clog(val(w))
    return memo("ln", w, go)


def cexp(Z):
    r = rexp(Z[0])
    if zint(Z[1]):
        return r, iv.mpf(0)
    return r * rcos(Z[1]), r * rsin(Z[1])


def cdiv(A, B):
    if zint(B[1]):
        if B[0].a <= 0 <= B[0].b:
            raise Refused("division by an interval around 0")
        return A[0] / B[0], A[1] / B[0]
    m2 = B[0] * B[0] + B[1] * B[1]
    if m2.a <= 0:
        raise Refused("division by a rectangle around 0")
    return (A[0] * B[0] + A[1] * B[1]) / m2, (A[1] * B[0] - A[0] * B[1]) / m2


def clog(Z):
    re, im = Z
    if zint(im):
        if re.a > 0:
            return rlog(re), iv.mpf(0)
        if re.b < 0:
            return rlog(-re), -iv.pi
        raise Refused("log of a real interval around 0")
    m2 = re * re + im * im
    if m2.a <= 0:
        raise Refused("log of a rectangle around 0")
    if re.a > 0 or im.a > 0 or im.b < 0:
        return rlog(m2) / 2, rarg(im, re)
    raise Refused("log on the cut")


def log2_up(x):
    """An integer >= log2|x| for a finite nonzero mpf x."""
    sign, man, exp, bc = x._mpf_
    if not man:
        raise Refused("zero or infinite bound")
    return exp + bc


def phase(word, verbose=True):
    """A 128-bit interval containing Im(value of word) - 2*pi*n for some integer n,
    or None when no precision up to MAX_BITS gives one."""
    if word in PHASES:
        return PHASES[word]
    saved = iv.prec
    out, note = None, ""
    t0 = time.time()
    try:
        iv.prec = 512
        im = val(word)[1]
        with mp.workprec(64):
            m = max(abs(mpf(im._mpi_[0])), abs(mpf(im._mpi_[1])))
            if not mp.isfinite(m):
                raise Refused("unbounded imaginary part")
        bits = ((max(log2_up(m), 0) + 512) // STEP + 1) * STEP
        while bits <= MAX_BITS and out is None:
            iv.prec = bits
            im = val(word)[1]
            if not (mp.isfinite(mpf(im._mpi_[0])) and mp.isfinite(mpf(im._mpi_[1]))):
                raise Refused("unbounded imaginary part")
            twopi = 2 * iv.pi
            # any integer n near Im / 2pi will do
            sign, man, exp, _ = (im / twopi)._mpi_[0]
            n = (int(man) << exp) if exp >= 0 else (int(man) >> -exp)
            n = -n if sign else n
            th = im - twopi * iv.mpf(n)
            iv.prec = 128
            th = +th
            if th.b - th.a < mpf(2) ** -20:
                out = th
            else:
                bits += STEP
        note = f"{bits} bits"
    except (Refused, ZeroDivisionError, ValueError, OverflowError) as why:
        note = f"refused: {why}"
    finally:
        iv.prec = saved
    if verbose and (out is not None or time.time() - t0 > 1):
        iv.prec = 128
        c = None if out is None else iv.cos(out)
        iv.prec = saved
        print(f"deep.py: Im({word}) mod 2pi in {out}, cos in {c}  ({note}, {time.time() - t0:.0f} s)",
              flush=True)
    PHASES[word] = out
    return out


# ---------------------------------------------------------------- parallel driver

def _init(share):
    global SHARE
    SHARE = share
    import towers
    towers.PHASE = phase


def _work(job):
    import towers
    word, tre, tk = job
    t0 = time.time()
    verdict, why = towers.decide(word, tre, tk)
    return word, tre, tk, verdict, why, time.time() - t0


def run(jobs, workers=None):
    """towers.decide(word, tre, tk) with the phase oracle, for each (word, tre, tk), in
    parallel. Returns {(word, tre, tk): (verdict, reason)}."""
    from concurrent.futures import ProcessPoolExecutor, as_completed
    jobs = list(dict.fromkeys(jobs))
    if not jobs:
        return {}
    workers = workers or max(1, min(len(jobs), (os.cpu_count() or 2) - 1))
    share = tempfile.mkdtemp(prefix="eml-deep-")
    out = {}
    try:
        with ProcessPoolExecutor(max_workers=workers, initializer=_init, initargs=(share,)) as ex:
            for f in as_completed([ex.submit(_work, j) for j in jobs]):
                word, tre, tk, verdict, why, secs = f.result()
                print(f"deep.py: {word} target {tre}{'+' + str(tk) + 'i*pi' if tk else ''}: "
                      f"{'excluded' if verdict else ('EQUAL' if verdict is False else 'undecided: ' + str(why))}"
                      f"  ({secs:.0f} s)", flush=True)
                out[(word, tre, tk)] = (verdict, why)
    finally:
        shutil.rmtree(share, ignore_errors=True)
    return out


if __name__ == "__main__":
    words = sys.argv[1:] or WORDS
    t0 = time.time()
    res = run([(w, -2, 0) for w in words])
    ok = all(v is True for v, _ in res.values())
    print(f"deep.py: {sum(v is True for v, _ in res.values())} of {len(res)} excluded as -2  "
          f"({time.time() - t0:.0f} s)")
    sys.exit(0 if ok else 1)
