"""Independent high-precision check of EML words (lower cut, ln 0 = -inf).

Values are (re, im) mpf pairs so signed infinities stay explicit. A component is
treated as exactly 0 when it cancelled below 10^-(dps-12) of its operands; the
check runs at two precisions and a word passes only if both agree with the target
to 10^-(dps-20). This is a numerical check, not a proof.
"""
import sys
from mpmath import mp, mpf, exp, log, cos, sin, atan2, pi, hypot, isinf, isnan, inf

def snap(d, a, b):
    if d == 0 or isinf(d) or isnan(d):
        return d
    s = max(abs(a), abs(b))
    if s > 0 and not isinf(s) and abs(d) <= s * mpf(10) ** (-(mp.dps - 12)):
        return mpf(0)
    return d

def cexp(re, im):
    if isnan(re) or isnan(im) or isinf(im):
        return None
    if re == -inf:
        return (mpf(0), mpf(0))
    # reduce angle to nearest quarter turn like complex.ts
    q = pi / 2
    k = int(mp.nint(im / q))
    d = im - k * q
    if abs(d) <= mpf(10) ** (-(mp.dps - 12)) * max(1, abs(im)):
        d = mpf(0)
    s = mpf(0) if d == 0 else sin(d)
    c = mpf(1) if d == 0 else cos(d)
    ax = k % 4
    t = [(c, s), (-s, c), (-c, -s), (s, -c)][ax]
    if re == inf:
        f = lambda p: mpf(0) if p == 0 else (inf if p > 0 else -inf)
        return (f(t[0]), f(t[1]))
    m = exp(re)
    return (m * t[0], m * t[1])

def clog(re, im):
    if re == 0 and im == 0:
        return (-inf, mpf(0))
    if isinf(re) or isinf(im):
        arg = -pi if (re < 0 and im == 0) else atan2(im, re)
        return (inf, arg)
    arg = -pi if (re < 0 and im == 0) else atan2(im, re)
    return (log(hypot(re, im)), arg)

def evaluate(word):
    st = []
    for ch in word:
        if ch == '1':
            st.append((mpf(1), mpf(0)))
        else:
            y = st.pop(); x = st.pop()
            a = cexp(*x)
            if a is None:
                return None
            b = clog(*y)
            re = a[0] - b[0]; im = a[1] - b[1]
            if isnan(re) or isnan(im):
                return None
            st.append((snap(re, a[0], b[0]), snap(im, a[1], b[1])))
    return st[0]

def target(spec):
    re, im = spec
    return (mp.mpmathify(re), mp.mpmathify(im))

def matches(word, tre, tim, dps):
    mp.dps = dps
    v = evaluate(word)
    if v is None or isinf(v[0]) or isinf(v[1]):
        return False, v
    T = (eval(tre, {"pi": pi, "e": mp.e, "sqrt": mp.sqrt, "log": log, "mpf": mpf}), eval(tim, {"pi": pi, "e": mp.e, "sqrt": mp.sqrt, "log": log, "mpf": mpf}))
    tol = mpf(10) ** (-(dps - 20)) * max(1, abs(T[0]), abs(T[1]))
    ok = abs(v[0] - T[0]) <= tol and abs(v[1] - T[1]) <= tol
    # a zero target component must be exactly zero
    if T[1] == 0 and v[1] != 0: ok = False
    if T[0] == 0 and v[0] != 0: ok = False
    return ok, v

if __name__ == "__main__":
    # stdin: id \t K \t ln0 \t word \t exact_re \t exact_im
    for line in sys.stdin:
        tid, K, fl, w, tre, tim = line.rstrip("\n").split("\t")
        ok1, v1 = matches(w, tre, tim, 100)
        ok2, v2 = matches(w, tre, tim, 700) if ok1 else (False, None)
        status = "PASS" if ok1 and ok2 else "FAIL"
        mp.dps = 25
        val = "None" if v1 is None else f"{mp.nstr(v1[0], 20)} {mp.nstr(v1[1], 20)}"
        print(f"{status}\t{tid}\t{K}\t{fl}\t{w}\t{val}", flush=True)
