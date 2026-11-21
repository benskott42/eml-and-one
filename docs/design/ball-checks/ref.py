# mpmath reference (700 digits), calculator log bank: ln of a negative real = ln|x| - i*pi.
import json, sys, mpmath
mpmath.mp.dps = 700
def elog(z):
    if z.imag == 0 and z.real < 0:
        return mpmath.mpc(mpmath.log(-z.real), -mpmath.pi)
    return mpmath.log(z)
out = []
for t in json.load(sys.stdin):
    z = mpmath.mpc(mpmath.mpf(t[1]), mpmath.mpf(t[2]))
    v = mpmath.exp(z) if t[0] == "exp" else elog(z)
    out.append([mpmath.nstr(v.real, 600, min_fixed=1, max_fixed=0), mpmath.nstr(v.imag, 600, min_fixed=1, max_fixed=0)])
print(json.dumps(out))
