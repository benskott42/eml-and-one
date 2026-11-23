# Sanity check of the series remainder bounds in ball-soundness.md §5 on complex discs (mpmath, 60 digits).
import mpmath as mp, random
mp.mp.dps = 250
random.seed(1)
def pts(m, n=200):
    for _ in range(n):
        t = random.uniform(0, 2*mp.pi); s = random.choice([1, random.random()])
        yield m*s*mp.expj(t)
def worst(f, poly, bound, ms):
    w = 0
    for m in ms:
        B = bound(mp.mpf(m))
        for z in pts(mp.mpf(m)):
            w = max(w, abs(f(z) - poly(z)) / B)
    return w
def odd_poly(coef, N):  # sum over odd k <= N of coef(k) z^k
    return lambda z: mp.fsum(coef(k)*z**k for k in range(1, N+1, 2))
ms = ["1e-6", "1e-3", "0.1", "0.5", "0.9"]
rows = []
for N in (1, 3, 7, 11):
    # sinh / sin: |a_k| <= 1/k!; tail after degree N (odd): m^(N+2)/(N+2)! / (1 - m^2/((N+3)(N+4)))
    tb = lambda m: m**(N+2)/mp.factorial(N+2)/(1 - m**2/((N+3)*(N+4)))
    rows.append((f"sinh N={N}", worst(mp.sinh, odd_poly(lambda k: 1/mp.factorial(k), N), tb, ms)))
    rows.append((f"sin  N={N}", worst(mp.sin, odd_poly(lambda k: (-1)**((k-1)//2)/mp.factorial(k), N), tb, ms)))
    # generic factorial tail for exp-1 etc: m^(N+1)/(N+1)! / (1 - m/(N+2))
    tg = lambda m: m**(N+1)/mp.factorial(N+1)/(1 - m/(N+2))
    rows.append((f"exp  N={N}", worst(mp.exp, lambda z: mp.fsum(z**k/mp.factorial(k) for k in range(N+1)), tg, ms)))
    # artanh / arctan: coefficients 1/k on odd k; tail m^(N+2)/((N+2)(1-m^2))
    ta = lambda m: m**(N+2)/((N+2)*(1 - m**2))
    rows.append((f"artanh N={N}", worst(mp.atanh, odd_poly(lambda k: mp.mpf(1)/k, N), ta, ms)))
    rows.append((f"arctan N={N}", worst(mp.atan, odd_poly(lambda k: (-1)**((k-1)//2)*mp.mpf(1)/k, N), ta, ms)))
    # arcsin: c_k = binom(2j,j)/(4^j (2j+1)) <= 1/k, same tail
    rows.append((f"arcsin N={N}", worst(mp.asin, odd_poly(lambda k: mp.binomial(k-1, (k-1)//2)/(4**((k-1)//2)*k), N), ta, ms)))
    # ln(1+z): coefficients (-1)^(k+1)/k; tail m^(N+1)/((N+1)(1-m))
    tl = lambda m: m**(N+1)/((N+1)*(1 - m))
    rows.append((f"log1p N={N}", worst(mp.log1p, lambda z: mp.fsum((-1)**(k+1)*z**k/k for k in range(1, N+1)), tl, ms)))
for name, w in rows:
    print(f"{name:14s} worst |tail|/bound = {mp.nstr(w, 4)}" + ("   VIOLATION" if w > 1 else ""))
print("ALL WITHIN BOUND" if all(w <= 1 for _, w in rows) else "VIOLATION FOUND")
# The 'next term' rule fails on complex discs: sinh, N=1, z = i*m vs real alternating intuition is irrelevant;
# show a case where |tail| > |next term| for arctan on |z|=0.9 (complex direction).
z = 0.9j; N = 1
nt = abs(z**3/3); tail = abs(mp.atan(z) - z)
print(f"arctan, z=0.9i, N=1: |tail|={mp.nstr(tail,6)} vs |next term|={mp.nstr(nt,6)} -> next-term rule {'FAILS' if tail > nt else 'holds'}")
