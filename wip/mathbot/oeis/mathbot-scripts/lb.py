import sys; sys.path.insert(0,'.')
from common import *
cut=sys.argv[1]; N=int(sys.argv[2])
C, V, best, nofree, unres = enumerate_values(N, cut, False)
items=[]
for n in sorted(V):
    for k,v in V[n].items():
        if k[0]=='F': items.append((n,k,v))
def ball(v):
    b=None
    for p in (2048, 8192):
        b=C.ball(v,p)
        if b.is_finite() and float(b.real.rad())+float(b.imag.rad())==0: break
    return b
B=[(n,ball(v)) for n,k,v in items]
for nmax in range(1,N+1):
    bs=[b for n,b in B if n<=nmax and b.is_finite()]
    # greedy max independent set on interval-overlap graph: sort by real upper end (optimal for 1-D intervals), check full complex overlap vs chosen in window
    bs.sort(key=lambda b: float(b.real.upper()))
    chosen=[]
    for b in bs:
        lo=float(b.real.lower())
        if all(not b.overlaps(c) for c in chosen if float(c.real.upper())>=lo): chosen.append(b)
    U=sum(1 for n,b in B if n<=nmax)
    print(cut,'n',nmax,'L',len(chosen),'U',U,flush=True)
