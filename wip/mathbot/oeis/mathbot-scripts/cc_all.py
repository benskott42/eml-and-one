import sys; sys.path.insert(0, '.')
from common import *
cut=sys.argv[1]; N=int(sys.argv[2])
C, V, best, nofree, unres = enumerate_values(N, cut, False)
cum_f=0; cum_s=0
for n in sorted(V):
    f=sum(1 for k in V[n] if k[0]=='F'); s=sum(1 for k in V[n] if k[0]!='F')
    cum_f+=f; cum_s+=s
    print(cut, 'K=',2*n-1 if n>=1 else n, 'new finite',f,'cum finite',cum_f,'new special',s,'cum special',cum_s, flush=True)
print('unresolved',len(unres))
