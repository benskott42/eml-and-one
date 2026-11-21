import sys; sys.path.insert(0,'.')
from common import *
cut=sys.argv[1]; N=int(sys.argv[2])
C=EC.Ctx(cut,'allowed'); S={1:{('F',C.ONE):C.ONE}}; seen={('F',C.ONE)}; new={1:1}; unres=0
for n in range(2,N+1):
    S[n]={}; nw=0
    for i in range(1,n):
        for ka,a in S[i].items():
            for kb,b in S[n-i].items():
                l0=C.stats['log0']
                try: v=EC.eml_val(C,a,b)
                except EC.Unresolved: unres+=1; continue
                if C.stats['log0']!=l0 or v in ('NAN','INVALID'): continue
                k=skey(v)
                if k[0]!='F': continue
                if k not in S[n]: S[n][k]=v
                if k not in seen: seen.add(k); nw+=1
    new[n]=nw
cum=0
for n in range(1,N+1):
    cum+=new[n]; print(cut,'n',n,'exactly',len(S[n]),'new',new[n],'cum',cum,flush=True)
print('unresolved',unres)
