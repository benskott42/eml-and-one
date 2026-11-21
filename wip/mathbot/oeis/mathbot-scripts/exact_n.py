import sys; sys.path.insert(0,'.')
from common import *
cut=sys.argv[1]; N=int(sys.argv[2])
C=EC.Ctx(cut,'allowed'); S={1:{('F',C.ONE):C.ONE}}; unres=0
for n in range(2,N+1):
    S[n]={}
    for i in range(1,n):
        for ka,a in S[i].items():
            for kb,b in S[n-i].items():
                try: v=EC.eml_val(C,a,b)
                except EC.Unresolved: unres+=1; continue
                if v in ('NAN','INVALID'): continue
                k=skey(v)
                if k not in S[n]: S[n][k]=v
for n in range(1,N+1):
    print(cut,'n',n,'K',2*n-1,'exactly-n finite',sum(1 for k in S[n] if k[0]=='F'),'special',sum(1 for k in S[n] if k[0]!='F'),flush=True)
print('unresolved',unres)
