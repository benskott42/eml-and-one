import sys; sys.path.insert(0,'.')
from common import *
cut=sys.argv[1]
C=EC.Ctx(cut,'allowed'); S={1:{('F',C.ONE):C.ONE}}
for n in range(2,11):
    S[n]={}
    for i in range(1,n):
        for ka,a in S[i].items():
            for kb,b in S[n-i].items():
                try: v=EC.eml_val(C,a,b)
                except EC.Unresolved: continue
                if v in ('NAN','INVALID'): continue
                k=skey(v)
                if k not in S[n]: S[n][k]=v
def word(w):
    st=[]; l0=C.stats['log0']
    for c in w:
        if c=='1': st.append(C.ONE)
        else: b=st.pop(); a=st.pop(); st.append(EC.eml_val(C,a,b))
    return skey(st[0]), C.stats['log0']>l0
P=[['1111EEE11EE', '111111EEE11EEE1EE1E'], ['111E11E1EEE11EE', '111E1EE11E11E1EEE1E'], ['1111EEE111EE1E1EE', '11111EEE1EE111EEE1E'], ['1111EE11EEE11E1EE', '111E1EE111EE11EEE1E'], ['111E1EE111EEE11EE', '11111E1EEEE111EEE1E'], ['111E11E1E1E1EEE11EE', '11E11E11E1E1E1EEE1E']]
for x,y in P:
    kx,lx=word(x); ky,ly=word(y)
    print(cut,len(x),len(y),'distinct keys',kx!=ky,'short key at exactly K19',kx in S[10],'long in S10',ky in S[10],'ln0',lx,ly,flush=True)
