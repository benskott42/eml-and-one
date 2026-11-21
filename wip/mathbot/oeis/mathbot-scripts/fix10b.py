import sys; sys.path.insert(0,'.')
from common import *
cut=sys.argv[1]
P=[['1111EEE11EE', '111111EEE11EEE1EE1E'], ['111E11E1EEE11EE', '111E1EE11E11E1EEE1E'], ['1111EEE111EE1E1EE', '11111EEE1EE111EEE1E'], ['1111EE11EEE11E1EE', '111E1EE111EE11EEE1E'], ['111E1EE111EEE11EE', '11111E1EEEE111EEE1E'], ['111E11E1E1E1EEE11EE', '11E11E11E1E1E1EEE1E']]
def run(free):
    C=EC.Ctx(cut,'allowed'); S={1:{('F',C.ONE):C.ONE}}
    for n in range(2,11):
        S[n]={}
        for i in range(1,n):
            for ka,a in S[i].items():
                for kb,b in S[n-i].items():
                    l0=C.stats['log0']
                    try: v=EC.eml_val(C,a,b)
                    except EC.Unresolved: continue
                    if v in ('NAN','INVALID') or (free and C.stats['log0']!=l0): continue
                    k=skey(v)
                    S[n].setdefault(k,v)
    def wk(w):
        st=[]
        for c in w:
            if c=='1': st.append(C.ONE)
            else: b=st.pop(); a=st.pop(); st.append(EC.eml_val(C,a,b))
        return skey(st[0])
    par={}
    def f(x):
        while par.get(x,x)!=x: x=par[x]
        return x
    for x,y in P: par[f(wk(x))]=f(wk(y))
    cl=lambda ks:len({f(k) for k in ks})
    cumk=set(); prev=None; out=[]
    for n in range(1,11):
        Fn={k for k in S[n] if k[0]=='F'}; cumk|=Fn; a=cl(cumk); out.append((n,cl(Fn),len(Fn),a,len(cumk)))
    return out
for free in (False,True):
    r=run(free)
    print(cut,'ln0free' if free else 'all', 'n=9:',r[8],'n=10 (exact corrected, exact engine, cum corrected, cum engine):',r[9],'new10 corrected',r[9][3]-r[8][3],flush=True)
