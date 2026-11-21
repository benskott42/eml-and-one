import sys,pickle,time,json
sys.path.insert(0,'/workspace/eml-hub/mathbot/schanuel/hunt')
from common import *
sys.path.insert(0,'/workspace/eml-hub/oeis/mathbot-scripts')
# reference remains read-only
P=[['1111EEE11EE', '111111EEE11EEE1EE1E'], ['111E11E1EEE11EE', '111E1EE11E11E1EEE1E'], ['1111EEE111EE1E1EE', '11111EEE1EE111EEE1E'], ['1111EE11EEE11E1EE', '111E1EE111EE11EEE1E'], ['111E1EE111EEE11EE', '11111E1EEEE111EEE1E'], ['111E11E1E1E1EEE11EE', '11E11E11E1E1E1EEE1E']]
C=EC.Ctx('lower','allowed'); S={1:{('F',C.ONE):(C.ONE,'1',True)}};best={('F',C.ONE):'1'};free=set(best); exact={}
for n in range(2,11):
 S[n]={}
 for i in range(1,n):
  for ka,(a,wa,fa) in S[i].items():
   for kb,(b,wb,fb) in S[n-i].items():
    l0=C.stats['log0']
    v=EC.eml_val(C,a,b)
    if v in ('NAN','INVALID'):continue
    k=skey(v);w=wa+wb+'E';f=fa and fb and C.stats['log0']==l0
    if k not in S[n]:S[n][k]=(v,w,f)
    else:
     vo,wo,fo=S[n][k];S[n][k]=(vo,min(w,wo),fo or f)
    if k not in best or (len(w),w)<(len(best[k]),best[k]):best[k]=w
    if f:free.add(k)
 print(n,len(S[n]),len(best),flush=True)
def wk(w):
 st=[]
 for ch in w:
  if ch=='1':st.append(C.ONE)
  else:b=st.pop();a=st.pop();st.append(EC.eml_val(C,a,b))
 return skey(st[0])
par={}
def f(x):
 while par.get(x,x)!=x:x=par[x]
 return x
for x,y in P:par[f(wk(x))]=f(wk(y))
groups={}
for k,w in best.items():
 if k[0]=='F':groups.setdefault(f(k),[]).append(k)
print('RAW',sum(k[0]=='F' for k in best),'MERGED',len(groups),flush=True)
q=['11111E11EEE11EEE1EE','11111E1EEEE11E11EEE'];print('seventh',[(w,wk(w),C.show(wk(w)[1])) for w in q],flush=True)
rows=[]
for root,ks in groups.items():
 w=min((best[k] for k in ks),key=lambda w:(len(w),w))
 rows.append(dict(word=w,fid=wk(w)[1],keys=ks,b=int(len(w)==19),c=int(any(k in S[10] for k in ks)),ln0free=int(any(k in free for k in ks))))
rows.sort(key=lambda r:(len(r['word']),r['word']))
print('flags',*[sum(r[k] for r in rows) for k in ('b','c','ln0free')],flush=True)
for r in rows: r['keys']=[list(k) for k in r['keys']]
json.dump(rows,open('/workspace/eml-hub/oeis/mathbot-scripts/n10-audit/rows.json','w'))

import mpmath as mp, signal
class TO(Exception):pass
def h(*a):raise TO()
signal.signal(signal.SIGALRM,h)
def mval(fid,memo):
  if fid in memo:return memo[fid]
  cre,cim,terms=C.fkey[fid]
  z=mp.mpc(cre,0)+mp.mpc(0,cim)*mp.pi
  if cim==0 and len(terms)==1 and terms[0][1]==-cre and cre!=0 and C.akind[terms[0][0]]=='E':
    z=-cre*mp.expm1(mval(C.aarg[terms[0][0]],memo)); memo[fid]=z; return z
  for a,k in terms:
    g=C.aarg[a]
    if C.akind[a]=='E': t=mp.exp(mval(g,memo))
    else:
      gk=C.fkey[g]
      if gk[0]==1 and gk[1]==0 and gk[2]:
        rest=mp.mpc(0)
        for a2,k2 in gk[2]:
          rest+=k2*(mp.exp(mval(C.aarg[a2],memo)) if C.akind[a2]=='E' else mp.log(mval(C.aarg[a2],memo)))
        t=mp.log1p(rest)
      else: t=mp.log(mval(g,memo))
    z+=k*t
  memo[fid]=z;return z
def close(x,y,d):
  return (x==y) or abs(x-y)<=mp.mpf(10)**(-d)*max(abs(x),abs(y))
def big(fid,seen=None):
  seen=set() if seen is None else seen
  if fid in seen: return False
  seen.add(fid)
  for a,k in C.fkey[fid][2]:
    g=C.aarg[a]
    if C.akind[a]=='E':
      bb=C.ball(g)
      if not bb.is_finite() or not (bb.real < 10**8): return True
    if big(g,seen): return True
  return False
def ev(fid):
  if big(fid): return None,None
  try:
    signal.alarm(10)
    mp.mp.dps=90; v1=mval(fid,{}); mp.mp.dps=180; v2=mval(fid,{})
    signal.alarm(0)
    mp.mp.dps=180
    if close(v1.real,v2.real,64) and close(v1.imag,v2.imag,64): return v2,'mpmath'
  except (TO,OverflowError,ValueError,ZeroDivisionError): signal.alarm(0)
  return None,None
from flint import ctx as fc
nfb=0
import time
T0=time.time()
for ii,r in enumerate(rows):
  if ii%250==0: print('row',ii,time.time()-T0,flush=True)
  v,src=ev(r['fid'])
  b=C.ball(r['fid'],512) if v is not None else None
  if v is None:
    nfb+=1; src='arb8192'
    for pr in (512,2048,8192):
      b=C.ball(r['fid'],pr); fc.prec=pr
      if b.is_finite() and min(b.real.rel_accuracy_bits() if b.real!=0 else 10**9,b.imag.rel_accuracy_bits() if b.imag!=0 else 10**9)>210: break
    r['re']=b.real.str(60,radius=False); r['im']=b.imag.str(60,radius=False)
    r['acc']=min(b.real.rel_accuracy_bits(),b.imag.rel_accuracy_bits()) if True else None
  else:
    mp.mp.dps=70
    r['re']=mp.nstr(+v.real,60); r['im']=mp.nstr(+v.imag,60)
  r['src']=src
for r in rows: r['form']=C.show(r['fid']).replace('\\n',' ')
print('fallbacks',nfb,flush=True)
for r in rows:
  if r['src']!='mpmath':print(r['word'],r['re'][:40],r['im'][:40],flush=True)
for r in rows: r['keys']=[list(k) for k in r['keys']]
json.dump(rows,open('/workspace/eml-hub/oeis/mathbot-scripts/n10-audit/rows.json','w'))
