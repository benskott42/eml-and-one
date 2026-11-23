import json,sys
best=json.load(open(__import__("os").path.join(__import__("os").path.dirname(__file__), "../../lib/eml/best-known.json")))["programs"]
bk={k:len(v) for k,v in best.items() if set(v)<=set("1E")}
b={}
for l in open(sys.argv[1]):
  s,t,K,fl,w,*_=l.rstrip("\n").split("\t")
  if s!="PASS": continue
  K=int(K)
  if t not in b or K<b[t][0]: b[t]=(K,w,fl)
for k,(K,w,fl) in sorted(b.items(), key=lambda x:x[1][0]):
  print(f"{k:8s} K{K:3d} ln0={fl} known={bk.get(k,'-')}/{bk.get(k+'-strict','-')} {w}")
