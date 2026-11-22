import json, sys
from verify import matches
ex=json.load(open("exact.json"))
best=json.load(open(__import__("os").path.join(__import__("os").path.dirname(__file__), "../../lib/eml/best-known.json")))["programs"]
bk={k:len(v) for k,v in best.items() if set(v)<=set("1E")}
alias={"1i":"i","-1ipi":"-ipi","1ipi":"ipi"}
for f in sys.argv[1:]:
    groups={}
    for l in open(f):
        if not l.startswith("CAND"): continue
        _,t,K,fl,w=l.rstrip("\n").split("\t"); groups.setdefault(t,{}).setdefault(int(K),[]).append((fl,w))
    print("==", f)
    for t in sorted(groups, key=lambda t: min(groups[t])):
        a,b=ex[t]; found=None; tried=0
        for K in sorted(groups[t]):
            for fl,w in groups[t][K]:
                tried+=1
                ok1,_=matches(w,a,b,100)
                if ok1 and matches(w,a,b,700)[0]: found=(K,fl,w); break
            if found: break
        kn=bk.get(alias.get(t,t),"-"); kns=bk.get(alias.get(t,t)+"-strict","-")
        print(f"{t:8s} {'K%d'%found[0] if found else 'none':5s} ln0={found[1] if found else '-'} known={kn}/{kns} tried={tried} {found[2] if found else ''}", flush=True)
