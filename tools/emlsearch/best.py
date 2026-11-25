import json, os, sys
best = json.load(open(os.path.join(os.path.dirname(__file__), "../../lib/eml/best-known.json")))["programs"]
bk = {k: len(v) for k, v in best.items() if set(v) <= set("1E")}
alias = {"1i": "i", "-1ipi": "-ipi", "1ipi": "ipi"}
b = {}
for l in open(sys.argv[1]):
  s, t, K, fl, w, *_ = l.rstrip("\n").split("\t")
  if s != "PASS": continue
  K = int(K)
  if t not in b or (K, fl) < (b[t][0], b[t][2]): b[t] = (K, w, fl)
for k, (K, w, fl) in sorted(b.items(), key=lambda x: x[1][0]):
  name = alias.get(k, k)
  print(f"{k:8s} K{K:3d} ln0={fl} known={bk.get(name, '-')}/{bk.get(name + '-strict', '-')} {w}")
