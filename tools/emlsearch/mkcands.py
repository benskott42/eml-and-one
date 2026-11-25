import json, os, sys
ex = json.load(open(os.path.join(os.path.dirname(__file__), "exact.json")))
for line in open(sys.argv[1]):
  if line.startswith("CAND"):
    _, t, K, fl, w = line.rstrip("\n").split("\t"); a, b = ex[t]; print(f"{t}\t{K}\t{fl}\t{w}\t{a}\t{b}")
