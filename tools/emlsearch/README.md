# emlsearch

A fast bottom-up search for short constant EML words, and an independent checker.

```bash
cargo build --release
SLOTS=3 CAND_CAP=400 ./target/release/emlsearch 21 0 targets.tsv 20 > deep-ln0.txt     # K ≤ 41, ln 0 allowed
SLOTS=3 CAND_CAP=400 ./target/release/emlsearch 21 1 targets.tsv 20 > deep-strict.txt  # K ≤ 41, no ln 0
python mkcands.py deep-ln0.txt > cands.tsv
python verify.py < cands.tsv > verified.tsv      # PASS needs agreement at 100 and 700 digits
python best.py verified.tsv                      # shortest verified word per target, beside best-known.json
```

`verify.py` is mpmath with the calculator's conventions (lower cut, ln 0 = −∞). It is a
numerical check, not a proof: a residue below about 10^(−680) still passes. At 250 digits it
passed the K 35 word `11111111E11E1EE1EEEEEE1E1E11E1E1EEE`, which is −9×10^(−307) − i(π − ε),
not −iπ. A new record also has to pass `acceptsConstantProgram` in `lib/eml/golf.ts`.

Results of the 2026-11-22 run are in `docs/search-k41.md`.
