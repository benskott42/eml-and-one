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

## Last-gate inversion (MITM)

Every word ends in one gate, eml(a, b) = t, and on the lower cut that means ln b = exp(a) − t. With the whole pool up to K 35 in memory, each `a` gives the `b` it needs, and `b` is looked up among all stored values. That reaches words up to K 71 whose two halves are each at most K 35:

```bash
MITM=1 MITM_KMAX=71 SLOTS=3 ./target/release/emlsearch 18 0 focus.tsv 18 > mitm-ln0.txt     # ~90 s, ~6 GB
MITM=1 MITM_KMAX=71 SLOTS=3 ./target/release/emlsearch 18 1 focus.tsv 18 > mitm-strict.txt
python firstpass.py mitm-ln0.txt mitm-strict.txt   # shortest word per target that passes 100 and 700 digits
```

The first run of this found −iπ (lower cut) without ln 0 at K 47: `11111E1E1EEEE11111111E1E1EEEE1E1E1EEE1EE11E1EEE`. The record had been K 55. Most float hits are impostors. The tolerance is 1e-11 and nothing is filtered by "best so far", because an early impostor must not hide a genuine longer word.
