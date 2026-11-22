# Search through K 41, and last-gate inversion to K 71 (2026-11-22)

An independent bottom-up search ([tools/emlsearch](../tools/emlsearch)) enumerated constant words through K 41 (21 ones) under the calculator's float semantics, twice: with ln 0 = −∞ allowed, and without it (strict). Every hit was then checked with mpmath at 100 and 700 digits (lower cut, ln 0 = −∞), and every dyadic hit also with `acceptsConstantProgram`.

This is a search, not a proof. Values are deduplicated by an 11-digit float key with three representatives per key. Programs whose float evaluation overflows or underflows are left out, as in `golf.ts`, so towers such as `11E1E1E1E` are not in the pool. A word missing here can still exist.

## What it confirms

Every record in `best-known.json` with K ≤ 41 was found again at its stated length, and **none was beaten**:

| value | with ln 0 | strict |
| --- | --- | --- |
| 0 | 7 | 7 |
| −1 | 15 | 17 |
| 2 | 19 | 19 |
| +iπ on this cut | 21 | 23 |
| −2 | 25 | 27 |
| ln 2 | 25 | 25 |
| 1/2, −1/2 | 29 | 31 |
| 3 | 29 | 29 |
| −3 | 35 | 35 |
| 1/3 | 35 | 37 |
| 4, 2/3 | 39 | 39 |
| −1/3 | 41 | 41 |

No −iπ on this cut was found through K 41, with or without ln 0, which is consistent with the K 45 record.

## New shortest-found words for values without a record

| value | K | ln 0 | word | certified by |
| --- | --- | --- | --- | --- |
| −e | 17 | yes | `11111E1EEEE11E1EE` | mpmath 700 |
| 1/e | 17 | yes | `11111E1EEEE11EE1E` | mpmath 700 |
| e + 1 | 19 | yes | `111111E1EEEE11EE1EE` | mpmath 700 |
| 1/e | 19 | no | `11111EEE1EE11E1EE1E` | mpmath 700 |
| e² | 21 | no | `111111EEE1EE11EE1EE1E` | mpmath 700 |
| e + 1 | 21 | no | `111111EEE1EE11E1EE1EE` | mpmath 700 |
| −e | 23 | no | `1111E11E1EEE1EE11E1E1EE` | mpmath 700 |
| −ln 2 | 27 | yes | `111E111111E1EEEE11EEE1E1EEE` | mpmath 700 |
| −ln 2 | 29 | no | `1111111E1E1EEE1EE11E1E1EE1EEE` | mpmath 700 |
| ±2πi | 31 | no | `111111E1E1EEEE1EE1111E1E1EEE1EE` (+), `11111E1E1EEEE11111E1E1EEEE1E1EE` (−) | mpmath 700 |
| −3/2 | 31 | yes | `1111111E1EEEE11EEE11E1E1EEE11EE` | mpmath 700, acceptsConstantProgram |
| −3/2 | 33 | no | `1111111EEE1EE11E1EEE11E1E1EEE11EE` | mpmath 700, acceptsConstantProgram |
| ln 3 | 35 | no | `1111111111EEE1EE11EEE1EE11EE1EEE1EE` | mpmath 700 |
| −2/3 | 37 | yes | `111E111111E1EEEE11EEE11E1E1EE1EEE11EE` | mpmath 700 |
| −2/3 | 39 | no | `111E111111EEE1EE11E1EEE11E1E1EE1EEE11EE` | mpmath 700 |
| 3/2 | 39 | yes | `111E1EE1111111E1EEEE11EEE11E1E1EEE1E1EE` | mpmath 700, acceptsConstantProgram |
| 3/2 | 41 | no | `111E1EE1111111EEE1EE11E1EEE11E1E1EEE1E1EE` | mpmath 700, acceptsConstantProgram |
| ±5/2 | 41 | yes | `111E1EE1111111E1EEEE11EEE11E1E1EEE11EE1EE` (+), `111111111E1EEEE11EEE11E1E1EEE11EEE1EE11EE` (−) | mpmath 700, acceptsConstantProgram |
| −5/3 | 41 | yes | `11111111E1EEEE11E1E1EEE11EEE11E1E1EEE11EE` | mpmath 700 |

The compiler builds several of these much longer. `e^2` compiles to K 45, `2*pi*i` to K 199, `5/2` to K 105, `-1/2` to K 49, `3/2` and `2/3` to K 63, and `4` to K 53. A constant-substitution pass that swaps a closed constant for its shortest known word would shorten those circuits.

## Impostors

Float64 cannot see these. They are why every hit needs a high-precision check:

- `1111EE1E1E1EE11EE` (K 17) is −1 + 4.4×10^(−114). With one representative per float key it hid the true −1, and the strict −1/2 (K 31) and 1/3 (K 37) records were missed.
- `11111111E11E1EE1EEEEEE1E1E11E1E1EEE` (K 35) is −9.0×10^(−307) − i(π − 4×10^(−307)), not −iπ. It passes a 250-digit check. Before this change `acceptsConstantProgram` accepted it as −iπ, because a ball or a 280-digit comparison cannot see a part below about 10^(−240). The certifier now also requires exact mode not to refuse the word.
- At 700 digits, 322 of the hits that passed at 250 digits fail. Their residues are between 10^(−250) and 10^(−690).

## Counts

New distinct values per length (ln 0 allowed, 3 representatives per key, so a slight overcount), against the number of programs, Catalan(n − 1):

| K | programs | new values | share |
| --- | --- | --- | --- |
| 19 | 4 862 | 2 303 | 0.47 |
| 25 | 208 012 | 71 753 | 0.34 |
| 31 | 9 694 845 | 2 435 125 | 0.25 |
| 35 | 129 644 790 | 26 183 375 | 0.20 |
| 39 | 1 767 263 190 | 284 386 204 | 0.16 |

Distinct values grow about 3.25× per extra 1, while programs grow about 3.7×. Through K 9 these counts are the 19 finite values of `reachable-values.md`'s 20 that do not overflow float64. The 20th is `11E1E1E1E`, about e^(3.8×10^6).

## Last-gate inversion to K 71

`MITM=1` builds the pool up to K 35. Then, for every value `a` and every target `t`, it computes the `b` that eml(a, b) = t needs (ln b = exp(a) − t on the lower cut) and looks `b` up among the 37 million stored values. This covers every word up to K 71 whose two halves are each at most K 35. The genuine words below passed 100 and 700 digits. Most float hits were impostors.

| value | K | ln 0 | word | note |
| --- | --- | --- | --- | --- |
| −iπ (lower cut) | **47** | no | `11111E1E1EEEE11111111E1E1EEEE1E1E1EEE1EE11E1EEE` | **new record; was K 55.** Exact mode certifies it, `acceptsConstantProgram` accepts it, and the imaginary part is −π at every precision from 30 to 480 digits. |
| −iπ (lower cut) | 45 | yes | `11111E1E1EEEE11111E1EEEE11111E1E1EEEE1E1E1EEE` | the existing record, found again |
| −4 | 53 | yes / no | `1111111E1EEEE11EEE1EE11111111EEE1EE11EEE1EE11EE1EE1EE` / `11111111EEE1EE11EE1EEE11E1E1EEE111111EEE1EE11EE1EE1EE` | |
| 5 | 63 / 65 | yes / no | `1111111111E1EEEE11EEE1EE11EE1EEE1EE1111111EEE1EE11EEE1EE11EE1EE` / `11111E1EE1111E1E1EEE11EE1EEE1EE11111E1EE11E11E1EEE11EEE1EE11EE1EE` | |
| −5 | 63 | yes / no | `111111111EEE1EE11EEE1EE11EEE1EE11111111E1EEEE11EEE1EE11EE1EE1EE` / `11111111EEE1EE11EE1EEE11E1E1EEE11111111EEE1EE11EEE1EE11EE1EE1EE` | |

No genuine word up to K 71 with both halves at most K 35 was found for π, i, √2, √3, φ, ±1/4, ±iπ/2, 2π, 6 or 10. The hand-built constructions (i at K 57, π at K 93, √2 at K 61) stand. A word whose last gate has a half longer than K 35, such as the K 39 records for 4 and 2/3, is out of reach of this pass.
