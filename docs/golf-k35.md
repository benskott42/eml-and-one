# The K 35 constant search (2026-11-23)

`npm run eml:golf` runs `searchConstants(35)` from `lib/eml/golf.ts` twice, with ln 0 = −∞ allowed and without it, and checks the result against the records. It had not been run since v1.0. This is its run on Windows, one core per table, after the key-table rewrite listed in the changelog.

## What the search keeps

The pool is not a set of value classes. It keeps every circuit whose float value is finite and that did not overflow or underflow. v1.0 meant to keep up to four circuits per 10-digit key, but its key table compared a signed 32-bit word against an unsigned store. The fourth salt is always a negative word, so every circuit was admitted, and each repeat of a value walked every earlier copy. The rewrite stores and compares unsigned words, drops the key table for circuits nowhere near a target, and does not store circuits of the last length, which are never a child. Through K 29 the hit tables, the per-length pool counts, and the totals are identical to v1.0, with ln 0 and without it, and with the 4-way partition.

| K | v1.0 | now | peak memory, v1.0 → now |
| --- | --- | --- | --- |
| 25 | 1.4 s | 0.5 s | 106 → 86 MB |
| 27 | 7.3 s | 0.7 s | 114 → 95 MB |
| 29 | 77 s | 1.7 s | 245 → 117 MB |
| 35 | not practical | 45 s | 863 MB |

Times are with ln 0; the strict search is about the same. The v1.0 time grows with the square of each value's repeat count, so K 35 was not tried.

## Result

`npm run eml:golf` passed in 74 s (both tables, one worker thread, on a shared machine).

| value | with ln 0 | strict |
| --- | --- | --- |
| e | 3 | 3 |
| 0 | 7 | 7 |
| −1 | 15 | 17 |
| 2 | 19 | 19 |
| +iπ on this cut | 21 | 23 |
| −2 | 25 | 27 |
| 1/2 | 29 | 31 |
| −1/2 | 29 | 31 |
| 3 | 29 | 29 |
| −3 | 35 | 35 |
| −iπ on this cut | none | none |

Every word is the one in `best-known.json`, except strict 1/2, where the search reports the second K 31 word, `1111111E1E1EEE1EE11E1E1EE1EEE1E`, that the 1/2-strict record already names. No record was beaten. No −iπ on this cut was accepted through K 35, which is consistent with the K 45 and K 47 records, and neither K 35 −iπ impostor in check.ts was accepted.

The pool through K 35 is 88 041 356 circuits with ln 0 and 63 503 930 without it. The last length alone is 62 868 184 and 44 953 839. These are programs, not distinct values: [search-k41.md](search-k41.md) counts 26 183 375 new values at K 35.

This is a search of the float-finite pool, not a proof. A program whose float evaluation overflows or underflows is not in the pool, as in [search-k41.md](search-k41.md), so a shorter word can still exist.
