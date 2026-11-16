# Why the counting construction gives exactly n

Keys: `1` pushes 1. `E` pops y, then x, and pushes eml(x, y) = exp(x) − Log y. K is the number of presses.
Convention: lower cut, Arg in [−π, π) (Log of a negative real takes Arg −π); ln 0 = −∞ where a word allows it. The words below never take ln 0, and their value is the same under the principal Log.

## n ≥ 2: K = 10n − 1
word(n) = `1`^(2n+2) · (`EEE1EE11`)^(n−1) · `EE1EE`.

Write c_k = e − k. Before each block the stack is [1, …, 1, L, 1, 1] with e^L = c_k. The prefix gives c_0 = e. The block's steps are:
- `E` gives e;
- `E` gives eml(L, e) = e^L − 1 = c_{k+1};
- `E` gives e − Log c_{k+1};
- `1E` gives e^e / c_{k+1};
- `E` gives L' = e − Log(e^e / c_{k+1});
- `11` pushes two ones.

L' equals Log c_{k+1} only up to a multiple of 2πi; they differ when c_{k+1} < 0, that is when k + 1 ≥ 3. But L' is used only through exp, so e^{L'} = c_{k+1} exactly, on either cut. Since c_k ≠ 0 (e is irrational), ln 0 never occurs. On [1, L, 1, 1], the tail `EE1EE` outputs e + 1 − e^L = e + 1 − (e − (n − 1)) = n. ∎

This gives 2 at K 19, 3 at K 29 and 4 at K 39, the same words as the table's 2, 3 and 4.

## n = −m ≤ −1: K = 10m + 7
word(−m) = `11`^m · `111` · (`EEE1EE11`)^m · `E1EE`.

The invariant is the same: after m blocks the stack is [L, 1, 1] with e^L = e − m. The tail then gives e^L − Log(e^e) = e − m − e = −m, on both cuts, with no ln 0. ∎

This gives −1 at K 17 and −2 at K 27, the same lengths as the integer table's words without ln 0. It is longer than the table's words for −3…−9 (K 35, 45, 55, 65, 75, 77 with ln 0, 79).

## n = 1 and n = 0
- 1 is the `1` key (K 1).
- 0 is ln(1) via the ln template `11xE1EE` with x = 1: `111E1EE` (K 7).

These are constructions. A length is called minimal only where best-known.json and the README (see docs/minimality.md) say it is proved: 0, −1 and 2. Lower cut, Arg in [−π, π), ln 0 = −∞; on this cut −iπ becomes +iπ under the principal Log.
