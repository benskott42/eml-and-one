# Changelog

## 1.0.0 — 2026-11-15

First version of EML and One, a two-button calculator.

- Exact mode is the default. It is 120-digit decimal arithmetic, raised up to 480 digits when a cancellation would hide a value. Within one working precision, a residual below about 10^(−(digits−8)) relative to its operands is treated as 0. That is not a fixed snap at 10^(−112). A known magnitude of 10^(−432) still resolves. 10^(−433) says it could not verify. It is not symbolic. It runs off the main thread, the screen says computing, and Cancel clears the result. A newer exact expression pre-empts the one already running.
- Float is a hardware view of the same gates. When it disagrees with exact beyond what float can claim, the float stays on screen and the exact value is shown beside it.
- arcsin, arccos, and arsinh share one principal branch in both modes. A real greater than 1 has arcsin equal to π/2 − i·arcosh(x).
- Variable subtraction and addition use one shared scale and ln 0 = −∞. Phase-free infinities are not enough for a zero partner: b = 0 needs a directed infinity, and sub(5, 0) and add(5, 0) are NaN in the phase-free model.
- 0 at K 7, −1 at K 15 (using ln 0) and at K 17 (without ln 0), and 2 at K 19 are proved minimal. The proof is computer-assisted and is summarized in docs/minimality.md. Every other record is shortest known. +iπ at K 21 and K 23, and −2 at K 25, are shortest known. Dependence on ln 0 = −∞ is stated on the record. Nothing in this version depends on Schanuel's conjecture. 3 at K 29 is a tie with an earlier code-golf answer, not a first discovery.
