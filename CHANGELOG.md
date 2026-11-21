# Changelog

## 1.0.1 — 2026-11-21

Exact-mode fixes. A result is either right or says it could not verify; none of these is certified wrong any more.

- A tiny angle is no longer snapped to the axis: exp(6.103515625×10^(−120) i) keeps its imaginary part.
- A repeat evaluation matches the first one: the pure cache keeps each subtree's cancellation, smallest value, and series-shortcut notes, and the large-argument, pole, and precision notes come back on a cache hit. EML_NOCACHE is read on every evaluation.
- The worker path carries the asinh and addition precision notes.
- A tiny real part beside an imaginary one, such as ((1+10^(−130))−1)+i/2, is kept.
- Refused rather than certified (exact mode says it could not verify; float keeps its own value): sin, cos, or tan of an angle past 10^15 anywhere below the root, such as −cos(10^119) or cos(10^119)+1; a part cancelled to 0 beside a nonzero part after a value too small for the precision, such as ((1+10^(−500))−1)+i/2; a finite result far below an overflowed operand, such as (exp(800)+1)−exp(800), and exp(800)·0; sinh(z)−z, artanh(z)−z, and arcsin(z)−z where the small-argument shortcut drops the cubic; tanh of a real past 100, which rounds to ±1.
- A repeat of sin(10^22), tan(10^22), cos(10^7), or cos(2^60) keeps "argument too large to reduce".
- A circuit that shares a subtree at every level no longer copies its cancellation records once per path.
- exact-zero residues, tiny sums lifted to full size, and an infinity whose finite partner a gate drops are no longer certified.

## 1.0.0 — 2026-11-15

First version of EML and One, a two-button calculator.

- Exact mode is the default. It is 120-digit decimal arithmetic, raised up to 480 digits when a cancellation would hide a value. Within one working precision, a residual below about 10^(−(digits−8)) relative to its operands is treated as 0. That is not a fixed snap at 10^(−112). A known magnitude of 10^(−432) still resolves. 10^(−433) says it could not verify. It is not symbolic. It runs off the main thread, the screen says computing, and Cancel clears the result. A newer exact expression pre-empts the one already running.
- Float is a hardware view of the same gates. When it disagrees with exact beyond what float can claim, the float stays on screen and the exact value is shown beside it.
- arcsin, arccos, and arsinh share one principal branch in both modes. A real greater than 1 has arcsin equal to π/2 − i·arcosh(x).
- Variable subtraction and addition use one shared scale and ln 0 = −∞. Phase-free infinities are not enough for a zero partner: b = 0 needs a directed infinity, and sub(5, 0) and add(5, 0) are NaN in the phase-free model.
- 0 at K 7, −1 at K 15 (using ln 0) and at K 17 (without ln 0), and 2 at K 19 are proved minimal on the lower cut, Arg in [−π, π), with ln 0 = −∞. On this cut −iπ becomes +iπ under the principal Log. The proof is computer-assisted and is summarized in docs/minimality.md. Every other record is shortest known. +iπ at K 21 and K 23, and −2 at K 25, are shortest known. Dependence on ln 0 = −∞ is stated on the record. Nothing in this version depends on Schanuel's conjecture. 3 at K 29 is a tie with an earlier code-golf answer, not a first discovery.
