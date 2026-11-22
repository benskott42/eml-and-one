# Changelog

## 1.0.2 — 2026-11-22

Fixes from an outside review. Each one has a check.ts or golden row.

- Exact mode certifies large real and imaginary products and quotients again. v1.0.1 refused every real or pure-imaginary product or quotient past about 10^226, such as 10^400/7, 10^400·2, and 10^400·i, because the cancellation check counted the reciprocal the product passes through as if it could reach the zero imaginary part. That check now tracks small values per component. ((1+10^(−500))−1)+i/2 and i·((1+10^(−500))−1)+1/2 are still refused. This had also failed the v1.0.1 deploy, so the site still served 1.0.0.
- artanh of a real above 1 is −iπ/2 however the real was built, and arctan of iy with y < −1 is −π/2 + …i. Before, atanh(1.694^3) and atan(−2i·asinh 9) were certified on the other bank whenever the range table had no point for the argument. artanh is now Log(√(1+z)/√(1−z)), and arctan is −i·artanh(iz). Both equal mpmath's atanh and atan, on the cuts and off them. Circuits for these keys are about 5–9% longer.
- The record certifier (acceptsConstantProgram) no longer accepts a word whose value differs from the target below about 10^(−240). The K 35 word 11111111E11E1EE1EEEEEE1E1E11E1E1EEE is −9×10^(−307) − i(π − ε). Before this change it was accepted as −iπ, so a K 35 search would have published a false −iπ record.
- Presses on the page before React has hydrated were lost. The page now sets data-ready once it is live, and the browser check waits for it. That race is what failed "1, 1, EML" in CI. The handlers are also the only writers of the model ref, so an effect can no longer roll it back.
- Text was set in Times New Roman, because --font-sans was never defined. The unselected evaluation mode is now dimmed. Before, only a 3 px press told the two apart.
- A product or quotient of a huge sum with a small non-integer part, such as (10^400+i)·2 or 2·(10^400+π), is refused. Exact mode looked for the marker on such a sum only 8 gates deep, so the product word hid it and the small part was dropped. (10^400+2i)−10^400 is still 2i.
- A small component no longer prints with extra digits when its 13th and 14th places happen to be 0 (0.0199308684580096i is now 0.019930868458i). The hidden-tail display for values such as 0.5 − 10^(−72) is unchanged.
- CI runs in parallel: static checks, eml:check in 6 shards (EML_SHARD), each golden mode in 4 shards (GOLDEN_SHARD), and the site build with headless Chrome. Locally the check suite drops from 830 s to 167 s, and each golden mode from about 300 s to 90 s.
- eml:check and eml:golden --wire run on Windows: child processes use node and tsx's cli.mjs, and the wire build uses esbuild's API.
- New record: −iπ (lower cut) without ln 0 at K 47, down from K 55. tools/emlsearch found it by inverting the last gate against every value with K ≤ 35 (MITM=1).
- tools/minimality/decide.py re-derives every claim in docs/minimality.md. The original scripts are not in the repository. It reports 0 at K 7, −1 at K 15 and K 17, and 2 at K 19 as PROVED with nothing undecided.
- tools/emlsearch is a fast independent search (K 41 in about 5 minutes on 16 cores) with an mpmath checker. docs/search-k41.md lists its results. Every record with K ≤ 41 was found again at its stated length, and none was beaten.

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
