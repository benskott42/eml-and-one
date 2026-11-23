# Changelog

## Unreleased

- x^0 is 1 for every finite x, 0^0 included (the IEEE pow convention, which v1.1 uses too). It was undefined: the power word evaluates ln(0) for a zero base. An infinite base, such as ln(0)^0, stays undefined.
- Exact mode raises its precision when exp turns an angle near a multiple of π/2. Such an angle keeps only part of its digits in cos or sin. (10^108 − i)·sin(atanh(−i)) printed a real part of −0.868670961405; the value is −0.868670961486. The same raise fixes cos(1e119), which showed −0.98499 beside its "argument too large" note and now shows −0.372261757876, and certifies ((1 + 10^−130) − 1) + i/2 as 1×10^−130 + 0.5i where it used to refuse.
- Exact mode keeps a tiny imaginary part that an angle sum rounded away. (10^300 − (2 − 2i))^(−1) printed 1×10^−300 without its −2×10^−600 i. Past 480 digits, as with 10^400 in place of 10^300, the result is unverified.
- A refused subexpression refuses everything built on it. 1 + (10^400 + π) is refused, but the folds read its placeholder as an exact 0: minus 2 it was certified −2, times 2 it was 0, and a longer sum with 10^400 in it printed −1.6487 − i.
- arccos next to ±1 no longer rounds to the endpoint. arccos(1 + 10^−16) printed 0; it is 1.414×10^−8 i. arccos(1 − 10^−200) and arccos(−1 − 10^−200) kept 0 and π the same way. Next to +1 the circuit is −i·Log(z + i√(1−z)√(1+z)), so arccos(2/2) is still a certified 0.
- A value below the working precision that a sum absorbed is found again. atanh(2/exp(300)) printed 0; it is 1.0296×10^−130. Exact mode now raises the precision to fit the smallest value the pass computed when the result vanishes.
- A tiny part read twice for confirmation is read where it sits above the noise, not 24 digits higher. sin(2/exp(300)) printed −5.3×10^−261 i beside its real value (a regression from the absorbed-part fix above), and sin(x) for x = 2.77×10^−87 printed x²/2 as an imaginary part.
- An angle that lost digits in cos or sin counts those digits as noise. sinh(10^300 i) printed a real part of 4.6×10^−47; it is −0.98575042516i.
- ∞ − ∞ that no ln 0, pole, or division by 0 of the expression produced is refused, not called undefined: asinh(1/10^−200), asin(−1/10^−200), and acosh(asinh(10^400)) are finite. tanh of any real past 100 is refused, as the release notes say; tanh(10^20) and tanh(exp(800)) printed undefined, and tanh(−10^300) printed −1.
- A value that underflows the decimal range is not a certified 0: exp(−10^20), 1/cosh(10^50), and cosh(10^50)^(−2) are refused. 1 + exp(−10^20) is still 1.
- Exact mode keeps the side of a point just below the negative real axis when another function is applied to it. ln(ln(−5 − i·10^−300)) printed 1.261257534955 + 1.097357207506i; the value is 1.261257534955 − 1.097357207506i. The log's angle, −π + 2×10^−301, rounded to −π at 120 digits, a later gate snapped onto the axis, and the next log took the upper bank. Only the root's own value was checked for this before. sqrt(acosh(−2 − i·10^−120)), acos(atanh(−5 − i·10^−120)), (−1/2 − i·10^−120)^(1+i) and ln(−2 − i·10^−300) − (2+3i)^(−5) had the same flip. Exact mode now reads such a circuit again with enough digits for that angle, and past 480 digits, as with 10^−450, the result is unverified. Tiny literals such as 10^−300 do not take this path and stay at 120 digits. A tiny part that the higher-precision reading shows, and that holds still on a second reading, is kept: sqrt(−4 − i·10^−200) is 2.5×10^−201 − 2i. The record certifier now also requires a target's zero component to be certified as 0, so the K 35 word −9×10^−307 − i(π − 4×10^−307) is still not accepted as −iπ.
- Expression errors say what to type. 2pi, 2(3), and x y say "Put * between …"; sin 1 says to write sin(1); an unknown function such as abs is named as a function; 2^^3 says a value is missing before the second ^. They said "The expression has an extra symbol" or called sin an unknown name.
- An error in the x or y field names the field ("In x: …"), and an empty field says "Give x a value." It read "Enter an expression.", which points at the expression box. Errors on the screen are announced to screen readers (role="alert").

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
- +iπ on this cut is proved minimal at K 21 (with ln 0). It had been shortest known. All 6918 programs with K ≤ 19 are excluded, three tower impostors near 10^(−1656519) among them.
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
