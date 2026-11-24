# Known limitations

This is the v1 list of what is unfinished. None of it blocks the calculator. 0 at K 7, −1 at K 15 (using ln 0) and at K 17 (without ln 0), 2 at K 19, +iπ at K 21 (K 23 without ln 0), and −2 at K 25 (using ln 0) are proved minimal. Without ln 0, every K 25 program but two is excluded as −2. The proof is computer-assisted and is summarized in [docs/minimality.md](minimality.md). Every other length here is shortest known. A record that uses ln 0 = −∞ says so. No claim in this release depends on Schanuel's conjecture. A later identity that does will say so in the same place as the claim.

## Records

−iπ at K 45, 4, 2/3, −1/3, −3, and both 1/3 words are stored in `best-known.json`. −iπ at K 45 is not the K 21 word: that word is +iπ on this cut and −iπ under the principal log. −iπ at K 47 does not use ln 0. −iπ at K 45 and 1/3 at K 35 use ln 0 = −∞. 1/3 at K 37 does not. None of those lengths is proven minimal.

Scaled variable subtraction is K 565 and scaled variable addition is K 655. Both are the current constructions, shortest known, and both depend on ln 0 = −∞. Neither is proven minimal. +iπ at K 21, and at K 23 without ln 0, is proved minimal (tools/minimality/decide.py --open). −2 at K 25 with ln 0 is proved minimal (decide.py --open --deep: the tower programs that turn on a phase take tools/minimality/deep.py, runs of up to 5.5 million bits, the whole run takes about 80 minutes). Without ln 0, −2 at K 27 is shortest known: 2 K 25 programs remain undecided, exp(exp(exp(T4/z))) and exp(exp(T5/z)) (words `11E1E1111E1E1EEEE1E1E1E1E` and `11E1E1E1111E1E1EEEE1E1E1E`). Each is −2 only if the phase of a tower of towers, such as Im exp(T4/z) mod 2π, is within 10^(−1000) of ±π/2, and no enclosure reaches that phase. The other 15 that were undecided are excluded.

Phase-free infinities do not make subtraction or addition work at b = 0. sub(5, 0) and add(5, 0) are NaN in that model. b = 0 needs a directed infinity. artanh of a real greater than 1 is ½ ln|(1+x)/(1−x)| − iπ/2, matching mpmath's atanh. C99 catanh of that real with a +0 imaginary part returns +iπ/2.

## Float

Float is a hardware view of the same gates. It is not patched toward the exact value. The screen compares the real and imaginary parts separately. With 12 digits shown, a relative error of about 5×10^(−12) or larger on either component is flagged, and so is a component that float dropped. Within one working precision, a residual smaller than about 10^(−(digits−8)) relative to its operands is treated as 0. That precision starts at 120 digits and rises, up to 480, when the rounding would hide a value. It is not a fixed snap at 10^(−112). A known magnitude of 10^(−432) still resolves. 10^(−433) is past the cap, and the screen says it could not verify. A power such as 10^(−400) records its decade when that still fits in 480 digits, and division carries that decade, so ln(1+10^(−400)), 0−10^(−400), and 0−1/10^400 keep the small term instead of a confident 0. Past that cap, 0−10^(−500) is negation and still prints the value. A logarithm the circuit collapses, such as ln(1−10^(−500)) or ln(1±exp(−1000)), says it could not verify instead of a confident 0. An exact 0 times a finite factor stays a certified 0. A finite result far below a value past float range is refused unless an enclosure of the circuit confirms it: ln(10^400), ln(10^(−400)), √(4×10^(−400)) and hypot(−10^(−200), 3×10^(−200)) are certified, (exp(800)+1)−exp(800) is not. hypot(2×10^(−160), 1) and hypot(10^160, −1) still say they could not verify: their circuits pass through a 0 that only the gates' snap makes exact, and the enclosure cannot take ln of a 0 it cannot prove. A sum or difference of decimal literals that comes to 0, such as 0.1 + 0.2 − 0.3, is an exact 0; 1/10 + 2/10 − 3/10 is not, because quotients are not followed. Some deep towers whose extra term is far below working precision (e.g. the word 111E1E1E1EE11EE, which differs from -1 by about 10^(-1656520)) can display as an exact value with no flag; an absorbed-term check is planned for v1.1. For words lying on the negative real axis (e.g. 111111E1EEEE11E1E1EEE), the display can show +i*pi without a branch-cut note. A compare that hits the node limit says the same, and a too-large circuit does not also say it left the finite numbers. A zero that a series shortcut produced is not certified. An infinity whose finite partner a gate drops, such as ln(ln(0))·i (−π + i∞) or exp of it (no limit), is not certified; so is any value computed from one, finite or not, even where it is right, such as 1/(ln(ln(0))·i).

These float results stay wrong, and the flag is what publishes that. There is no second float formula for them:

- A variable just off the cut, with |x| > 1 and |eps/x| ≤ 10^(−15), at 17 points of arcsin, arccos, and arsinh.
- A dropped component, including exp(10^(−9) i) − 1 and 10^300 + i. Scaling keeps (10^(−90) i) − 2×10^(−90) within the displayed digits.
- tan(50000), whose float and the exact value differ in the later of the 12 displayed digits, and exp(10^(−6)) − 1.
- A series shortcut keeps a leading term only when the next term is past the 480-digit cap. That is |x| ≤ 10^(−241) for sin, tan, tanh, arctan, and cos(x)−1, and |x| ≤ 10^(−480) for ln(1+x), exp(x)−1, and sqrt(1+x)−1. Sin keeps odd powers for |x| ≤ 10^(−61). tan, tanh, and arctan keep odd powers, and cos(x)−1 keeps even powers, for |x| ≤ 10^(−20), until the next term is past the cap. A larger argument stays on the real circuit. tan(10^(−20)) is that series, so float and exact agree on the displayed digits. A one-digit literal such as tan(1e-5000) or exp(1e-1000)−1 prints that value, because the significand is 1 and the exponent is stored. The power spellings tan(10^(−5000)) and exp(10^(−1000))−1 do not resolve inside the cap, so they say could not verify rather than 0. cos(10^(−200))−1 keeps the even powers that start with −x²/2. Float still underflows that square, so the flag stays.
- Variable asinh of ±10^(−12), which leaves a float residual of about 10^(−15). Below about 10^(−12) the low-precision flag is also set.
- tan(π/2) and tan(3π/2), labelled near a pole in both modes. The digits of a near-pole float still depend on the engine.
- sin, cos, and tan of a real at least 10^6, because float π cannot reduce them.
- A real part around 1.3×10^154 or larger, where the shared scale overflows and x − y is undefined.
- ln(−2 − 10^(−20) i) and ln(−2 − 10^(−35) i), which show +iπ in float and −iπ in exact and are flagged as near the cut.

What the flag does not catch:

- A relative error at or below about 5×10^(−12) on a component. That is one digit past the 12 on screen. A few ulps, and 0.1 + 0.2 − 0.3, sit in this band.
- In float mode, sinh(+-0.00005i) can show a -1e-16 real part below the flag threshold.
- 0 minus the smallest positive float, 5×10^(−324). Float keeps a signed zero and exact keeps 0. The comparison treats those magnitudes as equal.
- 1 − 10^400 is NaN in float. That is overflow, not a value the flag replaces.
- A cancellation whose size is not visible in a known leaf and not visible as a residual at 120 digits can still agree with float. The reference does not search every expression for a hidden scale.

## Circuits and search

- Rebuilding a circuit from its press string drops the low-precision, pole, and large-angle flags. Those notes sit beside the node, not in the gates.
- The fast suite stops at the K = 21 table (K 23 without ln 0). `npm run eml:golf` runs K = 35 in about 75 s and is not part of the publish check; its last run is in [docs/golf-k35.md](golf-k35.md).
- The constant search does not merge circuits by value. Its pool is every float-finite circuit that did not overflow or underflow, 88 M through K 35 with ln 0, so K 37 and past are left to tools/emlsearch.
- 0, −1, and 2 tie the lengths in arXiv:2603.21852. ±iπ at K 21 was posted publicly before this project. 3 at K 29 ties an earlier code-golf answer. Those are not claimed as first discoveries. The citations are in the EML and One README.
