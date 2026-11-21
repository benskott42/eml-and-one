# Design: ball arithmetic as the exact engine

Status: design only. No engine change in this PR. Branch base: `main` at `d6be0d1`.

`lib/eml/enclose.ts` becomes the exact engine. A result is a complex ball. A ball proves digits, a sign, or nonzero. It never proves an exact 0, an exact integer, or a point exactly on an axis or the cut. Exact 0 is a structural zero whose radius is 0. Any other ball that contains 0 prints a labelled bound, "0 to N digits", when both ends of the interval round to that text. It is not the exact 0 that today's dust and snap-to-zero would print. The cutoff "certified 0 means both intervals lie inside `10^(-480)`" is dropped. That rule would show `1e-500` and `exp(-1200)` as exact 0, which is a severity-1 false certificate, and it would still miss `1-1`: at the 480-digit cap the cancellation radius is about `10^(-478)`, larger than `10^(-480)`.

EML builds `0`, `−1`, `i`, `π`, and negatives through `ln 0` and the cut. The seed's overflow on `−1`, `−2`, `i`, `π`, and `ln(−1)`, and its cut on `1e-500`, `exp(-1200)`, and `1e-400*(1+1e-100)-1e-400`, are the refusals the log and cut rules below already require. The exact layer is what certifies the points. This rewrite does not add functions and does not widen any domain (review E6). A case the ball cannot decide stays unverified. It does not grow a new approximation.

## 1. Scope and non-goals

In scope: the exact-mode decision and the digits it prints, for the circuits the calculator already builds. The float evaluator stays the float evaluator. Constant search keeps enumerating with float.

Out of scope:

- New functions, new identities, or a wider domain for an existing one (E6).
- Porting the absorbed-term retry from #33. That PR did not merge, and `main` does not have the retry (`docs/known-limitations.md` only plans it). A term inside the radius widens the ball. That is the replacement.
- Changing the lower-bank cut. Arg on the negative real stays −π, matching `lib/eml/complex.ts` and the head of `exact.ts`.
- The golf pool. `searchConstants` never asks the exact engine for the millions of rejected circuits. Only a watched constant confirm calls `enclose` today (`golf.ts`).

## 2. What `exact.ts` does today, and what replaces it

Working precision starts at 120 (`PRECISION`) and stops at 480 (`PRECISION_CAP`). `Decimal.clone` at `exact.ts:42` is a module global. `exactReport` (`:571`) walks the circuit once, then runs several repairs. `atPrecision` (`:389`) re-enters `exactReport` at `pass = 2`, which returns before the repair loop.

| Mechanism | Where | Under balls |
| --- | --- | --- |
| Precision passes | 120, then raised by gap, tiny leaf, or hidden component | One adaptive loop. Double the precision until the ball decides or the cap is hit. No separate repair passes. |
| `cosSin` snap (`:75-87`) | An angle within tolerance of `k·π/2` becomes that axis | The snap goes away. A ball inside the tolerance is the axis value plus a remainder ball. The remainder is not cleared, so the result is not a point on the axis. An exact axis point comes from the exact layer. |
| `axisInfinity` (`:89-94`) | A component of an infinity smaller than `1e-15` becomes signed 0 | Each part is its own interval. That interval may be finite, or it may be the exact point `+∞` or `−∞` with that sign. The `1e-15` snap goes away. |
| `scrubDust` (`:252`) | A component far below its sibling is cleared to a certified 0 | The radius stops that digit from printing. Clearing it to 0 is the snap this design drops. A component interval that contains 0 is a labelled bound or undecided, never exact 0. |
| `lossGap` / `tiniest` (`:195`, `:197`) | A cancellation or a tiny nonzero raises precision, up to the cap. `certifyZero` (`:469`) then prints a certified 0 | The globals go away. A ball that excludes 0 certifies nonzero. A ball that contains 0 stays a labelled bound or undecided at every precision, including the cap. Nothing in the loop promotes it to exact 0. |
| `hiddenComponent` (`:411`) | One component is 0 and the other is huge (`10^300 + i`), and the 0 is kept | The small interval contains 0, so that component is a labelled bound or undecided. The huge component can still certify its digits. The screen must not print the small one as exact 0. |
| `confirmDust` (`:454`) and `settleResidue` (`:514`) | Re-run at +24 or +96 digits and keep a part only if it does not move | The adaptive loop is this re-run. A part that "moves" is a radius that was too small for the claim. |
| `pureCache` (`:307-310`, hit `:747`, store `:804`) | `{value, why, logged, work}` by node, per precision. A hit does not restore `lossGap`, `tiniest`, or `sawLead` | Cache the ball inside the evaluation context. The key is the node, the precision, the variable bindings, and the node's context facts. A hit returns the ball that walk would have built under those same bindings and facts. |
| Absorbed-term retry | Not on this SHA. #33 did not merge. Its draft certified values whose lost term sat in an exact-0 component | Not ported. `1 + 10^(-130)` is a ball whose radius is at least that term. It is not the integer 1. |

Side-table facts that the point engine reads (`wire.ts` carries the ones the worker must see):

| Fact | Role today | Under balls |
| --- | --- | --- |
| `decades` | A known power of ten, so a later pass can see `10^(-400)` | A hint for the starting precision, so the loop does not double from 120 up to 400. Not a certificate. Missing hint: the loop still runs to the cap. The hint is part of the cache key. |
| `lostTiny` / `cap` | A term past 480 digits. A vanished result is not a certified 0 | The cap still stops the loop. A ball that contains 0 at 480 digits is a labelled bound or undecided, never exact 0. Today's snap of a vanished value to 0 does not survive. The flag is part of the cache key. |
| `scaledShell` | Lift gates are left out of the noise exponent | The lift is ordinary arithmetic. The radius of the quotient is the proof. Delete the mark when decisions switch. Until then it is part of the cache key. |
| `lead` (series shortcut) | The circuit was replaced by a leading term. A zero from that replacement is not certified. A nonzero leading term is printed | Taylor polynomial plus a remainder ball that is valid on the complex rectangle. The boolean is not a certificate. It is part of the cache key. |
| `unver` | The builder dropped a term, or a `beside:` integer mul must not be certified (`hidesBeside`) | Remainder balls cover the shortcuts. `beside:` stays: it is a structural refusal, not a radius. The unverified placeholder is never rewritten as the point 0. The mark is part of the cache key. |
| `int` / `provenInteger` | The leaf is an integer the float has already rounded | Stays, as an exact point: the builder recorded the integer, so the leaf has radius 0. A computed ball is not an integer, whatever integer its center is near. |

`piCoeff`, the series-arg maps, `realSum` / `realSub`, and the other build-only tables in `library.ts` and `lowering.ts` choose which circuit is built. They are not exact-mode certificates. This design does not merge them.

## 3. The ball

The model is the rectangle. A disk is not used. The seed already stores a rectangle and then inflates `cexp` with `rr+ir`, an upper bound on the half-diagonal; the signed bounds are written for the rectangle itself.

```
{ re, im, rr, ir }   // center (re, im), radii rr, ir ≥ 0
```

The set is `[re−rr, re+rr] × [im−ir, im+ir]`. Each part is its own interval. Either interval may be a finite segment, or the exact point `+∞` or `−∞` with that sign. That replaces `axisInfinity` (`exact.ts:89-94`), which snaps a component smaller than `1e-15` to signed 0. A finite residual beside an infinity stays in its interval. It is not cleared.

`decimal.js` defaults to `ROUND_HALF_UP` (`Decimal.rounding === 4`, confirmed on this tree). That mode is not an outward rounding. Radius steps run on a separate clone, at low precision, with rounding directed upward. The high-precision clone that builds the center is not that clone. Every elementary error is added to the radius as an absolute quantity on the outward clone. A relative factor that rounds away, and one ulp of a final multiply, are not a charge. `cos` / `sin` of a large argument include the absolute error of reducing modulo π. `atan2Fast` (`exact.ts:144-156`, the float seed plus the odd series at `:158-192`) is excluded from any certified argument. It stays out until a signed bound covers the seed and the series. The seed's `D.atan2` is the function a bound has to cover; the fast path is not a substitute.

`cexp` as seeded (`enclose.ts:52-63`) sets the center to `exp(re)·(cos im, sin im)` and the radius to `exp(re+rr)·(exp(rr+ir)−1)` plus one ulp of the output, on both axes. The Lipschitz shape is the right one: `|e^(z+δ) − e^z| ≤ e^(Re z) (e^(|δ|) − 1)`. The seeded line is not yet a proof. It charges one ulp at the end and none for `exp`, `cos`, `sin`, or the two multiplies, and it ignores argument reduction. That is B3. Until mathbot signs a bound, `cexp` stays a shadow. It must not certify.

Other ops, same standard:

- Add and sub: radius is the sum of the radii plus the absolute rounding error of the sum, charged on the outward clone. The seed's `cadd` is the pattern, once that charge replaces its half-up ulp.
- Mul and div: not in the seed (`enclose` only implements `exp(a) − ln(b)`). Needed once shortcuts and scalings are balls rather than rewritten gates. Bound is the usual product of centers and radii, plus absolute errors, with div refused when the denominator rectangle contains 0.
- `ln`: the seed returns overflow when the rectangle contains 0 (`mag ≤ rr+ir`), and a cut ball when `straddlesCut` says the rectangle meets both imaginary signs and the negative reals. Log of a ball that contains 0 is undecided, not −∞. The extended value `ln 0 = −∞` applies only to a structural zero of radius 0. A computed ball whose center rounded to 0 is not that point.
- Cut, lower bank (B4). On the negative real this engine uses arg = −π. Just above that ray, arg is near +π. A rectangle that only touches the ray from above (`im` interval `[0, ε]`, real interval meeting `(−∞, 0)`) does **not** trip `straddlesCut`, because that test demands a strictly negative and a strictly positive imaginary part (`enclose.ts:71`). Touching the closed ray is already two values a full turn apart. Such a ball is a cut, same as a ball that crosses. A ball strictly off the ray keeps a bounded `atan2`, not `atan2Fast`. A ball never proves that a point lies exactly on the cut.
- Infinities and poles. A non-finite center or a non-finite radius from rounding is overflow, not a number. A certified infinite part is an exact point `+∞` or `−∞` from the exact layer, one part at a time. A pole of `tan` is the angle ball meeting an odd multiple of `π/2` while also meeting points that are not that multiple: unverified, which matches today's pole flag. Containment in a pole tolerance does not prove the angle is that multiple.
- Series (B1/B2). The shortcuts in `library.ts` (`SERIES_ODD` −241, `SERIES_POLY` −61, `SERIES_WIDE` −20, `SERIES_REL` −480) become a Taylor polynomial evaluated as a ball, plus a remainder bound in the radius. The remainder has to be valid on the complex rectangle. "At most the next term" holds for a real alternating series and does not transfer to a complex ball. If the signed remainder still forces both ends of an interval to the same digit text, those digits are certified. If the remainder ball contains 0, the result is a labelled bound or undecided, never exact 0. That replaces today's "past the cap" outcome, without a lead flag and without printing a truncated term as exact.

### Exact layer

The ball refuses a point it cannot enclose. The constants the calculator actually builds are such points, because their circuits pass through `ln 0` and the cut. A small exact layer sits beside the ball and supplies only these points:

- A structural zero, radius 0. This is the only exact 0.
- An exactly-zero imaginary part the builder has proved, as the exact point 0 on that part.
- The points `+0`, `−0`, `+∞`, and `−∞`.
- An integer leaf the builder recorded (`int` / `provenInteger`), radius 0.
- `ln(exp x) = x` only when `Im x` is proved to lie inside `(−π, π)`. A ball that merely overlaps that strip does not fire the identity.

The unverified placeholder never becomes the point 0. A dropped term stays unverified.

This layer is why the seed may overflow on `−1`, `−2`, `i`, `π`, and `ln(−1)`, and may cut on `1e-500`, `exp(-1200)`, and `1e-400*(1+1e-100)-1e-400`, and still be right. Those are the log and cut rules above. The layer certifies `0`, `−1`, `i`, `π`, `ln(−1)`, and the other negatives. It does not turn a positive-radius ball into exact 0, so the three cut rows stay refusals.

## 4. Decisions, digits, adaptive loop

Every numeric claim a ball makes is containment of an inequality. `cut` or overflow refuses every numeric claim. A timeout does the same and shows "couldn't verify".

- **Digits.** Print `n` digits of a part only when both ends of that part's interval round to the same text. This is an inequality (the value lies in that decimal interval), not a claim that the center is exact. A half-unit test on the radius is not the rule: the two ends can round apart inside it. Digits past the radius are not stored and not shown. `sin(10^22)` prints as many digits as the argument-reduction bound actually proves, which may be none.
- **Labelled bound.** When both ends round to 0 for `N` digits, the screen prints "0 to N digits". That is the bound. It is the replacement for a certified 0 that came from dust, a cancellation snap, or a vanished value. `1e-500` and `exp(-1200)` may wear that label once a signed ball exists. They are never exact 0.
- **Nonzero and sign.** If the rectangle excludes 0, the value is certified nonzero. If a part's interval lies in a half-line (`Re > 0`, `Im < 0`, and so on), that sign is certified. An exact infinite sign is the exact-layer point, not a ball that overflowed.
- **Integer.** An integer is an exact point or a structural proof: the recorded integer leaf, radius 0. A ball does not become an integer by lying near one. `2.3 ± 0.1` lies inside `(1.5, 2.5)` and is not the integer 2. `1 + 10^(-130)` is not the integer 1.
- **Exact zero.** Only a structural zero of radius 0. The rule "both intervals inside `10^(-480)`" is dropped. It would certify `1e-500` and `exp(-1200)` as exact 0. It would also fail `1-1`, whose radius at the cap is about `10^(-478)`. There is no separation bound in this design that would let a class of tiny balls count as zero.
- **Couldn't verify.** The claim is not forced: a cut, an overflow, a timeout, or a radius whose two ends still round to different text at the cap. Containing 0 is never read as exact 0. That is the break with today's dust and snap-to-zero (`scrubDust`, a cancellation cleared to exact 0, a vanished value kept as 0).
- **Differs from float.** Unchanged comparison, against the ball rather than a point. Float differs when its displayed value lies outside the ball (plus the existing 12-digit slack). A ball that is itself unverified does not accuse the float. A float 0 against a labelled "0 to N digits" is not a disagreement the ball can settle.

Per component, not only for the complex value. A tight imaginary interval and a real interval that contains 0 certify the imaginary digits and leave the real part as a labelled bound or undecided. They do not print a real exact 0. Whether the screen shows the good component beside an undecided one does not block the switch. The bug to forbid is the one #33 proposed and did not merge: printing `0.5i` as a match while the real part was dropped.

Adaptive loop, one place, replacing every retry:

1. Start at 120, or at the decade hint when that is higher. Stop at 480.
2. Enclose at that precision. The deadlines are the ones the Chrome job already uses: 15 s for an ordinary value, 30 s for a slow one.
3. If the claim is decided (shared digit text, a labelled "0 to N digits", a nonzero or a sign, a cut, or an overflow), stop. A ball that still contains 0 is not an exact 0.
4. Still ambiguous at 480, or the deadline fired: "couldn't verify".

No second policy for dust versus residue versus a hidden component.

## 5. Fit with D3

One context per evaluation, passed down, not module globals:

```
{ precision, rounding, cache, bindings, facts }
```

`cache` maps `(node, precision, bindings, facts)` to a ball. `bindings` are the variable values for this evaluation. `facts` are the marks the walk already consults: `unver`, `lead`, `cap`, `decades`, `scaledShell`, `int`, and the trig and pole notes. The hit at `exact.ts:744-747` shows why the node alone is the wrong key: a cached exp-formula value is recomputed when the argument is infinite, because the same node is not the same claim in every context. The store at `:803` only skips nodes that contain a variable. It does not key the marks. Both have to be in the key. A hit returns the same ball the walk would have built. `lossGap`, `tiniest`, `emlWork*`, and `sawLead` are not in the context. They described a point evaluation.

The worker and the main-thread fallback each build their own context. They already do not share `exact.ts` globals, because a worker is another realm. `D.set` goes away as a process-wide side effect. The context owns two `Decimal` clones. The center clone keeps the working precision. The radius clone is the separate low-precision clone that rounds upward. Nested re-entry is just another context. It cannot clobber the caller's precision.

`hasVarOf` can stay a per-context memo or be recomputed. It is not a ball.

Lines a later patch will touch, and that bigfixer is also touching: `cosSin` at `exact.ts:75-87`, and the `pureCache` hit and store at `:747-754` and `:804`. The shadow PR should land beside those, not inside them, until that work settles.

## 6. Migration

The gate is the golden harness in #41. It compares display text, status, reason, the differs-from-float flag, and per-part digits. `eml:check` stays as the regression net for everything already locked.

The corpus includes the #33 repros, the cancellation family `k = 110..136` with the constants `{1/2, 1/3, 3/2, −1/2}`, `tan(1e100)`, `cos(1e100)`, `sin(1e22)`, `tan(1e22)`, `cos(1e7)`, the tiny-imaginary Chrome set, `ln(1+10^(-130))`, and the exact-layer rows `0`, `−1`, `i`, `π`, `ln(−1)`, and the other negatives.

A line may move from certified to unverified only when this section lists it. Any value change, and any new certification, needs an mpmath or Arb check at 2000 digits or more, named in that PR. The fuzz bar is zero false certifications: an unverified result is allowed, a certified digit, sign, nonzero, or exact point that is false is not.

**(a) Shadow.** Run the ball decision next to `exactReport`, in CI only, in three settings: in-process, a fresh process over the packed wire (`scripts/fresh-exact.ts`), and a Chrome Worker (`lib/eml/exact.worker.ts`). The screen keeps today's text. The golden file is recorded from today's engine first, so the shadow PR changes no golden line. If the packed token changes, that PR adds or bumps `WIRE_VERSION` in `lib/eml/wire.ts`, and all three runners refuse a mismatch. The tree has no such constant today.

**(b) Switch.** The screen and the returned decision follow the ball and the exact layer. This waits on mathbot's sign-off of the blocking questions in §8, and the same PR updates `README.md`, `docs/known-limitations.md`, and the UI. Those three still say a small residual is treated as 0 and that an exact 0 times a finite factor stays a certified 0. The UI prints "0 to N digits" for a labelled bound and keeps exact 0 for a structural zero of radius 0. The golden file moves only on lines listed below, each with the 2000-digit check when the value or the certification changes.

**(c) Delete.** After the switch, each old mechanism stays in CI as a reverse shadow. One mechanism is removed per PR, and only after that reverse-shadow period. The mechanisms are `scrubDust`, `confirmDust`, `settleResidue`, `hiddenComponent`, the `lossGap` / `tiniest` retry, the `cosSin` point snap, and the `axisInfinity` `1e-15` snap. Float evaluation stays.

Expected disagreements, current engine wrong, ball right once the bounds are signed. Each of these is a listed certified-to-unverified line, or a listed digit change, and each needs the 2000-digit check:

- `((1+10^(-k))-1)+i·c` for `k` in 110..136 prints `c·i` and drops the real `10^(−k)`. Measured on this SHA: `((1+10^(-130))-1)+i/2` prints `0.5i`, `((1+10^(-136))-1)+i*3/2` prints `1.5i`, `((1+10^(-110))-1)+i*10^10/3` prints `3333333333.33i`.
- `(i*(1+10^(-124))-i)*i+i*10^10/3` prints `3333333333.33i` and drops the real `−10^(−124)`. Same on `(i*(1+10^(-130))-i)*i+i/2`, which prints `0.5i`.
- `sin` / `tan(10^22)` and `cos(10^7)` print a dozen digits the reduction does not justify. Fewer digits, or unverified, is the expected change. Matching the point engine's digits with a huge radius is a failed display rule.
- `tan(1e100)` and `cos(1e100)` are the same class.
- `1-1` is a certified 0 today by snap. After the switch it is "0 to N digits" unless a recorded rewrite has already reduced it to a structural zero of radius 0. Keeping today's exact 0 would be the dropped rule coming back.

Rows the exact layer must keep certified, because the ball's refusal is correct and the point is structural:

- `0`, `−1`, `−2`, `i`, `π`, `ln(−1)`, and the other negatives. The seed overflows on these. That matches the log rule: the circuit goes through `ln 0` or the cut, and a ball must not invent the point. The exact layer is the certificate. Losing the certified value is a regression.

Rows the seed refuses correctly, which stay refusals:

- `1e-500`, `exp(-1200)`, and `1e-400*(1+1e-100)-1e-400` come back `cut`. That matches the cut rule. They are not exact 0, and the exact layer does not make them so. A later signed ball may print "0 to N digits". Printing exact 0 here is the severity-1 failure the `10^(-480)` cutoff would have shipped.
- `ln(1+10^(-130))` and `sin(pi/6)` come back `cut` and overflow from the same rules. They are not seed bugs to patch so the ball prints today's text. `sin(pi/6)` stays `0.5` once `π` is an exact point and a signed bound forces both ends to that text. `ln(1+10^(-130))` stays `1×10^−130` once a remainder valid on the complex rectangle does the same. Until that bound is signed, an unverified result is a listed line, not a quiet fix.

`1+1` stays the digits `2`. The seeded ball has radius about `10^(-297)` and both ends round to that text. That is a digit claim. It is not a certificate that the value is the integer 2; the integer, if claimed, comes from the exact layer.

On this corpus the seed is not ready to switch. Of 37 expressions, 35 came back `cut` or overflow and left the walk early, including `exp(1e-6)-1` and the identities above. The cancellation rows came back `cut`, which is the right refusal to print `0.5i`. A cut caused by a blown `cexp` radius is not yet a proof that the real part is ambiguous. Shadow mode has to separate those, and the exact layer has to be present before the constant rows are judged.

## 7. Performance

Throwaway timing on this SHA, cold process, no ball cache. `exactReport` against `enclose` at its fixed 300 digits. 37 expressions: the named repros, `k ∈ {110,116,124,130,136}` crossed with `{1/2, 1/3, 3/2, −1/2}`, plus `1+1`, `1-1`, `sin(pi/6)`, `ln(1+10^(-130))`.

| | exact path | seeded enclose |
| --- | ---: | ---: |
| Total | 7.3 s | 32.1 s (4.4×) |
| `1+1` | 9 ms | 83 ms |
| `1-1` | 2 ms | 26 ms |
| A cancellation row | about 110–450 ms | about 0.7–1.4 s |

The outside review (Part 3) measured about 93 ms for a small exact report, dominated by per-gate transcendentals. That is the current-engine baseline this table sits next to: a short circuit is already a transcendental walk, not a decimal add. The float-seeded Taylor/Newton idea (review P5) is on hold. It becomes a candidate only if profiling under the ball engine shows those transcendentals still dominate. It is a possible later optimization of this design, not part of the shadow or the switch.

The 4.4× is not an upper bound. 35 of the 37 rows returned `cut` or overflow and exited before a finished decision, so the seeded total understates a walk that runs out to the cap. The cap is 480 digits. The deadlines are 15 s for an ordinary value and 30 s for a slow one. When a deadline fires, the screen shows "couldn't verify". It does not print the center it had reached.

The adaptive engine starts at 120 and stops when the radius decides, so a clean digit claim should land nearer one 120-digit pass than this 300-digit walk. A shared subcircuit hits the context cache only when the bindings and the facts match. The point engine's second pass does not.

One expression at about 1 s fits the 15 s budget. A stack recompute of several rows at the seeded cost does not feel like the current screen. That is a reason to keep shadow mode until the adaptive loop is measured on the same corpus, not a reason to skip the harness.

Golf: the search loop is float `evaluate`. It does not call `enclose` or `exactReport`. A confirm of a watched constant already encloses, then calls `exactValueAt`. After (b) that confirm is the ball plus the exact layer. The pool time does not move.

## 8. Open questions for mathbot

Questions 1–7 block the switch. Question 7 is decided here. Question 8 does not block.

1. **B3, `cexp`. Blocking.** Is `exp(re+rr)·(exp(rr+ir)−1)` plus the absolute errors of `exp`, `cos`, `sin`, and the multiplies an outward radius for the rectangle? What is the absolute error of those decimal.js functions, including argument reduction for `|θ| ≥ 10^6`?
2. **B4, the closed ray. Blocking.** A rectangle with imaginary part `[0, ε]` and real part meeting `(−∞, 0)`, under arg = −π on the ray. Inconclusive, or is there an outward ball that stays off the cut?
3. **B6, rounding. Blocking.** Confirm the outward clone: low precision, rounding up, absolute charges. What is the absolute error per elementary function, including a bounded `atan2`? `atan2Fast` stays excluded until that bound exists.
4. **B1/B2, remainders. Blocking.** Sign a remainder that is valid on the complex rectangle for the shortcuts that exist today: sin, tan, tanh, arctan, `cos x − 1`, `ln(1+x)`, `exp(x)−1`, `sqrt(1+x)−1`, on the balls those thresholds describe. The real alternating "next term" bound is not that remainder.
5. **Exact zero. Blocking.** Confirm the exact layer's list: structural zero of radius 0, an exactly-zero imaginary part, `±0`, `±∞`, and integer leaves. Confirm that no separation bound is being assumed. `1e-500` and `exp(-1200)` are the counterexamples to any fixed cutoff, and `e^(-e^e^e)` is a nonzero far below every cutoff this engine can reach.
6. **Infinities. Blocking.** Which non-finite results are the exact points `+∞` and `−∞` on one part, and which are overflow? The `1e-15` snap is not an answer.
7. **Rectangle. Blocking, and decided.** The model is the rectangle in §3. Op bounds are written for that rectangle. The seed's half-diagonal inflation is not a second model.
8. **Per component. Not blocking.** May the screen certify one component's digits or sign and leave the other as a labelled bound or undecided when that other interval contains 0? The alternative is: if either interval contains 0, the whole value is undecided. Neither alternative may print the undecided component as exact 0.
