# Design: ball arithmetic as the exact engine

Status: design only. No engine change in this PR. Branch base: `main` at `d6be0d1`.

`lib/eml/enclose.ts` becomes the exact engine. A result is a complex ball. The screen certifies a claim only when every point of the ball satisfies it. A ball can certify nonzero (it excludes 0) or a sign or other inequality. A ball that contains 0 is always undecided, never a certified 0: it only proves a bound on the magnitude. Exact zero needs a recorded rewrite or other symbolic identity, or a separation bound for that class of expressions, and this design does not have that bound. This is a behavior change from today's dust and snap-to-zero, which turn a tiny residual into a certified 0. "Couldn't verify" is that undecided ball, a cut, or an overflow. The snap, dust, residue, and `lossGap` retries are not part of the test. This rewrite does not add functions and does not widen any domain (review E6). A case the ball cannot decide stays unverified. It does not grow a new approximation.

## 1. Scope and non-goals

In scope: the exact-mode decision and the digits it prints, for the circuits the calculator already builds. The float evaluator stays the float evaluator. Constant search keeps enumerating with float.

Out of scope:

- New functions, new identities, or a wider domain for an existing one (E6).
- Porting the absorbed-term retry from #33. `main` does not have it (`docs/known-limitations.md` only plans it). A term inside the radius widens the ball. That is the replacement.
- Changing the lower-bank cut. Arg on the negative real stays −π, matching `lib/eml/complex.ts` and the head of `exact.ts`.
- The golf pool. `searchConstants` never asks the exact engine for the millions of rejected circuits. Only a watched constant confirm calls `enclose` today (`golf.ts`).

## 2. What `exact.ts` does today, and what replaces it

Working precision starts at 120 (`PRECISION`) and stops at 480 (`PRECISION_CAP`). `Decimal.clone` at `exact.ts:42` is a module global. `exactReport` (`:571`) walks the circuit once, then runs several repairs. `atPrecision` (`:389`) re-enters `exactReport` at `pass = 2`, which returns before the repair loop.

| Mechanism | Where | Under balls |
| --- | --- | --- |
| Precision passes | 120, then raised by gap, tiny leaf, or hidden component | One adaptive loop. Double the precision until the ball decides or the cap is hit. No separate repair passes. |
| `cosSin` snap (`:75-87`) | An angle within tolerance of `k·π/2` becomes that axis | Containment. If the whole angle ball sits inside the tolerance of the axis, the value ball is the axis value plus the remainder of being off it. If the angle ball only overlaps the axis, the result covers both, or the claim is unverified. A point snap goes away. |
| `scrubDust` (`:252`) | A component far below its sibling is cleared to a certified 0 | The radius stops that digit from printing. Clearing it to 0 is the snap this design drops. A component interval that contains 0 is undecided, not zero. |
| `lossGap` / `tiniest` (`:195`, `:197`) | A cancellation or a tiny nonzero raises precision, up to the cap. A zero that still vanishes is unverified (`certifyZero`, `:469`). One that survives is certified 0 | The globals go away. A ball that excludes 0 certifies nonzero. A ball that contains 0 stays undecided at every precision, including the cap. Nothing in the loop promotes it to zero. |
| `hiddenComponent` (`:411`) | One component is 0 and the other is huge (`10^300 + i`), and the 0 is kept | The small interval contains 0, so that component is undecided. The huge component can still certify its digits. The screen must not print the small one as 0. |
| `confirmDust` (`:454`) and `settleResidue` (`:514`) | Re-run at +24 or +96 digits and keep a part only if it does not move | The adaptive loop is this re-run. A part that "moves" is a radius that was too small for the claim. |
| `pureCache` (`:307-310`, hit `:747`, store `:804`) | `{value, why, logged, work}` by node, per precision. A hit does not restore `lossGap`, `tiniest`, or `sawLead` | Cache the ball, keyed by `(node, precision)`, inside the evaluation context from D3. A hit returns the same ball the walk would have built. |
| Absorbed-term retry | Not on this SHA. #33 added one and certified values whose lost term sat in an exact-0 component | Not ported. `1 + 10^(-130)` is a ball whose radius is at least that term. It is not the integer 1. |

Side-table facts that the point engine reads (`wire.ts` carries the ones the worker must see):

| Fact | Role today | Under balls |
| --- | --- | --- |
| `decades` | A known power of ten, so a later pass can see `10^(-400)` | A hint for the starting precision, so the loop does not double from 120 up to 400. Not a certificate. Missing hint: the loop still runs to the cap. |
| `lostTiny` / `cap` | A term past 480 digits. A vanished result is not a certified 0 | The cap still stops the loop. A ball that contains 0 at 480 digits is undecided, not zero. The flag can go once that is the only rule. Today's snap of a vanished value to 0 does not survive. |
| `scaledShell` | Lift gates are left out of the noise exponent | The lift is ordinary arithmetic. The radius of the quotient is the proof. Delete the mark when decisions switch. |
| `lead` (series shortcut) | The circuit was replaced by a leading term. A zero from that replacement is not certified. A nonzero leading term is printed | Taylor polynomial plus a remainder ball (B1/B2). The boolean is not a certificate. |
| `unver` | The builder dropped a term, or a `beside:` integer mul must not be certified (`hidesBeside`) | Remainder balls cover the shortcuts. `beside:` stays: it is a structural refusal, not a radius. |
| `int` / `provenInteger` | The leaf is an integer the float has already rounded | Stays for that leaf: the builder recorded the integer, so the leaf ball is that integer with radius 0. A computed value is only the inequality the ball proves, not an equality to the nearest integer. |

`piCoeff`, the series-arg maps, `realSum` / `realSub`, and the other build-only tables in `library.ts` and `lowering.ts` choose which circuit is built. They are not exact-mode certificates. This design does not merge them.

## 3. The ball

Seed: `enclose.ts`. A ball is a center and a radius per component, not a general set.

```
{ re, im, rr, ir }   // center (re, im), radii rr, ir ≥ 0
```

The set is the rectangle `[re−rr, re+rr] × [im−ir, im+ir]`. A disk is a possible later tightening. The seed already uses a rectangle and then inflates `cexp` with `rr+ir`, which is an upper bound on the half-diagonal. Mathbot owns which model the op bounds are written for (open question below).

`decimal.js` defaults to `ROUND_HALF_UP` (`Decimal.rounding === 4`, confirmed on this tree). That mode is not an outward rounding. Two rules, both required (B6):

- Radius arithmetic rounds up. Each primitive adds at least one unit in the last place of its result (`u` in `enclose.ts:16` is `10^(e+1−precision)`, one ulp).
- Elementary functions need a published error in ulps, not a hope that half-up was correctly rounded. `cos` / `sin` of a large argument also need the error of reducing modulo π. Padding by one ulp of the final multiply does not cover that.

`cexp` as seeded (`enclose.ts:52-63`) sets the center to `exp(re)·(cos im, sin im)` and the radius to `exp(re+rr)·(exp(rr+ir)−1)` plus one ulp of the output, on both axes. The Lipschitz shape is the right one: `|e^(z+δ) − e^z| ≤ e^(Re z) (e^(|δ|) − 1)`. The seeded line is not yet a proof. It charges one ulp at the end and none for `exp`, `cos`, `sin`, or the two multiplies, and it ignores argument reduction. That is B3. Until mathbot signs a bound, `cexp` stays a shadow. It must not certify.

Other ops, same standard:

- Add and sub: radius is the sum of the radii plus one ulp of the sum. The seed's `cadd` is the pattern.
- Mul and div: not in the seed (`enclose` only implements `exp(a) − ln(b)`). Needed once shortcuts and scalings are balls rather than rewritten gates. Bound is the usual product of centers and radii, plus ulps, with div refused when the denominator rectangle contains 0.
- `ln`: the seed returns overflow when the rectangle contains 0 (`mag ≤ rr+ir`), and a cut ball when `straddlesCut` says the rectangle meets both imaginary signs and the negative reals. Log of a ball that contains 0 is undecided, not −∞. The extended value `ln 0 = −∞` applies only to a structural zero, the zero leaf or a recorded rewrite, not to a computed ball whose center rounded to 0.
- Cut, lower bank (B4). On the negative real this engine uses arg = −π. Just above that ray, arg is near +π. A rectangle that only touches the ray from above (`im` interval `[0, ε]`, real interval meeting `(−∞, 0)`) does **not** trip `straddlesCut`, because that test demands a strictly negative and a strictly positive imaginary part (`enclose.ts:71`). Touching the closed ray is already two values a full turn apart. Such a ball is a cut, same as a ball that crosses. A ball strictly off the ray keeps `atan2`.
- Infinities and poles. A non-finite center or a non-finite radius is overflow, not a number. A certified infinity is a separate claim: the ball lies outside every finite bound in a stated direction (the directed-infinity facts already record a quarter turn). A pole of `tan` is the angle ball meeting an odd multiple of `π/2` while also meeting points that are not that multiple: unverified, which matches today's pole flag. A ball contained in the pole tolerance may say "pole" rather than a finite number.
- Series (B1/B2). The shortcuts in `library.ts` (`SERIES_ODD` −241, `SERIES_POLY` −61, `SERIES_WIDE` −20, `SERIES_REL` −480) become a Taylor polynomial evaluated as a ball, plus a remainder bound in the radius. `sin x = x − x^3/6 + … + R` with `|R|` at most the next term on the ball of `x`. If that radius still determines the printed digits, those digits are certified. If the remainder ball contains 0, the result is undecided, not zero. That replaces today's "past the cap" outcome, without a lead flag and without printing a truncated term as exact.

## 4. Decisions, digits, adaptive loop

Every claim is containment. `cut` or overflow refuses every numeric claim.

- **Value.** Print a digit only when every point of the ball has that digit. The count is the largest `n` such that the radius is strictly below half a unit in that place, relative to the center's scale. This is an inequality (the value lies in that decimal interval), not a claim that the center is exact. It is the fix for the #33 dust complaint: digits past the radius are not stored and not shown. `sin(10^22)` prints as many digits as the argument-reduction bound actually proves, which may be none.
- **Nonzero, sign, inequality.** If the rectangle excludes 0, the value is certified nonzero. If it lies in a half-plane (`Re > 0`, `Im < 0`, and so on), that sign is certified. `|x − n| < 1/2` is the same kind of claim. None of these is an equality.
- **Integer equality.** A ball inside `(n − 1/2, n + 1/2)` certifies the nearest-integer inequality and excludes every other integer. It does not certify `x = n`. A residue smaller than the radius, the same shape as `10^(-130)` beside an integer, is still allowed by the ball. Equality to `n` needs a recorded rewrite or another symbolic identity, just as zero does.
- **Exact zero.** Dropped: both intervals inside `10^(-480)` is not a proof of zero. A ball of that size only proves `|x| < 10^(-480)`. EML values such as `e^(-e^e^e)` are nonzero and far smaller than any fixed cutoff, so no absolute `τ` works. A ball that contains 0 is always undecided, at 120 digits and at the cap. Exact zero is a structural fact: the zero leaf, or a recorded rewrite such as a fold that the builder has already justified. This design does not have a proven separation bound that would let a class of tiny balls count as zero. Until that bound exists, the engine must not invent one.
- **Couldn't verify.** The claim is not forced. A rectangle that contains 0, a cut, an overflow, or a radius that still moves the leading digit at the cap. Containing 0 is never read as zero. That is the break with today's dust and snap-to-zero (`scrubDust`, a cancellation cleared to exact 0, a vanished value kept as 0).
- **Differs from float.** Unchanged comparison, against the ball rather than a point. Float differs when its displayed value lies outside the ball (plus the existing 12-digit slack). A ball that is itself unverified does not accuse the float. A float 0 against a ball that merely contains 0 is not a disagreement the ball can settle.

Per component, not only for the complex value. A tight imaginary interval and a real interval that contains 0 certify the imaginary digits and leave the real part undecided. They do not print a real 0. Whether the screen shows the good component beside an undecided one is the open question in §8. The bug to forbid is the one #33 shipped: printing `0.5i` as a match.

Adaptive loop, one place, replacing every retry:

1. Start at 120, or at the decade hint when that is higher.
2. Enclose at that precision.
3. If the claim is decided (printed digits, a nonzero or sign or other inequality, a cut, or an overflow), stop. A ball that still contains 0 is not decided.
4. Otherwise double, up to 480. Still ambiguous: couldn't verify.

No second policy for dust versus residue versus a hidden component.

## 5. Fit with D3

One context per evaluation, passed down, not module globals:

```
{ precision, rounding, cache }
```

`cache` maps `(node, precision)` to a ball. It is the replacement for `pureCache`, and it stores the radius. `lossGap`, `tiniest`, `emlWork*`, and `sawLead` are not in the context. They described a point evaluation. The worker and the main-thread fallback each build their own context. They already do not share `exact.ts` globals, because a worker is another realm. `D.set` goes away as a process-wide side effect. The context owns its `Decimal` clone. Radius steps set that clone to round up, or they use a second clone that does. Nested re-entry is just another context. It cannot clobber the caller's precision.

`hasVarOf` can stay a per-context memo or be recomputed. It is not a ball.

Lines a later patch will touch, and that bigfixer is also touching: `cosSin` at `exact.ts:75-87`, and the `pureCache` hit and store at `:747-754` and `:804`. The shadow PR should land beside those, not inside them, until that work settles.

## 6. Migration

Each step is its own PR. Each is gated by a golden file: exact display text plus flags (`unverified`, `singular`, differs-from-float) for a fixed corpus. The corpus includes the #33 repros, the cancellation family `k = 110..136` with the constants `{1/2, 1/3, 3/2, −1/2}`, `tan(1e100)`, `cos(1e100)`, `sin(1e22)`, `tan(1e22)`, `cos(1e7)`, the tiny-imaginary Chrome set, and `ln(1+10^(-130))`. `eml:check` stays as the regression net for everything already locked.

**(a) Shadow.** Run the ball decision next to `exactReport`. Log disagreements. The screen keeps today's text. The golden file is recorded from today's engine first, so the shadow PR changes no golden line.

**(b) Switch.** The screen and the returned decision follow the ball. The golden file is updated only on lines marked expected below.

**(c) Delete.** Remove `scrubDust`, `confirmDust`, `settleResidue`, `hiddenComponent`, the `lossGap` / `tiniest` retry, and the `cosSin` point snap. Float evaluation stays.

Expected disagreements, current engine wrong, ball right once the bounds are signed:

- `((1+10^(-k))-1)+i·c` for `k` in 110..136 prints `c·i` and drops the real `10^(−k)`. Measured on this SHA: `((1+10^(-130))-1)+i/2` prints `0.5i`, `((1+10^(-136))-1)+i*3/2` prints `1.5i`, `((1+10^(-110))-1)+i*10^10/3` prints `3333333333.33i`.
- `(i*(1+10^(-124))-i)*i+i*10^10/3` prints `3333333333.33i` and drops the real `−10^(−124)`. Same on `(i*(1+10^(-130))-i)*i+i/2`, which prints `0.5i`.
- `sin` / `tan(10^22)` and `cos(10^7)` print a dozen digits the reduction does not justify. Fewer digits, or unverified, is the expected change. Matching the point engine's digits with a huge radius is a failed display rule, not a win.
- `tan(1e100)` and `cos(1e100)` are the same class.

Regressions, ball wrong if these move:

- `1+1` stays the digits `2`. The seeded ball has radius about `10^(-297)` and excludes every other displayed value. That is an inequality, not a new kind of exact equality.
- `1-1` is the behavior change, not a regression against the new rule. Today it is a certified 0 by snap. The seeded ball contains 0 with radius about `10^(-298)`, which proves `|z| < 10^(-297)` and nothing more. After the switch that result is undecided, unless a recorded rewrite has already reduced the circuit to the zero leaf. Keeping today's certified 0 here would be the old rule coming back.
- `ln(1+10^(-130))` prints `1×10^−130` today. A remainder ball should still certify that. The seed currently returns a cut. That is a seed bug to fix in (a), not a golden change in (b).
- `sin(pi/6)` prints `0.5`. The seed returns overflow. Same: fix the bound, do not flip the golden line.
- A certified value that becomes unverified with no entry in the expected list is a regression. Shadow mode fails the PR.

On this corpus the seed is not ready to switch. Of 37 expressions, 35 came back `cut` or overflow, including the identities above and `exp(1e-6)-1`. The cancellation rows came back `cut`, which is the right refusal to print `0.5i`, but a cut caused by a blown `cexp` radius is not yet a proof that the real part is ambiguous. (a) has to separate those.

## 7. Performance

Throwaway timing on this SHA, cold process, no ball cache. `exactReport` against `enclose` at its fixed 300 digits. 37 expressions: the named repros, `k ∈ {110,116,124,130,136}` crossed with `{1/2, 1/3, 3/2, −1/2}`, plus `1+1`, `1-1`, `sin(pi/6)`, `ln(1+10^(-130))`.

| | exact path | seeded enclose |
| --- | ---: | ---: |
| Total | 7.3 s | 32.1 s (4.4×) |
| `1+1` | 9 ms | 83 ms |
| `1-1` | 2 ms | 26 ms |
| A cancellation row | about 110–450 ms | about 0.7–1.4 s |

The outside review (Part 3) measured about 93 ms for a small exact report, dominated by per-gate transcendentals. That is the current-engine baseline this table sits next to: a short circuit is already a transcendental walk, not a decimal add. The float-seeded Taylor/Newton idea (review P5) is on hold. It becomes a candidate only if profiling under the ball engine shows those transcendentals still dominate. It is a possible later optimization of this design, not part of the shadow or the switch.

The 4.4× is an upper bound for "always 300 digits, never cached," and it buys almost no decisions. The adaptive engine starts at 120 and stops when the radius decides, so a clean identity should land nearer one 120-digit pass than this 300-digit walk. A shared subcircuit hits the context cache. The point engine's second pass does not.

The Chrome job allows 15 s for an ordinary exact value and 30 s for a slow one. One expression at about 1 s fits. A stack recompute of several rows at the seeded cost does not feel like the current screen. That is a reason to keep shadow mode until the adaptive loop is measured on the same corpus, not a reason to skip the harness.

Golf: the search loop is float `evaluate`. It does not call `enclose` or `exactReport`. A confirm of a watched constant already encloses, then calls `exactValueAt`. After (b) that confirm is the ball alone. The pool time does not move.

## 8. Open questions for mathbot

Soundness rules, and B3–B6, stay with mathbot. These block step (b).

1. **B3, `cexp`.** Is `exp(re+rr)·(exp(rr+ir)−1)` plus one output ulp an outward radius for the rectangle, once `exp`, `cos`, `sin`, and the multiplies are charged? What is the ulp error of those decimal.js functions, including argument reduction for `|θ| ≥ 10^6`?
2. **B4, the closed ray.** A rectangle with imaginary part `[0, ε]` and real part meeting `(−∞, 0)`, under arg = −π on the ray. Inconclusive, or is there an outward ball?
3. **B6, rounding.** Is one ulp of padding enough on top of `ROUND_HALF_UP`, or do radius ops have to round up, with a stated `k`-ulp bound per elementary function?
4. **B1/B2, remainders.** Sign the Lagrange remainder for the shortcuts that exist today: sin, tan, tanh, arctan, `cos x − 1`, `ln(1+x)`, `exp(x)−1`, `sqrt(1+x)−1`, on the balls those thresholds describe.
5. **Exact zero.** A ball that contains 0 is undecided, not zero. Which recorded rewrites count as a structural zero (the zero leaf, which folds), and is there a separation bound for any class of EML expressions that would prove a tiny value is exactly 0? This design does not have one. `e^(-e^e^e)` is the counterexample to any fixed cutoff.
6. **Infinities.** When is a non-finite ball a certified directed infinity, and when is it overflow?
7. **Rectangle or disk.** The op bounds need one model. The seed mixes them.
8. **Per component.** May the screen certify one component's digits or sign and leave the other undecided when that other interval contains 0? The alternative is: if either interval contains 0, the whole value is undecided. Neither alternative may print the undecided component as 0.
