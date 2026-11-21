# Design: ball arithmetic as the exact engine

Status: design only. No engine change in this PR. Branch base: `main` at `d6be0d1`.

`lib/eml/enclose.ts` becomes the exact engine. A result is a complex ball. A ball proves digits, a sign, or nonzero. It never proves an exact 0, an exact integer, or a point exactly on an axis or the cut. Exact 0 is only a point a closed rule in §3 returned. A ball that excludes 0 always prints the digits both ends share, and it never wears the label "0 to N digits". A ball that contains 0 prints that label, where `N` is the largest integer such that the radius proves `|x| < 10^(-N)`. That label is the bound. It is not the exact 0 that today's dust and snap-to-zero would print. The cutoff "certified 0 means both intervals lie inside `10^(-480)`" is dropped. That rule would show `1e-500` and `exp(-1200)` as exact 0, which is a severity-1 false certificate, and it would still miss `1-1`: at the 480-digit cap the cancellation radius is about `10^(-478)`, larger than `10^(-480)`. Those two values, and `1e-400*(1+1e-100)-1e-400`, stay certified at today's nonzero text. The seed's cut on them is the seed's weakness.

EML builds `0`, `−1`, `i`, `π`, and negatives through `ln 0` and the cut. The seed's overflow on `−1`, `−2`, `i`, `π`, and `ln(−1)` is the refusal the log and cut rules already require of a bare ball. The closed rules in §3 are what certify those points. The seed's cut on `1e-500`, `exp(-1200)`, and `1e-400*(1+1e-100)-1e-400` is a radius that blew up. Those three stay certified nonzeros. This rewrite does not add functions and does not widen any domain (review E6). A case the ball cannot decide stays unverified. It does not grow a new approximation.

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
| `int` / `provenInteger` | The leaf is an integer the float has already rounded | Not a certificate. `exact.ts:587-598` and `:691-700` return this mark without walking the circuit, which is how a rounded literal became an exact integer (#15). A ball near an integer is not that integer. An exact integer is a point a closed rule returned. |

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
- `ln`: the seed returns overflow when the rectangle contains 0 (`mag ≤ rr+ir`), and a cut ball when `straddlesCut` says the rectangle meets both imaginary signs and the negative reals. Log of a ball that contains 0 is undecided, not −∞. The extended value `ln 0 = −∞` applies only to the exact point `+0`. Every zero these rules produce is `+0`. `ln(−0)` is not that row: today it is `−∞ − iπ`, and `−0` is not in the domain. A computed ball whose center rounded to 0 is not `+0`.
- Cut, lower bank (B4). On the negative real this engine uses arg = −π. Just above that ray, arg is near +π. A rectangle that only touches the ray from above (`im` interval `[0, ε]`, real interval meeting `(−∞, 0)`) does **not** trip `straddlesCut`, because that test demands a strictly negative and a strictly positive imaginary part (`enclose.ts:71`). Touching the closed ray is already two values a full turn apart. Such a ball is a cut, same as a ball that crosses. A ball strictly off the ray keeps a bounded `atan2`, not `atan2Fast`. A ball never proves that a point lies exactly on the cut.
- Infinities and poles. A non-finite center or a non-finite radius from rounding is overflow, not a number. A certified infinite part is an exact point `+∞` or `−∞` from the exact layer, one part at a time. A pole of `tan` is the angle ball meeting an odd multiple of `π/2` while also meeting points that are not that multiple: unverified, which matches today's pole flag. Containment in a pole tolerance does not prove the angle is that multiple.
- Series (B1/B2). The shortcuts in `library.ts` (`SERIES_ODD` −241, `SERIES_POLY` −61, `SERIES_WIDE` −20, `SERIES_REL` −480) become a Taylor polynomial evaluated as a ball, plus a remainder bound in the radius. The remainder has to be valid on the complex rectangle. "At most the next term" holds for a real alternating series and does not transfer to a complex ball. If the signed remainder still forces both ends of an interval to the same digit text, those digits are certified. If the remainder ball contains 0, the result is a labelled bound or undecided, never exact 0. That replaces today's "past the cap" outcome, without a lead flag and without printing a truncated term as exact.

### Exact layer

The ball refuses a point it cannot enclose. `0`, `−1`, `i`, `π`, and `ln(−1)` are circuits that pass through `ln 0` and the cut, so a bare ball overflows or cuts, and that refusal is right for the ball. `0`, `−1`, and `ln(−1)` come from the rules below. `i` and `π` are the same kind of circuit; the proposed table does not close them, and §8 asks mathbot for the row that would. A builder mark is not a rule, and a new identity is the wider domain §1 already puts out of scope. That is the contradiction with trusting "the builder proved this imaginary part is exactly 0" or "`provenInteger` says this leaf is the integer": #15 certified a pasted literal from its stored float (`RESUME.md` on `cursor/long-literal-wire-a4e8`; `exact.ts` returns the `int` mark and skips the walk), and #35 certified a real infinity from a sign mark while a finite imaginary part was still there (`RESUME.md` on `cursor/v11-directed-infinity-1253`, M1 and M2: `ln(ln(0))*i` came out 0, and `ln(ln(0)*i)`, `(inf*i)/2`, `sqrt(ln(0)*i)` were confident and wrong). `docs/known-limitations.md` records the same pattern: the word `111E1E1E1EE11EE` displays as exact `−1` while it differs by about `10^(-1656520)`, and `6.103×10^(−120)i` added to itself displays half the sum. The `unver` row above is a refusal, not a value. The `int` row is the same kind of fact. Neither fires a rule.

A side condition is a fact a ball already proved about a child: the imag interval sits inside `(−π, π)`, the rectangle excludes 0, the rectangle misses the cut, or the child is finite. A side-table flag never satisfies one. When a rule fires, the exact point and the rule that produced it travel on the wire. That field is new, so the PR that adds it bumps `WIRE_VERSION` in `lib/eml/wire.ts`. The worker checks the shape and the ball condition again. A token that only carries `int`, a decade, or a direction is not the point.

The rules. Rules 1, 3, 4, 5, 6, and 8, and the placeholder rule, are the ones the re-review accepted. **R1 (the domain and rule 9) and R2 (rule 7) are PROPOSED, pending mathbot sign-off.**

1. The `one` token is the exact point `1 + 0i`. No other leaf is exact.
2. The composed log of the literal 1 is `+0`. The node is the three-gate shape `eml(1, eml(eml(1, 1), 1))`, and the K 7 word `111E1EE` is that shape. This is not the gate's own `ln(1)`. The inner logarithm of one `eml` applied to the literal 1 is the table row `ln(1) = +0` below, a different node.
3. `ln(exp x) = x` only when the node is structurally a log of an exp, and a ball of `x` proves `Im x ⊂ (−π, π)`. The result is the exact point `x` already was. If `x` is not an exact point, the rule does not create one.
4. `exp(ln x) = x` only when the node is structurally an exp of a log, and a ball of `x` proves the rectangle excludes 0 and does not meet the cut. Same restriction: no new exact point.
5. `ln(+0) = −∞`. The argument has to be the exact point `+0` from rule 2 or from `exp(−∞)`. A ball that contains 0 does not fire. `−0` does not fire: `−0` is not in the domain, and today's `ln(−0) = −∞ − iπ`. Every zero these rules produce is `+0`, so there is no other zero for this rule to see.
6. `exp(−∞) = +0`. `exp(+∞) = +∞`. Both arguments are exact real infinities. `exp` of a non-real infinity leaves the domain.
7. **R2, PROPOSED, pending mathbot sign-off.** The infinity rows of `eml`, listed under R2 below. The partner of an infinity has to be proved exactly real. A finite imaginary part beside an infinite real part leaves the domain.
8. The log of an exact negative real point this list already returned (imag part `+0`, real part `< 0`): the lower-bank log is `ln|x| − iπ`, and the composed log is `ln|x| + iπ`. A ball that only meets the cut does not fire. The result stays in the domain only when `ln|x|` is already in the domain, so the only negative real it returns here is `−1`: lower-bank `ln(−1) = −iπ`, composed `ln(−1) = +iπ`. It does not cover `ln(i)`.
9. **R1, PROPOSED, pending mathbot sign-off.** The finite table under R1 below. A gate returns an exact point only on a row of that table. "Both children exact" is not a row. The rule 7 rows are the one place a partner may be a proved-exactly-real ball rather than a domain point. That ball is not itself an exact point: `exp(1)` stays the real ball of `e`.

The unverified placeholder never becomes the point 0. A dropped term stays unverified. No rule reads `unver` or `int`.

**R1, PROPOSED, pending mathbot sign-off. The exact domain.** Rule 9 as "both children exact, so the gate is exact" is not closed. Every constant circuit is built from the `1` token, so that reading makes `e`, the screen expression `1−1`, and the residue rows exact, and it needs a zero test to decide which results are `+0`. That contradicts the `1−1` line in §6.

The domain is the set of

`a + bπ + (c + dπ) i`

with `a, b, c, d` rational, together with the exact real infinities `+∞` and `−∞` (imag part proved `+0`) and the one non-real infinity the log table names, `+∞ + iπ`. The zero element is `+0`. `−0` is not in the domain. Equality of finite points is equality of the four rationals. It is decidable because `1` and `π` are linearly independent over the rationals. There is no numeric zero test.

**Rule 9, PROPOSED, is this table.** An input that is not one of these rows leaves the domain, and from there only balls apply. `eml(x, y) = exp(x) − ln(y)`.

`exp`, finite and infinite points already in the domain:

- `exp(+0) = 1`. `exp(+∞) = +∞`. `exp(−∞) = +0`.
- Quarter turns, and only these, read mod `2`: `exp(iπ/2) = i`, `exp(−iπ/2) = exp(3iπ/2) = −i`, `exp(iπ) = exp(−iπ) = −1`, `exp(2iπ) = 1`.
- `exp` of any other exact point leaves. In particular `exp(1)` is the real ball of `e`: a ball proves it finite, its imag part is `+0` because the argument is exact real, and it is not an exact point.

`ln`:

- `ln(+0) = −∞`. `ln(+∞) = +∞`. `ln(−∞) = +∞ + iπ`.
- `ln(1) = +0`. This is the gate's own log of the exact point `1`, not rule 2.
- `ln(i) = iπ/2` and `ln(−i) = −iπ/2`. Rule 8 does not justify these: `i` is not a negative real.
- Lower-bank `ln(−1) = −iπ` is rule 8. Any other exact point, including `ln(2)` and `ln(π)`, leaves.

`add` and `mul` of finite points:

- Addition stays. It adds the four rationals. `1 + (−1) = +0`. Subtraction is addition of the negation, so it stays too. `+0 − 1 = −1`.
- Multiplication stays when at least one factor lies in `Q(i)`, both π-coefficients zero, so the product has no `π²` term. Then `i·i = −1`, `i·(iπ) = −π`, `(−i)·(iπ) = π`, and `i·π = iπ`. If both factors carry a π coefficient, including `π·π`, the product leaves.
- An exact real infinity times a positive rational stays that infinity. Times a negative rational it flips sign. Times `0` it leaves (`0·∞`). Times a non-real point it leaves. Addition of two infinite points leaves, apart from the `eml` rows in R2.

**R2, PROPOSED, pending mathbot sign-off. Rule 7, the infinity rows of `eml`.** The partner of an infinity has to be proved exactly real: imag part `+0`, not a ball around 0, and a ball proves the real part finite when the row says finite. A finite imaginary part beside an infinite real part leaves. That is the #35 pattern, and it is the live bug `ln(0)−1`, which comes out `−∞ i` when the imag part is not discharged. The rows:

- `ln(+∞) = +∞`. The `−1` trace uses this row.
- `ln(−∞) = +∞ + iπ`. Not a real infinity of the opposite sign.
- `ln(+0) = −∞`. `exp(+∞) = +∞`. `exp(−∞) = +0`.
- On the exp side of `eml`, a proved exactly-real finite value (the exact real point, or the real ball of `exp` of an exact real, imag `+0`) minus `ln = −∞` is exact `+∞`. The same partner minus `ln = +∞` is exact `−∞`.
- On the ln side, `exp = +∞` minus a proved exactly-real finite value is exact `+∞`.
- `∞ − ∞` leaves. `+∞ − (−∞)`, both proved real, is `+∞`. An infinity whose partner is not proved exactly real leaves, whether the imag part is finite (`ln(0)+i`, `ln(0)−1` as the screen shows it) or the infinity itself is `+∞ + iπ`.

The screen expression `1−1` never presents two exact points to the addition row. Its circuit leaves at `exp(1)`, so only the ball applies, and §6 stands: the result is "0 to N digits", not `+0`.

Worked derivations. Lower bank inside the gate, composed log on the screen.

- **0.** `111E1EE` is rule 2, the three-gate composed log of the literal 1. Exact `+0`.
- **−1.** The K 15 word is `11111E1EEEE11EE`, seven gates. Gate 1, `eml(1, 1) = exp(1) − ln(1)`: the table's `ln(1) = +0` fires and `exp(1)` leaves, so the gate is the real ball of `e`, not an exact point. Gate 2 is the next tower step and leaves with it. Gate 3 is the rule 2 shape and returns `+0` without using that ball. Gate 4 is `eml(1, +0) = exp(1) − ln(+0) = exp(1) − (−∞)`. The partner is proved exactly real and finite (imag `+0` because the argument is exact real, and a ball proves the real part finite), so rule 7 returns `+∞`. Gate 5 is `eml(1, +∞) = exp(1) − ln(+∞)`, and `ln(+∞) = +∞`, so rule 7 returns `−∞`. Gate 6 is another `eml(1, 1)`, again the real ball of `e`. Gate 7 is `eml(−∞, eml(1, 1)) = exp(−∞) − ln(eml(1, 1))`. Rule 6 returns `+0`. The logarithm's argument rewrites, by `ln(1) = +0`, to the exp of the literal 1, so rule 3 returns that literal: `Im 1 ⊂ (−π, π)`, and the rule does not promote gate 6 itself into an exact point. The table subtracts `+0 − 1 = −1`.
- **ln(−1).** The screen's `ln` is the composed log of the exact point `−1`. Rule 8 returns `+iπ`. The golden text is `3.14159265359i`. The lower-bank log of the same point is `−iπ`. A ball around `−1` would be a cut and would not certify either.
- **i.** The K 57 word in `lib/eml/best-known.json` is `111111111EEE1EE11EE1EEEE1EE1111111E1EEEE11E1E1EEEE1EE1E1E`, 28 gates. Gates 1–15 leave: each is an `exp` tower on `eml(1, 1)`, and `exp(1)` is outside the domain. Gate 16 is the rule 2 shape `eml(1, eml(eml(1, 1), 1))` and returns `+0`. Gate 17 is `eml(1, +0) = +∞`. Gate 18 is `eml(1, +∞) = −∞`, using `ln(+∞) = +∞`. Gates 19–21 are the tower `eml(eml(eml(1, 1), 1), 1)` and leave. Gate 22 is `eml(−∞, that tower)`. Its logarithm is not a log of an exact point, so rule 3 does not return one, and rule 8 does not apply to a ball. The numeric story that the two copies of `e` cancel, leaving exact `iπ`, is the open reading of rule 9, and this table refuses it: those copies are real balls, not domain points. Gates 23–28 each have a child outside the domain, so they leave. The last gate is not the table row `exp(iπ/2) = i`. Its argument never became the exact point `iπ/2`. Under this proposal the stored word does not produce exact `i`. Today's display of `i` still has to be kept, by a signed ball's digits or by a further row mathbot adds. A ball near `i` is not the exact point. The table route, which this word does not take, is `ln(i) = iπ/2` and then `exp(iπ/2) = i`. `ln(i)` is that table row. Rule 8 does not justify it, because `i` is not a negative real.
- **π.** The K 93 word is `1111111111E1EEEE11E1E1EEEE1EEE1EE111111111EEE1EE11EE1EEEE1EE1111111E1EEEE11E1E1EEEE1EE1E1EE1E`, 46 gates. Gates 1–2 leave. Gate 3 is rule 2, `+0`. Gate 4 is `+∞`. Gate 5 is `−∞`. Gates 6–8 are the real tower and leave. Gate 9 is `eml(−∞, that tower)` and leaves, the same refusal as gate 22 of `i`. Gates 10–31 leave. Gate 32 is rule 2 again, `+0`. Gate 33 is `+∞`. Gate 34 is `−∞`. Gates 35–37 are the tower and leave. Gate 38 meets that tower with `−∞` and leaves. Gates 39–46 leave. The previous trace routed `ln(i)` through rule 8. Rule 8 only covers negative reals, so it cannot. The table route, once an earlier gate has actually returned the exact point `i`, is `ln(i) = iπ/2` and then `(−i)·(iπ) = π`. This word never puts exact `i` on that row. The displayed `π` stays a must-keep digit claim until mathbot adds a row that brings the tower back into the domain.

## 4. Decisions, digits, adaptive loop

Every numeric claim a ball makes is containment of an inequality. `cut` or overflow refuses every numeric claim. A timeout does the same and shows "couldn't verify".

- **Digits.** A ball that excludes 0 always prints its proven digits. Print `n` digits of a part only when both ends of that part's interval round to the same text. This is an inequality, not a claim that the center is exact. A half-unit test on the radius is not the rule. Digits past the radius are not stored and not shown. `sin(10^22)` prints as many digits as the argument-reduction bound actually proves, which may be none. A ball that excludes 0 never shows "0 to N digits", however small the value is.
- **Labelled bound.** This label is only for a ball that contains 0. `N` is the largest integer such that the radius proves `|x| < 10^(-N)`. The screen prints "0 to N digits". It is the replacement for a certified 0 that came from dust, a cancellation snap, or a vanished value. It is not exact 0. `1e-500`, `exp(-1200)`, and `1e-400*(1+1e-100)-1e-400` exclude 0 and keep today's certified digits. They do not wear this label, and the `10^(-480)` cutoff must not turn them into exact 0.
- **Nonzero and sign.** If the rectangle excludes 0, the value is certified nonzero and the digits above are printed. If a part's interval lies in a half-line (`Re > 0`, `Im < 0`, and so on), that sign is certified. An exact infinite sign is a point from the closed rules, not a ball that overflowed.
- **Integer.** An integer is an exact point a closed rule returned. A ball does not become an integer by lying near one. `2.3 ± 0.1` lies inside `(1.5, 2.5)` and is not the integer 2. `1 + 10^(-130)` is not the integer 1. The `int` mark is not the rule.
- **Exact zero.** Only the point `+0`, from rule 2 or from `exp(−∞)`. Rule 5 fires only on that `+0`. The rule "both intervals inside `10^(-480)`" is dropped. It would certify `1e-500` and `exp(-1200)` as exact 0, and those two stay certified nonzeros. It would also fail `1-1`, whose radius at the cap is about `10^(-478)`. There is no separation bound in this design that would let a class of tiny balls count as zero. `1-1` prints "0 to N digits" from that radius. The table row `1 + (−1) = +0` does not apply to that circuit.
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

The corpus includes the #33 repros, the cancellation family `k = 110..136` with the constants `{1/2, 1/3, 3/2, −1/2}`, `tan(1e100)`, `cos(1e100)`, `sin(1e22)`, `tan(1e22)`, `cos(1e7)`, the tiny-imaginary Chrome set, `ln(1+10^(-130))`, the closed-rule rows `0`, `−1`, `i`, `π`, `ln(−1)`, and the other negatives, the #15 literal rows, the #35 infinity rows, the v1.1 real-part drop, the three wire real-part drops, the live infinity rows, the must-stay rows `1e-500`, `exp(-1200)`, `1e-400*(1+1e-100)-1e-400`, `1e-400*pi+1e-400`, `exp(-1000)-exp(-1001)`, and the two `−1×10^−450` rows, the exact-zero residues and the stable residues below, and the live rows `ln(0)-1`, `ln(0)+i`, and `exp(ln(ln(0))*i)`.

A line may move from certified to unverified only when this section lists it. Any value change, and any new certification, needs an mpmath or Arb check at 2000 digits or more, named in that PR. The fuzz bar is zero false certifications: an unverified result is allowed, a certified digit, sign, nonzero, or exact point that is false is not.

**(a) Shadow.** Run the ball decision next to `exactReport`, in CI only, in three settings: in-process, a fresh process over the packed wire (`scripts/fresh-exact.ts`), and a Chrome Worker (`lib/eml/exact.worker.ts`). The screen keeps today's text. The golden file is recorded from today's engine first, so the shadow PR changes no golden line. If the packed token changes, that PR adds or bumps `WIRE_VERSION` in `lib/eml/wire.ts`, and all three runners refuse a mismatch. The tree has no such constant today.

**(b) Switch.** The screen and the returned decision follow the ball and the exact layer. This waits on mathbot's sign-off of the blocking questions in §8, and the same PR updates `README.md`, `docs/known-limitations.md`, and the UI. Those three still say a small residual is treated as 0 and that an exact 0 times a finite factor stays a certified 0. The UI prints "0 to N digits", with `N` from the radius as in §4, only for a ball that contains 0. Exact 0 is a point a closed rule returned. A ball that excludes 0 prints its digits. The golden file moves only on lines listed below, each with the 2000-digit check when the value or the certification changes.

**(c) Delete.** After the switch, each old mechanism stays in CI as a reverse shadow. One mechanism is removed per PR, and only after that reverse-shadow period. The mechanisms are `scrubDust`, `confirmDust`, `settleResidue`, `hiddenComponent`, the `lossGap` / `tiniest` retry, the `cosSin` point snap, and the `axisInfinity` `1e-15` snap. Float evaluation stays.

Expected disagreements, current engine wrong, ball right once the bounds are signed. Each of these is a listed certified-to-unverified line, or a listed digit change, and each needs the 2000-digit check:

- `((1+10^(-k))-1)+i·c` for `k` in 110..136 prints `c·i` and drops the real `10^(−k)`. Measured on this SHA: `((1+10^(-130))-1)+i/2` prints `0.5i`, `((1+10^(-136))-1)+i*3/2` prints `1.5i`, `((1+10^(-110))-1)+i*10^10/3` prints `3333333333.33i`.
- `(i*(1+10^(-124))-i)*i+i*10^10/3` prints `3333333333.33i` and drops the real `−10^(−124)`. Same on `(i*(1+10^(-130))-i)*i+i/2`, which prints `0.5i`.
- `sin` / `tan(10^22)` and `cos(10^7)` print a dozen digits the reduction does not justify. Fewer digits, or unverified, is the expected change. Matching the point engine's digits with a huge radius is a failed display rule.
- `tan(1e100)` and `cos(1e100)` are the same class.
- `1-1` is a certified 0 today by snap. After the switch it is "0 to N digits", `N` from the radius. The circuit leaves the domain at `exp(1)`, so the table row `1 + (−1) = +0` never fires. Keeping today's exact 0 would be the dropped cutoff coming back.

The corpus also carries the known wrong answers, so a builder mark cannot certify them again:

- **#15, pasted literals.** A long decimal whose stored float is not the text. The rounded float is not a known point. `A−1` at 479 and 480 digits, and 479 nines times 2 minus 2, stay unverified. The square, `sqrt`, and `sin` of the 41-digit paste `1.000…1` use the text, not the float.
- **#35, directed infinities.** `ln(ln(0))*i` is not 0. `ln(ln(0)*i)`, `(inf*i)/2`, `(ln(0)*i)/2`, `(inf*i)/(1+i)`, and `sqrt(ln(0)*i)` are not confident finite values. `inf^0`, `(-inf)^0`, `(-inf)^3.0`, and `(-inf)^(6/2)` stay unverified. The known-limitations tower `111E1E1E1EE11EE` is not exact `−1`.
- **v1.1 real-part drop, the #33 failing test.** `(i*(1+10^(-124))-i)*i+i*10^10/3` prints `3333333333.33i` and drops the real `−10^(−124)`. Golden marks it `A1-real-drop`. The screen must keep the real part.
- **Wire real-part drop.** `((1+10^(-130))-1)+i/2`, `((1+10^(-130))-1)+i*(1+10^(-130))/2`, and `((1+10^(-136))-1)+i*3/2`. Golden marks these `wire-real-drop`: the real part near `10^(−130)` disappears on the packed wire. The ball keeps it.
- **Live infinity rows**, from `lib/eml/check.ts` and the #41 golden file. `ln(0)`, `ln(0)*2`, `ln(0)*(-2)`, `2*ln(0)`, `(-2)*ln(0)`, `ln(0)*i`, `i*ln(0)`, `ln(0)*i*i`, `sqrt(ln(0))`, `sqrt(ln(0))^2`, `-(sqrt(ln(0)))`, `(inf*i)*(inf*i)`, `(inf*i)^3`, `(-inf)^3`, `ln(0)^2`, `ln(0)^3`, `(ln(0)*i)^2`, `(ln(0)*i)^3`, and `1/0`. `ln(0)*0`, `sin(ln(0))`, `cos(ln(0))`, and `tan(ln(0))` stay undefined.
- **Live rows quoted as reviewbot wrote them.** `ln(0)-1`, `ln(0)+i`, and `exp(ln(ln(0))*i)`. If the partner of `ln(0)` is proved exactly real, the table says `ln(0)-1` is `−∞ − 1 = −∞`. The live value `−∞ i` is the case where a finite imag part survived, and that leaves the domain: undecided, not an exact real infinity. `ln(0)+i` is an infinity plus a non-real point, so it leaves. `exp(ln(ln(0))*i)`: `ln(−∞) = +∞ + iπ`, and multiplying by `i` leaves, so the exp leaves. Collapsing `ln(ln(0))` to a real `+∞` first is the #35 sign-mark bug, not a reading of this row. The spelling is the one above; none of the three has a second form in the suite.

Must stay certified. These are certified and correct today. Losing the value, or printing exact 0 or "0 to N digits" for a row that excludes 0, fails the PR:

- `0`, `−1`, and `ln(−1)`, by the derivations above. `−2`, the other negatives, `i`, and `π` stay at today's certified text. The proposed table produces `−1` and `+iπ` and does not produce `i` or `π` from the stored words. Losing any of these displays fails the PR. Certifying `i` or `π` by the old open reading of rule 9 fails it too. The seed overflows because the ball will not invent the point.
- `1e-500`, `exp(-1200)`, and `1e-400*(1+1e-100)-1e-400`. Each excludes 0 and is a certified nonzero today (`1e-400*(1+1e-100)-1e-400` is `1×10^−500`). The seed's cut is a blown radius, not the target. The digits are what both ends of a signed ball print. Exact 0 here is the severity-1 failure.
- `1e-400*pi+1e-400` stays `4.14159265359×10^−400`. `exp(-1000)-exp(-1001)` stays `3.20861797491×10^−435`. The `−1×10^−450` rows stay that text: `1e-400-1e-400*(1+1e-50)` and `(1e-400)*3/3-(1e-400)*(1+1e-50)`. Those are the kept-value rows in the tiny-ratio and residue tests, not the cancellations that are honestly 0.
- `ln(1+10^(-130))` stays `1×10^−130` once a remainder valid on the complex rectangle forces both ends to that text. `sin(pi/6)` stays `0.5` once a signed bound forces both ends. Until that bound is signed, an unverified result is a listed line, not a quiet seed patch.

Exact-zero residues are identities, and they are not in the domain, so the table does not return `+0`. The ball contains 0 and the screen shows "0 to N digits", not exact `+0`. The rows, quoted as reviewbot wrote them: `exp(ln(1e-400))-1e-400`, `1e-400*1.5/1.5-1e-400`, `1e-400/2*2-1e-400`, `1e-400/0.5/2-1e-400`, and `(2^0.5)^2-2e-400`. The last spelling is ambiguous. The residue tests write the scaled form `1e-400*(2^0.5)^2-2e-400`, and the unscaled identity is `(2^0.5)^2-2`. All three are in the corpus; none of them is exact `+0`.

Stable residues follow the same rule. The radius can sit still while precision climbs. `1e-100*1.5/1.5-1e-100`, and the same pattern at `1e-50`, `1e-150`, and `1e-200`. The suite also has `1e-200*(2^0.5)^2-2*1e-200`, which is the sqrt form at that scale, not a second spelling of the `1.5` row.

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

Questions 1–6 block the switch. Question 7 is decided. Question 8 does not block.

1. **B3, `cexp`. Blocking.** Is `exp(re+rr)·(exp(rr+ir)−1)` plus the absolute errors of `exp`, `cos`, `sin`, and the multiplies an outward radius for the rectangle? What is the absolute error of those decimal.js functions, including argument reduction for `|θ| ≥ 10^6`?
2. **B4, the closed ray. Blocking.** A rectangle with imaginary part `[0, ε]` and real part meeting `(−∞, 0)`, under arg = −π on the ray. Inconclusive, or is there an outward ball that stays off the cut?
3. **B6, rounding. Blocking.** Confirm the outward clone: low precision, rounding up, absolute charges. What is the absolute error per elementary function, including a bounded `atan2`? `atan2Fast` stays excluded until that bound exists.
4. **B1/B2, remainders. Blocking.** Sign a remainder that is valid on the complex rectangle for the shortcuts that exist today: sin, tan, tanh, arctan, `cos x − 1`, `ln(1+x)`, `exp(x)−1`, `sqrt(1+x)−1`, on the balls those thresholds describe. The real alternating "next term" bound is not that remainder.
5. **Exact points. Blocking.** Sign the rule list in §3. R1 (the domain and the operation table) and R2 (the infinity rows) are proposed there and wait on this sign-off. No builder mark is a side condition. No separation bound is assumed. `1e-500` and `exp(-1200)` stay certified nonzeros, and they are the counterexamples to any cutoff that would call them exact 0. `e^(-e^e^e)` is a nonzero far below every cutoff this engine can reach. The K 57 and K 93 words leave the proposed domain; a row that brings `i` and `π` back in is part of this sign-off.
6. **Infinities. Blocking.** Which non-finite results are the exact points `+∞` and `−∞` on one part, and which are overflow? The proposed answer is rule 7. A finite imaginary part beside an infinite real part leaves the domain. The `1e-15` snap is not an answer.
7. **Rectangle. Decided.** The model is the rectangle in §3. Op bounds are written for that rectangle. The seed's half-diagonal inflation is not a second model. This question does not block the switch.
8. **Per component. Not blocking.** May the screen certify one component's digits or sign and leave the other as a labelled bound or undecided when that other interval contains 0? The alternative is: if either interval contains 0, the whole value is undecided. Neither alternative may print the undecided component as exact 0.
