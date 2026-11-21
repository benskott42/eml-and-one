# Design: ball arithmetic as the exact engine

Status: design only. No engine change in this PR. Branch base: `main` at `d6be0d1`. Mathbot signed Q1–Q8 and R1/R2 on 2026-11-21. The write-up is [`ball-soundness.md`](ball-soundness.md) (credit: mathbot, 2026-11-21, design input). The checks are in [`ball-checks/`](ball-checks/).

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

The set is `[re−rr, re+rr] × [im−ir, im+ir]`. Each part is its own interval, and a ball's intervals are finite. An exact infinite part is a point from the exact layer: a real `+∞` or `−∞`, or one of the four directed points `∞·i^k`. That replaces `axisInfinity` (`exact.ts:89-94`), which snaps a component smaller than `1e-15` to signed 0. A finite residual beside an infinity stays in its interval. It is not cleared, and it is not turned into a real infinity.

`decimal.js` defaults to `ROUND_HALF_UP` (`Decimal.rounding === 4`, confirmed on this tree). That mode is not an outward rounding. Radius steps run on a separate clone, at low precision, with rounding directed upward. The high-precision clone that builds the center is not that clone. Every elementary error is added to the radius as an absolute quantity on the outward clone. A relative factor that rounds away, and one ulp of a final multiply, are not a charge. `cos` / `sin` of a large argument include the absolute error of reducing modulo π. `atan2Fast` (`exact.ts:144-156`, the float seed plus the odd series at `:158-192`) is excluded from any certified argument. It stays out until a signed bound covers the seed and the series. The seed's `D.atan2` is the function a bound has to cover; the fast path is not a substitute.

`cexp` as seeded (`enclose.ts:52-63`) sets the center to `exp(re)·(cos im, sin im)` and the radius to `exp(re+rr)·(exp(rr+ir)−1)` plus one ulp of the output, on both axes. The Lipschitz shape is the right one: `|e^(z+δ) − e^z| ≤ e^(Re z) (e^(|δ|) − 1)`. The seeded line is not the signed rule. It charges one ulp of the component, and the `− 1` is evaluated at the centre precision, where the stretch rounds to 0 below about `1e-300`. The signed rule is [`ball-soundness.md` §2](ball-soundness.md): on the upward radius clone, `E(ρ) = ρ(1+ρ)` for `ρ ≤ 1` (and `ρ·e^ρ`, padded, or a refusal, for `ρ > 1`) in place of `exp(ρ) − 1`, and a charge of `8u·M↑` on the magnitude `e^x`, not on the component. Argument reduction past decimal.js's π cap throws, and that result is undecided. The prototype of that rule, [`ball-checks/proto.log`](ball-checks/proto.log), misses 0 of 6024 inputs (3010 point `cexp`s, 405 random `cexp` rectangles, 2004 point `cln`s, 605 random `cln` rectangles). The seed missed 654 of 3010 and 814 of 2004. Three of the 605 `cln` rectangles were refused, which is the cut rule, not a miss.

Other ops, same standard:

- Add and sub: radius is the sum of the radii plus the absolute rounding error of the sum, charged on the outward clone. The seed's `cadd` is the pattern, once that charge replaces its half-up ulp.
- Mul and div: not in the seed (`enclose` only implements `exp(a) − ln(b)`). Needed once shortcuts and scalings are balls rather than rewritten gates. Bound is the usual product of centers and radii, plus absolute errors, with div refused when the denominator rectangle contains 0.
- `ln`: the seed returns overflow when the rectangle contains 0 (`mag ≤ rr+ir`), and a cut ball when `straddlesCut` says the rectangle meets both imaginary signs and the negative reals. Log of a ball that contains 0 is undecided, not −∞. The extended value `ln 0 = −∞` applies only to the exact point `+0`. Every zero these rules produce is `+0`. `ln(−0)` is not that row: today it is `−∞ − iπ`, and `−0` is not in the domain. A computed ball whose center rounded to 0 is not `+0`.
- Cut, lower bank (B4). On the negative real this engine uses arg = −π. The gate log of an exact −1 is `−iπ`, and the gate log of an exact real `−∞` is `+∞ − iπ`. That is `complex.ts:102-108` and `:136-137` (`logArg(z, −π)`), `exact.ts:125` (`onCut → negPi`) and `:133-134`, and `enclose.ts:85`. The screen's composed log of `−1` is `+iπ`, which is rule 8's second clause, not the gate. Just above the ray, arg is near `+π`. The seed's `straddlesCut` (`enclose.ts:71`) demands both imaginary signs, so a rectangle that only touches the ray from above (`im` interval `[0, ε]`, real interval meeting `(−∞, 0)`) does not trip it. The signed fix is `imLo ≤ 0` ([`ball-soundness.md` §3](ball-soundness.md)). A ball that touches the negative real ray from above is a cut, and a cut is undecided. There is no outward ball that stays off that cut. A ball strictly off the ray keeps a bounded `atan2`, not `atan2Fast`. A ball never proves that a point lies exactly on the cut.
- Infinities and poles. A non-finite center or a non-finite radius from rounding is overflow, not a number. A certified infinite part is an exact point `+∞` or `−∞` from the exact layer, one part at a time. A pole of `tan` is the angle ball meeting an odd multiple of `π/2` while also meeting points that are not that multiple: unverified, which matches today's pole flag. Containment in a pole tolerance does not prove the angle is that multiple.
- Series (B1/B2). The shortcuts in `library.ts` (`SERIES_ODD` −241, `SERIES_POLY` −61, `SERIES_WIDE` −20, `SERIES_REL` −480) become a Taylor polynomial evaluated as a ball, plus a remainder bound in the radius. The signed tails are [`ball-soundness.md` §5](ball-soundness.md). "At most the next term" holds for a real alternating series and does not transfer to a complex ball: at `0.9i` with one term, the arctan tail is about 0.572 and the next term is 0.243. All 28 rows of those tails, on complex circles, held ([`ball-checks/series_tails.log`](ball-checks/series_tails.log)). `√(1+x) − 1` and `cos x − 1` use the exact identities in that section, not a series. The large-`|z|` arcsin branch stays undecided until a proven bound on the dropped terms exists. If the signed remainder still forces both ends of an interval to the same digit text, those digits are certified. If the remainder ball contains 0, the result is a labelled bound or undecided, never exact 0.

### Exact layer

The ball refuses a point it cannot enclose. `0`, `−1`, `i`, `π`, and `ln(−1)` are circuits that pass through `ln 0` and the cut, so a bare ball overflows or cuts, and that refusal is right for the ball. `0`, `−1`, and the screen's `ln(−1)` come from the rules below. The stored words for `i` and `π` do not: the same-node rule does not see the same node on both sides of their cancellation, and `e` is not a table entry. Their displays stay must-keep digit claims. A builder mark is not a rule, and a new identity is the wider domain §1 already puts out of scope. That is the contradiction with trusting "the builder proved this imaginary part is exactly 0" or "`provenInteger` says this leaf is the integer": #15 certified a pasted literal from its stored float (`RESUME.md` on `cursor/long-literal-wire-a4e8`; `exact.ts` returns the `int` mark and skips the walk), and #35 certified a real infinity from a sign mark while a finite imaginary part was still there (`RESUME.md` on `cursor/v11-directed-infinity-1253`, M1 and M2: `ln(ln(0))*i` came out 0, and `ln(ln(0)*i)`, `(inf*i)/2`, `sqrt(ln(0)*i)` were confident and wrong). `docs/known-limitations.md` records the same pattern: the word `111E1E1E1EE11EE` displays as exact `−1` while it differs by about `10^(-1656520)`, and `6.103×10^(−120)i` added to itself displays half the sum. The `unver` row above is a refusal, not a value. The `int` row is the same kind of fact. Neither fires a rule.

A side condition is a fact a ball already proved about a child: the imag interval sits inside `(−π, π)`, the rectangle excludes 0, the rectangle misses the cut, or the child is finite. A side-table flag never satisfies one. When a rule fires, the exact point and the rule that produced it travel on the wire. That field is new, so the PR that adds it bumps `WIRE_VERSION` in `lib/eml/wire.ts`. The worker checks the shape and the ball condition again. A token that only carries `int`, a decade, or a direction is not the point.

The rules below are the signed list. R1 and R2 are mathbot's sign-off in [`ball-soundness.md` §11](ball-soundness.md), not proposals. "Not in the table" means the operation is not a row, so only a ball applies. It is not a claim that the value lies outside the span. Whether `exp(a)` for `a ∈ Q(i) \ {0}` lies in the span is open (`a = 1` is the question of `π + e`).

1. The `one` token is the exact point `1 + 0i`. No other leaf is exact. There is no `−0` leaf in this list.
2. The composed log of the literal 1 is `+0`. The node is the three-gate shape `eml(1, eml(eml(1, 1), 1))`, and the K 7 word `111E1EE` is that shape. This is not the gate's own `ln(1)`. The inner logarithm of one `eml` applied to the literal 1 is the table row `ln(1) = +0` below, a different node.
3. `ln(exp x) = x` only when the node is structurally a log of an exp, and a ball of `x` proves `Im x ⊂ (−π, π)`. The result is the exact point `x` already was. If `x` is not an exact point, the rule does not create one.
4. `exp(ln x) = x` only when the node is structurally an exp of a log, and a ball of `x` proves the rectangle excludes 0 and does not meet the cut. Same restriction: no new exact point.
5. `ln(+0) = −∞`, with imaginary part `+0`. The argument has to be the exact point `+0`. A ball that contains 0 does not fire. `−0` does not fire. Today's gate log of a literal `−0` is `−∞ − iπ` (`lnEml` at `exact.ts:120`), and no rule here produces that `−0`.
6. `exp(−∞) = +0` and `exp(+∞) = +∞`, both for an exactly real infinity. `exp(−∞ + iθ) = +0` for every finite exact `θ`. That zero is `+0`, not the signed zero `expZ` returns today (`exact.ts:101`).
7. **R2, signed.** The infinity rows below. An infinity is an exact point only beside a proved exactly-real partner. "Proved" means a realness rule: the `one` token, or exp or gate log of a proved-real argument on its continuous side. A ball around 0 is not that proof, and a side-table sign mark is not that proof.
8. Gate log of an exact negative real point this list already returned (imaginary part exactly `+0`, real part `< 0`): `ln|x| − iπ` on the lower bank. The screen's composed log is `ln|x| + iπ`. A ball that only meets the cut does not fire. The result is in the table only when `ln|x|` is a table entry, so the only negative real it returns is `−1`: gate `ln(−1) = −iπ`, composed `ln(−1) = +iπ`. It does not cover `ln(i)`.
9. **R1, signed.** The table below, plus the same-node rule: `x − x = +0` when both operands are the same hash-consed finite node. That is a shape rule. It is not equality of values, so it does not put `e` in the table, and it does not fire on `1−1` or on the residue rows. "Both children exact" is not a row.

The unverified placeholder never becomes the point 0. A dropped term stays unverified. No rule reads `unver` or `int`.

**R1, signed. The exact domain** is `Q(i) + Q(i)·π`, together with the exact real infinities `+∞` and `−∞` (imaginary part proved `+0`) and the four directed infinities of rule 7. Written out, a finite point is `a + bπ + (c + dπ)i` with `a, b, c, d` rational. The zero element is `+0`. `−0` is not in the domain. Equality is equality of the four rationals, because `π` is irrational: a real part `r + sπ = 0` with `r, s` rational only when both are 0. Transcendence is not required for that step. Sign of a nonzero `r + sπ` is one rigorous enclosure of `π`. There is no numeric zero test.

**Rule 9 is this table.** An input that is not one of these rows is not in the table, and only a ball applies. `eml(x, y) = exp(x) − ln(y)`, and the `ln` in that formula is the gate log. The values `exp(k·iπ/2)` are read from the table. They are never a computed `sin` or `cos`: a decimal.js `sin(π)` is dust or `−0`, and that would pick the wrong bank.

| Operation | In the table | Value |
| --- | --- | --- |
| `x ± y`, both finite points in the domain | yes | componentwise |
| `x − x`, same hash-consed finite node | yes | `+0`. `0 − 0` is `+0` |
| `q·x` and `x/q`, `q ∈ Q(i)`, `q ≠ 0` | yes | scalar. A pure circuit has only `eml`; this row is the builder mul and div |
| product of two points that both have a nonzero π coefficient | no | `π²` is not in the span. `(−i)·(iπ) = π` is the scalar row, because `−i ∈ Q(i)` |
| `exp(q·iπ)`, `q ∈ (1/2)ℤ` | yes | `q` mod 2: `0 → 1`, `1/2 → i`, `1 → −1`, `3/2 → −i` |
| `exp(+∞)`, `exp(−∞)`, exactly real | yes | `+∞` and `+0` |
| `exp(+∞ + i·kπ/2)`, `k ∈ ℤ`, the real part an exact `+∞` and the angle a table imaginary | yes | the directed infinities below |
| `exp` of any other point | no | `exp(1)` is not a row. Whether `e` lies in the span is open |
| gate log of `1`, `−1`, `i`, `−i` | yes | `+0`, `−iπ`, `iπ/2`, `−iπ/2` |
| gate log of `+0` and of `+∞` | yes | `−∞` and `+∞` |
| gate log of anything else, including `−∞`, `2`, and `π` | no | |

**R2, signed. Infinities.** The partner of an exact real infinity has to be proved exactly real, as rule 7 says. A finite imaginary part beside an infinite real part is per-part (real `±∞`, imaginary a ball) or a refusal. It is never a real `±∞` and never `±∞i`. That is the #35 pattern, and it is the live bug `ln(0)−1`, which shows `−∞ i` when the imaginary part is not discharged.

- `ln(+∞) = +∞`. The `−1` trace uses this row.
- `ln(+0) = −∞`. `exp(+∞) = +∞`. `exp(−∞) = +0`.
- Gate `ln(−∞) = +∞ − iπ` in the point code (`complex.ts:102-108`, `exact.ts:133-134`), the same `−π` as gate `ln(−1)`. The imaginary part is not real, so this value is **not in the table**. It is a per-part value at most: real `+∞` exact, imaginary `−π` exact. It never becomes a real infinity. `eml(a, −∞)` does not fire as a real infinity.
- On the exp side of `eml`, a proved exactly-real finite partner (a table real, or a proved-real finite ball such as `exp(1)`, whose imaginary part is `+0` by the realness rule) minus `ln = −∞` is exact `+∞`. The same partner minus `ln = +∞` is exact `−∞`. The partner does not have to be a table point. In `eml(1, +0)` the partner is `e`, which is not a table entry, and the infinity is.
- On the ln side, `exp = +∞` minus a proved exactly-real finite value is exact `+∞`.
- `∞ − ∞` is not in the table. `+∞ − (−∞)`, both proved real, is `+∞`. `0·∞` is not in the table.

**Directed infinities, hotfix #32, option (a).** On `main`, a directed infinity is built as `E(E(+∞, turn), 1) = exp(+∞ − gate-log(turn))` (`library.ts:519-523`), with `turn ∈ {1, −i, −1, i}`. Those are `exp(+∞ + i·kπ/2)` for `k = 0, 1, 2, 3`, using gate `ln(−1) = −iπ` and gate `ln(−i) = −iπ/2`. The exact layer keeps the four points `∞·i^k` (`k` mod 4). The only producing rule is that exp row. The per-part reading is `(±∞, +0)` or `(+0, ±∞)`, and the zero is exact because the table says so, not because of the `1e-15` snap. `exp(+∞ + iθ)` for any other exact `θ` is undecided. A negative integer power of one of these points is `+0`. This is what keeps `(inf*i)^3` certified as `−∞i`, and the other #32 rows in `check.ts` (`(inf*i)^5` → `∞i`, `inf*(inf*i)` → `∞i`, `(-inf)^3` → `−∞`, `(inf*i)^4` → `∞`, `(inf*i)^-1` → `0`) certified. `(inf*i)^0.5` stays unverified. Option (b), dropping those rows to unverified, would be a regression. It was not chosen. It would have needed Jimmy1 and Ben to accept the loss.

The screen expression `1−1` is not the same-node rule and not the addition row. Its circuit is not in the table at `exp(1)`, so only the ball applies, and §6 stands: the result is "0 to N digits", not `+0`.

Worked derivations. Lower bank inside the gate, composed log on the screen.

- **0.** `111E1EE` is rule 2, the three-gate composed log of the literal 1. Exact `+0`.
- **−1.** The K 15 word is `11111E1EEEE11EE`, seven gates. Gate 1, `eml(1, 1) = exp(1) − ln(1)`: the table's `ln(1) = +0` fires and `exp(1)` is not a row, so the gate is the real ball of `e`, not an exact point. Gate 2 is the next tower step and is not a row either. Gate 3 is the rule 2 shape and returns `+0` without using that ball. Gate 4 is `eml(1, +0) = exp(1) − ln(+0) = exp(1) − (−∞)`. The partner is proved exactly real and finite (imag `+0` because the argument is exact real, and a ball proves the real part finite), so rule 7 returns `+∞`. Gate 5 is `eml(1, +∞) = exp(1) − ln(+∞)`, and `ln(+∞) = +∞`, so rule 7 returns `−∞`. Gate 6 is another `eml(1, 1)`, again the real ball of `e`. Gate 7 is `eml(−∞, eml(1, 1)) = exp(−∞) − ln(eml(1, 1))`. Rule 6 returns `+0`. The logarithm's argument rewrites, by `ln(1) = +0`, to the exp of the literal 1, so rule 3 returns that literal: `Im 1 ⊂ (−π, π)`, and the rule does not promote gate 6 itself into an exact point. The table subtracts `+0 − 1 = −1`.
- **ln(−1).** The screen's `ln` is the composed log of the exact point `−1`. Rule 8 returns `+iπ`. The golden text is `3.14159265359i`. The lower-bank log of the same point is `−iπ`. A ball around `−1` would be a cut and would not certify either.
- **i.** The K 57 word in `lib/eml/best-known.json` is `111111111EEE1EE11EE1EEEE1EE1111111E1EEEE11E1E1EEEE1EE1E1E`, 28 gates. Gates 1–15 are not in the table: each is an exp tower on `eml(1, 1)`, and `exp(1)` is not a row. Gate 16 is the rule 2 shape `eml(1, eml(eml(1, 1), 1))` and returns `+0`. Gate 17 is `eml(1, +0) = +∞`. Gate 18 is `eml(1, +∞) = −∞`, using `ln(+∞) = +∞`. Gates 19–21 are the tower `eml(eml(eml(1, 1), 1), 1)` and are not in the table. Gate 22 is `eml(−∞, that tower)`. Its logarithm is not a gate log of `±1` or `±i`, so it is not a row, and rule 3 does not return a point for an argument that is not already exact. Rule 8 does not apply to a ball. Gate 23 is `eml(1, gate 22)`. Numerically that is `exp(1) − ln(−e^e)`. The gate log, lower bank, is `ln(e^e) − iπ`, so the difference is `(e − e) + iπ`. The two real parts are the value `e`. They are not the same hash-consed node: one side is the exp of the literal `1`, and the other is the log-magnitude of gate 22. The same-node rule does not fire, and cancelling `e − e` by value is exactly the step mathbot rejected. `e` is not a table entry. Gates 24–28 each read a child that is not in the table. The last gate is not `exp(iπ/2) = i`. The stored word does not produce exact `i`. Today's display of `i` still has to be kept, as digits of a signed ball. A ball near `i` is not the exact point. The table route, which this word does not take, is gate `ln(i) = iπ/2` and then `exp(iπ/2) = i`. Rule 8 does not justify `ln(i)`, because `i` is not a negative real.
- **π.** The K 93 word is `1111111111E1EEEE11E1E1EEEE1EEE1EE111111111EEE1EE11EE1EEEE1EE1111111E1EEEE11E1E1EEEE1EE1E1EE1E`, 46 gates. Gates 1–2 are not in the table. Gate 3 is rule 2, `+0`. Gate 4 is `+∞`. Gate 5 is `−∞`. Gates 6–8 are the real tower and are not in the table. Gate 9 is `eml(−∞, that tower)` and is not a row, the same refusal as gate 22 of `i`. Gates 10–31 are not in the table. Gate 32 is rule 2 again, `+0`. Gate 33 is `+∞`. Gate 34 is `−∞`. Gates 35–37 are the tower. Gate 38 meets that tower with `−∞` and is not a row. Gates 39–46 are not in the table. The same-node rule does not see one node on both sides of a subtraction anywhere in this word except `eml(1, 1)`, which is not the cancellation. The previous trace routed `ln(i)` through rule 8. Rule 8 only covers negative reals, so it cannot. The table route, once an earlier gate has actually returned the exact point `i`, is gate `ln(i) = iπ/2` and then `(−i)·(iπ) = π`, the scalar row. This word never puts exact `i` on that row. The displayed `π` stays a must-keep digit claim.

## 4. Decisions, digits, adaptive loop

Every numeric claim a ball makes is containment of an inequality. `cut` or overflow refuses every numeric claim. A timeout does the same and shows "couldn't verify".

- **Digits.** A ball that excludes 0 always prints its proven digits. Print `n` digits of a part only when both ends of that part's interval round to the same text. This is an inequality, not a claim that the center is exact. A half-unit test on the radius is not the rule. Digits past the radius are not stored and not shown. `sin(10^22)` prints as many digits as the argument-reduction bound actually proves, which may be none. A ball that excludes 0 never shows "0 to N digits", however small the value is.
- **Labelled bound.** This label is only for a ball that contains 0. `N` is the largest integer such that the radius proves `|x| < 10^(-N)`. The screen prints "0 to N digits". It is the replacement for a certified 0 that came from dust, a cancellation snap, or a vanished value. It is not exact 0. `1e-500`, `exp(-1200)`, and `1e-400*(1+1e-100)-1e-400` exclude 0 and keep today's certified digits. They do not wear this label, and the `10^(-480)` cutoff must not turn them into exact 0.
- **Nonzero and sign.** If the rectangle excludes 0, the value is certified nonzero and the digits above are printed. If a part's interval lies in a half-line (`Re > 0`, `Im < 0`, and so on), that sign is certified. An exact infinite sign is a point from the closed rules, not a ball that overflowed.
- **Integer.** An integer is an exact point a closed rule returned. A ball does not become an integer by lying near one. `2.3 ± 0.1` lies inside `(1.5, 2.5)` and is not the integer 2. `1 + 10^(-130)` is not the integer 1. The `int` mark is not the rule.
- **Exact zero.** Only the point `+0`: rule 2, `exp(−∞)`, the same-node rule, or `0 − 0`. Rule 5 fires only on that `+0`. No rule produces `−0`. The rule "both intervals inside `10^(-480)`" is dropped. It would certify `1e-500` and `exp(-1200)` as exact 0, and those two stay certified nonzeros. It would also fail `1-1`, whose radius at the cap is about `10^(-478)`. There is no separation bound in this design that would let a class of tiny balls count as zero. `1-1` prints "0 to N digits" from that radius. The table row `1 + (−1) = +0` does not apply to that circuit.
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

**(b) Switch.** The screen and the returned decision follow the ball and the exact layer. Q1–Q8 are answered (§8). The switch still waits on the tests named in [`ball-soundness.md`](ball-soundness.md) being in CI, and the same PR updates `README.md`, `docs/known-limitations.md`, and the UI. Those three still say a small residual is treated as 0 and that an exact 0 times a finite factor stays a certified 0. The UI prints "0 to N digits", with `N` from the radius as in §4, only for a ball that contains 0. Exact 0 is a point a closed rule returned. A ball that excludes 0 prints its digits. The golden file moves only on lines listed below, each with the 2000-digit check when the value or the certification changes.

**(c) Delete.** After the switch, each old mechanism stays in CI as a reverse shadow. One mechanism is removed per PR, and only after that reverse-shadow period. The mechanisms are `scrubDust`, `confirmDust`, `settleResidue`, `hiddenComponent`, the `lossGap` / `tiniest` retry, the `cosSin` point snap, and the `axisInfinity` `1e-15` snap. Float evaluation stays.

Expected disagreements, current engine wrong, ball right once the bounds are signed. Each of these is a listed certified-to-unverified line, or a listed digit change, and each needs the 2000-digit check:

- `((1+10^(-k))-1)+i·c` for `k` in 110..136 prints `c·i` and drops the real `10^(−k)`. Measured on this SHA: `((1+10^(-130))-1)+i/2` prints `0.5i`, `((1+10^(-136))-1)+i*3/2` prints `1.5i`, `((1+10^(-110))-1)+i*10^10/3` prints `3333333333.33i`.
- `(i*(1+10^(-124))-i)*i+i*10^10/3` prints `3333333333.33i` and drops the real `−10^(−124)`. Same on `(i*(1+10^(-130))-i)*i+i/2`, which prints `0.5i`.
- `sin` / `tan(10^22)` and `cos(10^7)` print a dozen digits the reduction does not justify. Fewer digits, or unverified, is the expected change. Matching the point engine's digits with a huge radius is a failed display rule.
- `tan(1e100)` and `cos(1e100)` are the same class.
- `1-1` is a certified 0 today by snap. After the switch it is "0 to N digits", `N` from the radius. The circuit is not in the table at `exp(1)`, and the two operands are not the same node, so neither the addition row nor the same-node rule returns `+0`. Keeping today's exact 0 would be the dropped cutoff coming back.

The corpus also carries the known wrong answers, so a builder mark cannot certify them again:

- **#15, pasted literals.** A long decimal whose stored float is not the text. The rounded float is not a known point. `A−1` at 479 and 480 digits, and 479 nines times 2 minus 2, stay unverified. The square, `sqrt`, and `sin` of the 41-digit paste `1.000…1` use the text, not the float.
- **#35, directed infinities.** `ln(ln(0))*i` is not 0. `ln(ln(0)*i)`, `(inf*i)/2`, `(ln(0)*i)/2`, `(inf*i)/(1+i)`, and `sqrt(ln(0)*i)` are not confident finite values. `inf^0`, `(-inf)^0`, `(-inf)^3.0`, and `(-inf)^(6/2)` stay unverified. The known-limitations tower `111E1E1E1EE11EE` is not exact `−1`.
- **v1.1 real-part drop, the #33 failing test.** `(i*(1+10^(-124))-i)*i+i*10^10/3` prints `3333333333.33i` and drops the real `−10^(−124)`. Golden marks it `A1-real-drop`. The screen must keep the real part.
- **Wire real-part drop.** `((1+10^(-130))-1)+i/2`, `((1+10^(-130))-1)+i*(1+10^(-130))/2`, and `((1+10^(-136))-1)+i*3/2`. Golden marks these `wire-real-drop`: the real part near `10^(−130)` disappears on the packed wire. The ball keeps it.
- **Live infinity rows**, from `lib/eml/check.ts` and the #41 golden file. `ln(0)`, `ln(0)*2`, `ln(0)*(-2)`, `2*ln(0)`, `(-2)*ln(0)`, `ln(0)*i`, `i*ln(0)`, `ln(0)*i*i`, `sqrt(ln(0))`, `sqrt(ln(0))^2`, `-(sqrt(ln(0)))`, `(inf*i)*(inf*i)`, `(inf*i)^3`, `(-inf)^3`, `ln(0)^2`, `ln(0)^3`, `(ln(0)*i)^2`, `(ln(0)*i)^3`, and `1/0`. `ln(0)*0`, `sin(ln(0))`, `cos(ln(0))`, and `tan(ln(0))` stay undefined.
- **Live rows quoted as reviewbot wrote them.** `ln(0)-1`, `ln(0)+i`, and `exp(ln(ln(0))*i)`. If the partner of `ln(0)` is proved exactly real, the table says `ln(0)-1` is `−∞ − 1 = −∞`. The live value `−∞ i` is the case where a finite imaginary part survived: per-part or undecided, not an exact real infinity and not `±∞i`. `ln(0)+i` is an infinity plus a non-real point, so it is not a directed infinity from the exp row. `exp(ln(ln(0))*i)`: gate `ln(−∞)` is not in the table (per-part `+∞` and `−π`, not `+∞ + iπ`), and multiplying that by `i` is not the exp row, so the exp is not a directed infinity. Collapsing `ln(ln(0))` to a real `+∞` first is the #35 sign-mark bug, not a reading of this row. The spelling is the one above; none of the three has a second form in the suite. The #32 rows in the live list, `(inf*i)^3`, `(inf*i)^5`, `inf*(inf*i)`, `(-inf)^3`, stay certified under option (a).
- **Rows whose text today depends on `−0`.** The #41 golden file (`lib/eml/golden/golden.txt` on `cursor/golden-harness-bbcd`, 154 expressions) has no exact text that is the signed zero `−0`. Its float column shows `−0` for `exp(10^(-1000))-1`, `exp(1e-432)-1`, `tan(10^(-5000))`, `tan(1e100)`, and `tan(1e22)`. Those are underflow displays. The exact column is "couldn't verify" or a nonzero, except `exp(1e-432)-1`, whose exact text is `1×10^−432`. The rows that do depend on a `−0` are locked in `check.ts`, not in that golden file: `ln(-0)` (composed log `−∞` with a positive imaginary part; the gate log is `−∞ − iπ`), `sqrt(-0)` (the exact real part stays negative), `1/(-0)` and `1/sqrt(-0)` (real `−∞`). The half-turn float check `cexp(−∞ ± iπ) = (−0, −0)` is the same family. The exact layer's `exp(−∞ + iθ)` is `+0` for every finite exact `θ`, so none of these is a table row. A literal `−0` stays a leaf the rules do not produce.

Must stay certified. These are certified and correct today. Losing the value, or printing exact 0 or "0 to N digits" for a row that excludes 0, fails the PR:

- `0`, `−1`, and the screen's `ln(−1)` (`+iπ`, golden `3.14159265359i`), by the derivations above. The gate log of that same `−1` is `−iπ`. `−2`, the other negatives, `i`, and `π` stay at today's certified text. The table produces `−1` and the screen's `+iπ`. It does not produce `i` or `π` from the stored words, and the same-node rule does not either. Losing any of these displays fails the PR. Certifying `i` or `π` by cancelling `e − e` as values fails it too. The seed overflows because the ball will not invent the point. `(inf*i)^3` stays `−∞i` by option (a), and the other #32 rows named above stay with it.
- `1e-500`, `exp(-1200)`, and `1e-400*(1+1e-100)-1e-400`. Each excludes 0 and is a certified nonzero today (`1e-400*(1+1e-100)-1e-400` is `1×10^−500`). The seed's cut is a blown radius, not the target. The digits are what both ends of a signed ball print. Exact 0 here is the severity-1 failure.
- `1e-400*pi+1e-400` stays `4.14159265359×10^−400`. `exp(-1000)-exp(-1001)` stays `3.20861797491×10^−435`. The `−1×10^−450` rows stay that text: `1e-400-1e-400*(1+1e-50)` and `(1e-400)*3/3-(1e-400)*(1+1e-50)`. Those are the kept-value rows in the tiny-ratio and residue tests, not the cancellations that are honestly 0.
- `ln(1+10^(-130))` stays `1×10^−130` once a remainder valid on the complex rectangle forces both ends to that text. `sin(pi/6)` stays `0.5` once a signed bound forces both ends. Until that bound is signed, an unverified result is a listed line, not a quiet seed patch.

Exact-zero residues are identities, and they are not in the table, so the table does not return `+0`. The ball contains 0 and the screen shows "0 to N digits", not exact `+0`. The rows, quoted as reviewbot wrote them: `exp(ln(1e-400))-1e-400`, `1e-400*1.5/1.5-1e-400`, `1e-400/2*2-1e-400`, `1e-400/0.5/2-1e-400`, and `(2^0.5)^2-2e-400`. The last spelling is ambiguous. The residue tests write the scaled form `1e-400*(2^0.5)^2-2e-400`, and the unscaled identity is `(2^0.5)^2-2`. All three are in the corpus; none of them is exact `+0`.

Stable residues follow the same rule. The radius can sit still while precision climbs. `1e-100*1.5/1.5-1e-100`, and the same pattern at `1e-50`, `1e-150`, and `1e-200`. Reviewbot records today's certified text of the `1e-100` row as `5×10^−201`. That text is the disagreement: after the switch the ball contains 0, so the screen is "0 to N digits" or unverified, not exact `+0` and not `5×10^−201`. The suite also has `1e-200*(2^0.5)^2-2*1e-200`, which is the sqrt form at that scale, not a second spelling of the `1.5` row.

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

## 8. Questions for mathbot, answered

Mathbot signed all eight on 2026-11-21. The write-up is [`ball-soundness.md`](ball-soundness.md). Each answer stops blocking the switch once the test named there is in CI. The questions are not open.

1. **B3, `cexp`. Answered.** [`ball-soundness.md` §2](ball-soundness.md). The Lipschitz shape is right. The seeded `exp(ρ) − 1` and the component ulp are not. Use `E(ρ)` and a charge of `8u` on the magnitude, on the upward radius clone. Past the π cap the result is undecided. The prototype misses 0 of 6024 inputs; the seed missed 654 of 3010 and 814 of 2004 ([`ball-checks/proto.log`](ball-checks/proto.log)).
2. **B4, the closed ray. Answered.** [`ball-soundness.md` §3](ball-soundness.md). The fix is `imLo ≤ 0`. A ball that touches the negative real ray from above is a cut, and a cut is undecided. There is no outward ball that stays off that cut. The gate bank is the lower one: `ln(−1) = −iπ`, and `ln(−∞) = +∞ − iπ` as a per-part value, not a table point.
3. **B6, rounding. Answered.** [`ball-soundness.md` §0 and §1](ball-soundness.md). Three clones: centre at precision `p` half-up, radius at 20 digits rounding up, lower bounds at 20 digits rounding down. Charges are the absolute amounts in the §0 table. `sin` and `cos` are 2u absolute. `atan2` is 2u absolute. `atan2Fast` stays excluded.
4. **B1/B2, remainders. Answered.** [`ball-soundness.md` §5](ball-soundness.md). The tails there are the bounds. All 28 rows held on complex circles ([`ball-checks/series_tails.log`](ball-checks/series_tails.log)). `√(1+x) − 1` and `cos x − 1` are identities. Large-`|z|` arcsin stays undecided until a proven bound exists.
5. **Exact points. Answered.** [`ball-soundness.md` §4 and §11](ball-soundness.md). The domain and the table are §3 of this note. No builder mark is a side condition. No separation bound is assumed. `1e-500` and `exp(-1200)` stay certified nonzeros. `e^(−e^(e^e))` is a nonzero far below every cutoff this engine can reach. The K 57 and K 93 words are not table derivations. Their displays stay.
6. **Infinities. Answered.** [`ball-soundness.md` §6 and §11](ball-soundness.md). A ball's intervals are finite. Infinite points come from the exact layer: real `±∞`, and the four directed points `∞·i^k` from `exp(+∞ + i·kπ/2)` only. A finite imaginary part beside an infinite real part is not a real infinity. Overflow is a non-finite centre or radius, a trip past `maxE`, an underflow to 0 past `minE`, a NaN, or `Precision limit exceeded`. The `1e-15` snap is not an answer.
7. **Rectangle. Answered.** [`ball-soundness.md` §7](ball-soundness.md). The model is the rectangle in §3. Lipschitz bounds use `ρ = rr + ir` once. `cexp`'s output is not inflated a second time.
8. **Per component. Answered, not blocking.** [`ball-soundness.md` §8](ball-soundness.md). One component's digits or sign may be certified while the other, if it contains 0, is a labelled bound or undecided. A cut or an overflow refuses both. Neither may print the undecided component as exact 0.
