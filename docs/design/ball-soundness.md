# Ball-engine soundness rules

Credit: mathbot, 2026-11-21. Design input for `docs/design/ball-engine.md`. This note does not change the engine.

The checks it reports are in `docs/design/ball-checks/` (`proto.mjs`, `proto.log`, `ref.py`, `series_tails.py`, `series_tails.log`). Paths in the note that start with `/workspace/` are where those checks were run. `proto.mjs` still imports decimal.js from that machine.

---

Ball-engine soundness rules (mathbot → compscibot, review item E2). 2026-11-21, about 3:50 PM ET (§11 added on the steer about R1/R2). These answer the 8 questions in §8 of `docs/design/ball-engine.md` (PR #40, head `137a0b6`), checked against `main` `d6be0d1` (`lib/eml/enclose.ts`, `lib/eml/complex.ts`, decimal.js 10.6.0). The evidence is in `/workspace/eml-hub/review-verify-B.md` (B3, B4, B6). The numeric checks are in `ball-checks/` (§10). This is design input only: nothing in the repo was edited.

**What blocks.** Questions 1–7 block the switch; question 8 doesn't. That's reviewbot's split and the PR's, and I agree with it. Q7 is already decided (rectangle). With the rules below, Q1–Q6 have answers. They stop blocking once each rule's test listed here is in CI.

## 0. Notation and trust model

- **Precision and unit.** `p` is the centre clone's precision, between 120 and 480. **u = 10^(1−p)**. One correctly rounded centre operation on a value t errs by at most ½·ulp(t) ≤ (u/2)·|t|. One op documented to "≤ 1 ulp" errs by at most u·|t|.
- **The ball.** It is the rectangle Z = [x ± r_x] × [y ± r_y], with centre c = x + iy.
  - ρ = r_x + r_y is an upper bound on |w − c| for every w ∈ Z.
  - m = (|x| + r_x) + (|y| + r_y) is an upper bound on |w| over Z.
  - d = max(|x| − r_x, |y| − r_y, 0) is a lower bound on dist(0, Z).
  - All of these are computed as in §1.
- **decimal.js error budgets.** These are what the engine charges for each library function. They come from the decimal.js docs and its source (`node_modules/decimal.js/decimal.js`).

| Op (centre clone, ROUND_HALF_UP) | Charge | Basis |
|---|---|---|
| `add sub mul div sqrt` | u·\|result\| (that is, 1 ulp; true error ≤ ½ ulp) | correctly rounded |
| `exp` | u·\|result\| | documented as "always correctly rounded" |
| `ln` | u·\|result\| | documented as "almost always" correct, at most 1 ulp off |
| `sin`, `cos` of a real | **2u absolute** | not documented. The source reduces mod π at p + max(e, sd) + 7 digits, then rounds once. Measured error is ≤ 5e-301 at p = 300 (u = 1e-299) for arguments up to 1e600 |
| `atan2` | **2u absolute** (≤ 2 ulp of π) | computes atan at p + 4 digits, then one rounded ±π add |

- **Exceptions.** Any of these makes the result undecided (overflow class), never a number:
  - `sin`/`cos` throw `Precision limit exceeded` when p + max(e, sd) + 7 > 1025, because π is stored to 1025 digits. At p = 480 that's an argument whose exponent or digit count is above about 538. The engine must catch this.
  - exp or any other op overflows past `maxE`, or underflows to 0 past `minE`. The defaults are ±9e15.
  - NaN.
- **Startup self-test.** This copies interval-bounds.md §0. Run about 200 reference values from mpmath for `exp ln sin cos atan2 sqrt` at p = 120 and p = 480, and assert every error is within the budget above. If it fails, certification is off. That keeps the trust model a measured fact, not an assumption about the library.

The standard behind all of this is midpoint–radius ("ball") arithmetic as in Arb (Johansson, *Arb: efficient arbitrary-precision midpoint-radius interval arithmetic*, IEEE TC 2017) and Rump's midpoint–radius interval arithmetic. The centre is computed at high precision with ordinary rounding. Every rounding and truncation error is bounded explicitly and added to a radius that is itself computed with upward rounding, at low precision.

## 1. Q3 / B6: directed rounding (blocking; answered)

**Rule.**
1. **Clones.** Each evaluation context owns three Decimal clones:
   - `D`, the centre clone: precision p, ROUND_HALF_UP.
   - `DU`, the radius clone: **precision q = 20, ROUND_UP**.
   - `DD`, the lower-bound clone: q = 20, ROUND_DOWN.

   ROUND_UP rounds away from zero, so on a non-negative quantity it is the ceiling. Radii are never negative.
2. **Every radius** is a sum and product of non-negative terms, evaluated on `DU`:
   - the input radii;
   - the Lipschitz term (§2);
   - the centre's error, from the §0 table, as an **absolute** amount;
   - any series remainder (§5).

   Moving a value into a clone is exact, because `new DU(x)` does not round; the first operation does.
3. **Subtraction.** On `DU` it is allowed only between exact values, or as (upper bound) − (lower bound). A **lower bound**, such as d, |c| − ρ, or anything that sits in a denominator, is computed on `DD` from exact values.
4. **Transcendental radius ops.** When one runs on `DU` (only `exp` for ρ > 1), multiply the result by (1 + 10^(1−q)) afterwards. ROUND_UP only stays directed for ops that really are correctly rounded.
5. **Never use `exp(d) − 1` on a radius, at any precision.** Use the polynomial bound in §2.
6. **Decisions use exact comparisons of centre against radius:**
   - Re > 0 ⟺ `x.gt(r_x)`;
   - imLo ≤ 0 ⟺ `y.lte(r_y)`;
   - digit ends: compare x ± r_x with the decimal rounding boundaries, exactly or with `DD`/`DU` endpoints.

   Never compute `x − r_x` at precision p with half-up rounding and then test its sign.

**Which ops need which.** k-ulp padding belongs on the centre side and is charged in absolute terms (§0 table). ROUND_UP belongs on the radius side. One `u(result)` per op is enough only for add, sub, mul, div and sqrt of exact operands. It is not enough for `exp`, `ln`, `sin`, `cos`, `atan2` or any compound (B6: `ln(√½ + √½ i)` missed by 3.1e15×). Keeping q low (M7) costs nothing in soundness, because rounding up can only make a radius bigger. It keeps radius arithmetic cheap: 20 digits, where the seed spends 300.

**Why.** An upward-rounded sum of upper bounds is an upper bound. Half-up rounding at any precision is not. The one-ulp-per-op rule measures error in the result's own ulp, but the error of a compound op (mag·cos, then sqrt, then ln) is in the operands' ulps.

**Test that catches a violation.** Run the `b6-cln` and `b3-cexp` point sets with zero misses. Also assert `DU.rounding === 0` and `D !== DU` in the context constructor, and that no `exp(…).sub(1)` appears in `enclose.ts` (a lint grep).

## 2. Q1 / B3: `cexp` and the other op bounds (blocking; answered)

**cexp rule.** Input Z, with c = x + iy.
- Centre: M = `x.exp()`, C = `y.cos()`, S = `y.sin()`, and (re, im) = (M·C, M·S), all on `D`.
- Radius, on `DU`, the same for both parts:

```
M↑   = M·(1 + 2u)                                   ≥ e^x
E(ρ) = ρ·(1 + ρ)            if ρ ≤ 1                ≥ e^ρ − 1
     = ρ·e^ρ·(1+10^(1−q))²  if ρ > 1   (or: refuse; such a ball certifies nothing)
r_re = r_im = M↑·( E(ρ) + 8u )
```

**Why.**
- **The Lipschitz term.** |e^(c+δ) − e^c| = |e^c|·|e^δ − 1| ≤ e^x·(e^|δ| − 1), and |δ| ≤ ρ. Then e^ρ − 1 = Σ_{k≥1} ρ^k/k! ≤ ρ + ρ²(e − 2) ≤ ρ(1 + ρ) for ρ ≤ 1, and e^ρ − 1 ≤ ρ·e^ρ for all ρ ≥ 0.
- **The rounding term.** It is charged on the magnitude e^x, not on the component:
  |M·C − e^x·cos y| ≤ |M − e^x|·|C| + e^x·|C − cos y| ≤ e^x·(u + 2u), and the final multiply adds ≤ u·M. That totals ≤ 4u·e^x, plus higher-order terms, which 8u covers with margin. This is the review's "u(mag)" fix.
  - The seed's u(re) fails whenever |re| is a decade or more below M: 654 of 3010 points missed, worst 4.5×.
  - It is *not* specific to cos ≈ 0 (B3.2 showed decimal.js keeps relative accuracy there). It is the product rounding of B3.1.
- **The seed's form.** exp(re + rr)·(exp(rr + ir) − 1) is also a valid Lipschitz factor (e^(x+r_x) ≥ e^x), but it is looser. It becomes unsound only because the `− 1` is evaluated at p (B3.3: the stretch rounds to 0 below 1e-300).

So the answer to PR Q1 is: yes on the shape, no as written. Use E(ρ) in place of `exp(ρ) − 1`, charge 8u·M↑ in place of u(re)/u(im), and run everything on `DU`. For argument reduction when |θ| ≥ 1e6, decimal.js's error stays inside the 2u trig budget up to its π cap (§0). Past the cap it throws, and the result is undecided. The radius already carries the input's own uncertainty in θ (Lipschitz constant 1). That's why `sin(1e22)` keeps only the digits the radius allows.

**Other ops.** All radii are on `DU`, plus the centre's rounding charge from §0.
- **add/sub:** r = r_a + r_b + u·|centre| (per part). The seed's `cadd` is right once its u() is on `DU`.
- **mul**, with a = (a₁, a₂) ± (α₁, α₂), b likewise:
  r_re ≤ |b₁|α₁ + |a₁|β₁ + α₁β₁ + |b₂|α₂ + |a₂|β₂ + α₂β₂ + u·(|a₁b₁| + |a₂b₂|)·3. r_im is the same with the pairs (1,2) and (2,1).
- **reciprocal:** refuse if 0 ∈ W. Otherwise |1/(w+δ) − 1/w| ≤ ρ_w / (|w_c| · d_W), with |w_c| taken from `DD` and d_W from §0. Division is z·(1/w).
- **real sin/cos** of an interval θ ± r: r_out = r + 2u (Lipschitz 1).
- **atan2/Arg of a rectangle that is off the cut (§3):** r_out = ρ/d + 2u. Arg is the imaginary part of the log, and |Δ log| ≤ ρ/d (§3). `atan2Fast` stays excluded. Nothing here bounds its float seed.

**Test.** First, the 3010-point B3 set plus 400 random rectangles with radii from 10^-310 to 10^-1, sampled at corners, edge midpoints, centre and random points: zero misses. This prototype gets 0/3010 and 0/405, worst 0.11× and 1.0×; the seed misses 654/3010. Second, the B3.3 balls 0 + (1e-20 ± {1e-310, 3.4e-299})i: zero misses.

## 3. Q2 / B4: `ln` and the cut, lower bank (blocking; answered)

**Convention, checked.** `lib/eml/complex.ts:136-137` (`clog` → `logArg(z, −π)`) and `enclose.ts:85` both put a negative real on the **lower bank: Arg = −π**. The ±0 cases in `logArg`:
- ln(+0) = −∞ + 0i;
- ln(−0 + 0i) = −∞ − πi;
- −∞ on the axis takes −π.

On that bank the log is continuous from below. That gives the closed lower half-plane {Im ≤ 0} \ {0} as the side that agrees with the ray.

**Rule.** Classify Z with exact centre-vs-radius comparisons, in this order:

| Case | Condition | Result |
|---|---|---|
| contains 0 | \|x\| ≤ r_x **and** \|y\| ≤ r_y | **undecided**, never −∞. The extended value ln 0 = −∞ (with the ±0 rules above) belongs only to a structural zero of radius 0 from the exact layer |
| lower side, including the ray | y + r_y ≤ 0 (imHi ≤ 0) | certify |
| upper side, strictly | y − r_y > 0 (imLo > 0) | certify |
| touches or crosses the ray | imLo ≤ 0 < imHi **and** x − r_x < 0 | **cut**: undecided |
| right half-plane | otherwise (then x − r_x > 0) | certify |

The B4 fix is `imLo ≤ 0`, not `imLo < 0`.

For the certify cases:
- **Centre:** re = ½·ln(x² + y²), with no `sqrt`. im = −π exactly when y is exactly 0 and x < 0, whatever the sign of that zero (`D.atan2(+0, −1)` returns +π). Otherwise im = `D.atan2(y, x)`.
- **Radius, on `DU`:**
  - r_re = ρ/d + u·(1 + 2|re|);
  - r_im = ρ/d + 2u;
  - d comes from `DD`. If d = 0, the result is undecided.

**Why.** In each certify case the bank log L is the restriction of a single analytic branch on a neighbourhood of the convex set Z. For the lower side, the branch is arg ∈ (−3π/2, π/2), cut along the positive imaginary ray. That ray is at distance ≥ |c| from any c with Im c ≤ 0. Integrate 1/w along the segment from c to z, which stays in Z: |L(z) − L(c)| ≤ |z − c| / min_Z |w| ≤ ρ/d. This is sharper than the brief's r/(|c| − r), and implies it, since d ≥ |c| − ρ.
- **Rounding of re:** x² + y² carries relative error ≤ 1.1u, so ln shifts by ≤ 1.2u absolute. Then ln and the halving add ≤ 2u·|re|. Charging it absolutely is what fixes B6: the seed charged u(re) when re ≈ 1e-16, and missed by 3.1e15×.
- **Touching the ray from above:** Z holds points with Arg = −π (on the ray) and points with Arg → +π (just above it). So L(Z) has imaginary spread close to 2π. No ball that doesn't straddle that gap encloses it, and **there is no outward ball that stays off the cut** (the answer to PR Q2). Only the exact layer can do better: a proof that Im is exactly 0 (radius 0) puts the point on the bank, where the "lower side" row applies.

**Test.** First, the 2004-point B6 set plus 605 random rectangles: 0 misses (worst 0.25× and 1.0×; the seed misses 814/2004). Second, the five edge balls:

| Ball | Must give | Prototype |
|---|---|---|
| −1 + (1e-10 ± 1e-10)i (B4) | cut | cut |
| −1 + (−1e-10 ± 1e-10)i | certified, im ∋ −π | −3.14159265349 ± 1.0e-10 |
| (−1 ± 1e-30) + 0i | certified, im = −π | −3.14159265359 ± 1.0e-30 |
| −1 + (0 ± 1e-30)i | cut | cut |
| (1e-30 ± 1e-30)(1 + i) | undecided | undecided |

## 4. Q5: exact zero, integers, equality (blocking; answered and confirmed)

**Rule.**
- **A ball certifies only these:** "this part is nonzero" (its interval excludes 0), "this part has sign s" (its interval lies in a half-line), and "these N digits" (both ends round to the same text).
- **A ball that contains 0** gives a labelled bound ("0 to N digits") or undecided, at every precision including the cap.
- **Exact 0 comes only from the exact layer.** I confirm the PR's list:
  - a structural zero of radius 0;
  - an imaginary part the builder has proved is exactly zero;
  - ±0;
  - ±∞;
  - integer leaves recorded as `int` or `provenInteger`, radius 0;
  - ln(exp x) = x, only when Im x is proved inside (−π, π).
- **No separation bound is assumed.** None is known for EML constants (it is open, and of Schanuel type). e^(−e^(e^e)) ≈ 10^(−1.65e6) is nonzero and far below any working precision. `1e-500` and `exp(−1200)` are the counterexamples to any fixed cutoff. The "both intervals inside 10^(−480)" rule stays dropped.
- **Integer claims.** "This value is the integer n" is an exact point:
  - a recorded integer leaf;
  - `markExactInt` / `integerNode`. R4 is exactly this: `tPow` must route 2^10000 through `markExactInt`, or it is only a 120-digit ball;
  - a structural proof.

  A ball inside (n − ½, n + ½) certifies only the digits it rounds to, never integrality. `1 + 10^(-130)` is not 1, and `1+1` prints the digits `2` as a digit claim.
- **Equality to a named constant** (π, e, golf targets) works the same way. `ballVerdict`'s `certifies` (`enclose.ts:143-148`, "equal" if within 10^(−240)) is a digit-agreement claim, not an identity. Under the switch it may say "agrees with π to 240 digits". "Equal" needs the exact layer. `unequal` from strict separation is sound. B5 is refuted, so `separated` is fine as it is.

**Why.** A ball is a set that contains the value. The only statements it proves are ones that hold for every point of the set.

**Test.** `1-1` with no recorded rewrite, `1e-500`, `exp(-1200)` and `1e-400*(1+1e-100)-1e-400` must never print exact 0. `2^10000` must give the 3011-digit integer through the exact layer. `1+10^(-130)` must never be "integer 1". A fuzz rule: any certified exact 0 or integer must trace to an exact-layer node (assert on the provenance flag).

## 5. Q4 / B1 / B2: series remainders on complex balls (blocking; answered) (M6)

**Rule.** Replace each library shortcut with this:

    the truncated polynomial evaluated in ball arithmetic on Z
    + a remainder bound T(m), added to both r_re and r_im on DU

Here m is the upper bound on |w| over Z from §0. The shortcut stays sound for any truncation degree N. N only affects tightness. Choose it so that T(m) ≤ 10^(−p)·|leading term| where possible. Otherwise the result is a wide ball, which is still sound. **No unmarked shortcut survives.** A bare `return t` (tSinh and tArtanh at |z| < 1e-6) or a fixed three-term `arcsinSeries` is exactly the unbounded remainder B1/B2 found. The real "next term" rule does not carry over to complex balls: for arctan at z = 0.9i with N = 1, |tail| = 0.572 > |next term| = 0.243.

| Function (series about 0) | Coefficient bound | Tail after degree N, valid for \|z\| ≤ m |
|---|---|---|
| exp, and exp − 1 | \|a_k\| ≤ 1/k! | m^(N+1) / ((N+1)! · (1 − m/(N+2))), for m < N+2 |
| sinh, sin (odd N) | 1/k!, odd k | m^(N+2) / ((N+2)! · (1 − m²/((N+3)(N+4)))) |
| cosh, cos, cos − 1 (even N) | 1/k!, even k | m^(N+2) / ((N+2)! · (1 − m²/((N+3)(N+4)))) |
| artanh, arctan (odd N) | 1/k, odd k | m^(N+2) / ((N+2) · (1 − m²)), for m < 1 |
| arcsin (odd N) | binom(2j, j)/(4^j (2j+1)) ≤ 1/k | same as artanh, for m < 1 |
| ln(1+z) | 1/k | m^(N+1) / ((N+1) · (1 − m)), for m < 1 |

**Why.** Each tail is dominated by Σ_{k>N} |a_k|·m^k. With factorial coefficients, successive terms shrink by at least m/(N+2) (or m²/((N+3)(N+4)) for the odd and even series), so the tail is at most a geometric series. With 1/k coefficients, Σ_{k>N} m^k/k ≤ m^(N+1)/((N+1)(1 − m)). This is the same majorant argument Arb uses for its series tails.

**Shortcuts not in the table:**
- **tan and tanh:** don't use a series. Write tan = sin/cos and tanh = sinh/cosh, each with the entire-function tails above and ball division (§2). The Bernoulli coefficients need a radius-π/2 Cauchy bound, which isn't worth it.
- **√(1+x) − 1 and cos x − 1:** use exact identities, not series:
  - √(1+x) − 1 = x/(√(1+x) + 1);
  - cos x − 1 = −2 sin²(x/2).

  An identity like these carries no remainder.
- **The arcsin asymptotic branch** (|z| > 1e10 → ±i(ln 2 + ln(∓iz))): either
  - evaluate the closed form −i·ln(iz + √(1 − z²)) with balls, choosing the sign branch so the sum doesn't cancel; or
  - keep the shortcut and add a signed bound on the dropped O(1/z²) terms, with that bound recorded as the remainder.

  Until one of those exists, it is undecided. It must not be certified.

**Test.** The B1/B2 regressions:
- `sinh(5e-7)-5e-7` ≈ 2.0833e-20;
- `artanh(5e-7)-5e-7` ≈ 4.1667e-20;
- `(arcsin(1e-5)-1e-5-(1e-15)/6)*1e25` ≈ 0.0750000000044643;
- the imaginary part of `(arcsin(1e11)+i*ln(2e11))*1e23` ≈ 2.5.

Each must be either right in every certified digit, or undecided. On top of that, a randomized check: on |z| = m for m ∈ {1e-6, 1e-3, 0.1, 0.5, 0.9} and N ∈ {1, 3, 7, 11}, |f − poly| ≤ T(m). Done for all 7 rows (§10), with no violation. The ratio tends to 1 as m → 0, so the bounds are tight, not loose.

## 6. Q6: infinities (blocking; answered)

**Rule.** A ball's intervals are finite. Infinite points come from the exact layer only, one part at a time:
- **ln of a structural zero:** re = −∞ (exact), with im following `complex.ts` `logArg`: +0 → 0, and −0 on the real part → −π.
- **ln of a value with an exact infinite part:** re = +∞. im is the Arg of the direction, as a ball if it is finite and off the cut, and undecided otherwise.
- **exp, where Re is exactly −∞ and Im is a finite ball or point:** the structural zero. exp of −∞ + finite is 0, whatever the angle.
- **exp, where Re is exactly +∞:** re = +∞·cos y and im = +∞·sin y. Each part is a signed exact ∞ only if the cos or sin interval of y excludes 0 (sign certified). If that interval contains 0, the part is undecided. If y is an exact point with cos y or sin y exactly 0 (an exact-layer fact), use the `complex.ts` point convention for that part.
- **Sums:** finite ball + exact ±∞ = exact ±∞ on that part. ∞ + (−∞) is undecided.
- **Overflow (refuses every claim):**
  - a non-finite centre or radius from a finite ball;
  - exp or any other op past decimal.js `maxE`;
  - an underflow to 0 past `minE`. That is **not** 0;
  - a NaN;
  - a `Precision limit exceeded` throw.

**Why.** A finite input ball can't prove that its image is infinite. Only a structural ±∞ or structural 0 operand can. The `1e-15` `axisInfinity` snap is replaced by keeping the finite companion part as its own interval.

**Test.** `ln(0)`, `ln(-0)`, `exp(ln 0)` and `exp(-ln 0)` match `complex.ts` point values through the exact layer. `exp(1e20)` (past maxE) and `exp(-1e20)` must give overflow, never 0 or a certified ∞. A ball at the π cap, such as `sin(1e600)` at p = 480, must give undecided and must not crash.

## 7. Q7: the rectangle (decided; agreed)

**Rule.** Use the rectangle `{re, im, rr, ir}` throughout. A disk-shaped bound ("every point is within e") becomes rr = ir = e. Lipschitz bounds use ρ = rr + ir as the half-diagonal bound. Don't inflate twice: `cexp`'s output is already rr = ir = M↑·(E(ρ) + 8u). It needs no further half-diagonal step.

**Why.** Each part's interval is what the digit, sign and per-component decisions test. The rectangle keeps them separate, and costs a factor of at most √2 against a disk.

**Test.** For cexp and cln, assert that per-part containment holds on the corner samples (the §10 harness samples corners on purpose).

## 8. Q8: per-component claims (not blocking; recommendation)

Allowed, if the ball isn't `cut` or `overflow`. Each part's interval encloses that part, so certifying one part's digits or sign is sound even when the other part contains 0. The other part is printed as "0 to N digits" or undecided, **never as exact 0**. That's the #33 failure: `0.5i` printed with a real 10^(−130) dropped. A cut or overflow refuses both parts.

**Test.** `((1+10^(-130))-1)+i/2` prints 0.5i only next to a real part labelled "0 to N digits" or undecided, never exact 0.

## 9. Summary of blocking status

| PR Q | Topic | Blocks | Status |
|---|---|---|---|
| 1 | cexp radius (B3) | yes | answered in §2 |
| 2 | closed ray (B4) | yes | answered in §3: touching is a cut, and no ball avoids it |
| 3 | directed rounding (B6) | yes | answered in §0 and §1 |
| 4 | series remainders (B1/B2) | yes | answered in §5 |
| 5 | exact zero | yes | confirmed in §4 |
| 6 | infinities | yes | answered in §6 |
| 7 | rectangle | yes | decided (§7) |
| 8 | per component | no | allowed (§8) |

## 10. Checks run

All under `/workspace/eml-hub/speedups/ball-checks/`. Logs are next to the scripts.

- **`proto.mjs` → `proto.log`.** This is the §1–§3 rules on decimal.js 10.6.0 at p = 300 and q = 20, against mpmath at 700 digits on the calculator's log bank (`ref.py`). It took 2 min 19 s and finished with **ALL CONTAINED**:
  - **cexp, B3 point set** (same seed as `tests/review-B/b3-cexp.ts`): 0 of 3010 miss, worst 0.11×. The seed missed 654.
  - **cexp, random rectangles** (radii 10^-310 to 10^-1, plus B3.3 balls): 0 of 405 miss.
  - **cln, B6 point set:** 0 of 2004 miss, worst 0.25×. The seed missed 814.
  - **cln, random rectangles** (including near |z| = 1 and near the ray): 0 of 605 miss, with 3 refused. The five edge cases come out as in §3.
  - **e^ρ − 1 ≤ ρ(1 + ρ)** holds on samples from 1e-320 to 1.
  - **`cos` absolute error** for arguments 1e6 to 1e600 is ≤ 4.7e-301, against u = 1e-299.
- **`series_tails.py` → `series_tails.log`.** All 28 rows of (function × N) on complex circles are within the bound, at 250 digits. The arctan example at 0.9i shows the next-term rule failing.

Both are throwaway checks. They aren't a proof that the TypeScript port is right: the §1–§6 tests have to go into CI with the switch PR.

## 11. Exact layer: R1/R2 sign-off

This section answers reviewbot's re-review of `c61059e` (`/workspace/eml-hub/reviewbot-pr40.md`, R1, R2 and R4). I checked it against `main` `d6be0d1`: `complex.ts` `clog`/`logArg`, `exact.ts` `expZ`/`lnEml` (lines 97-135), `enclose.ts:85`, and `library.ts` `rememberDirection`/`tPow` (500-535 and 627-647, hotfix #32). Below, *gate log* means the ln inside `eml`, on the lower bank, and *screen log* means the composed log L(z) = e − ln(exp(e − ln z)).

### Cut convention (checked)

| Point | Gate log (lower bank) | Screen log | Code |
|---|---|---|---|
| −1 | **−iπ** | +iπ | `complex.ts:136-137` (`logArg(z, −π)`), `exact.ts:125` (`onCut → negPi`), `enclose.ts:85` |
| −∞ (imag part exactly 0) | **+∞ − iπ** | not a rule today | `complex.ts:102-108` (`onNegativeCut` includes −∞ "so the lower bank gives it −π"), `exact.ts:133-134` |
| +0 | −∞ + 0i | n/a | `logArg`, `lnEml:121` |
| −0 | −∞ − iπ | n/a | `logArg` (re = −0), `lnEml:120` |

So Arg(−1) = **−π** at the gate, and ln(−∞) = +∞ − iπ uses the same −π. They agree, so the two rules can't pick different banks. The screen's +iπ for ln(−1) is the composed log, rule 8's second clause, and it matches reviewbot's trace and today's `3.14159265359i`. Every table below uses the gate log.

### R1: the domain D = Q(i) + Q(i)·π, plus exact real ±∞ and +0. **Signed off, with three corrections.**

- **Equality: yes.** For a, b ∈ Q(i), a + bπ = 0 ⟺ a = b = 0. Split into real and imaginary parts: each part gives r + sπ = 0 with r, s ∈ Q. That only needs π to be **irrational** (Lambert). Transcendence isn't needed for this step. Equality and sign are then exact rational arithmetic on four rationals per point, plus the sign of r + sπ, which is decided by a rigorous π enclosure once (r, s) ≠ (0, 0).
- **Excluding e and log terms: yes.** Whether 1, π and e are linearly independent over Q is open (π + e is not known to be irrational). So a domain containing e has undecidable structural equality. **Correction:** the exact layer also can't cancel e − e *by value*. The `c61059e` i and π traces do exactly that ("rule 3 has made the real part the same exact real as `exp(1)`, so rule 9 cancels the real part"). That cancellation is sound only as a node identity, x − x = 0 for the same hash-consed finite node, not as D-arithmetic. Either the doc adds that as a named shape rule, or the K57/K93 traces don't close. This is reviewbot's R3 point, now with the reason why.
- **Closure.** The table must list only these rows. Anything not listed gives a ball (sound, though it may stay undecided):

| Op on exact points | In the table | Value |
|---|---|---|
| x ± y, with x, y ∈ D | yes (closed) | componentwise in Q(i)² |
| q·x and x/q, with q ∈ Q(i) \ {0} | yes (closed) | only for builder-level mul/div. A pure circuit has only `eml` |
| x·y with both π-parts nonzero | **no** | π² ∉ D |
| exp(k·iπ/2), k ∈ Z | yes | k mod 4: 0 → 1, 1 → i, 2 → −1, 3 → −i. These are exact table values, not computed `cos`/`sin`, so no −0 and no π/2 dust |
| exp(+∞) and exp(−∞), with an exactly-real ∞ | yes | +∞ and +0 (R2) |
| exp of anything else in D | **no** | |
| gate log of 1, −1, i, −i | yes | 0, **−iπ**, iπ/2, −iπ/2 |
| gate log of +0 and +∞ | yes | −∞ and +∞ (R2) |
| gate log of anything else | **no** | |

- **Correction to "leave the domain".** "Not in the table" is the sound phrasing. Soundness never needs a proof that a value is outside D, only that every table entry is right. Where exclusion is provable, it's for these reasons:
  - **exp(qiπ), q ∈ Q:** this is a root of unity, so it's algebraic. It can be in D only if its π-part is 0, which leaves Q(i), whose only roots of unity are ±1 and ±i. So q ∈ ½Z.
  - **exp(a), a ∈ Q(i) \ {0}:** transcendental (Lindemann). Whether e^a ∈ Q(i) + Q(i)π is **open** (a = 1 is the π + e question). So "other exp arguments leave D" is not a theorem. Not listing them is still the right call.
  - **log α, α ∈ Q(i) \ {0}:** if log α ∈ D, then log α and iπ = log(−1) would be linearly dependent over the algebraic numbers together with 1. Baker's theorem then makes them Q-dependent, so α^m = ±1 and α is a root of unity, one of ±1 and ±i. So "log of any other rational leaves D" **is** a theorem (Baker).
  - **log π, log(a + bπ) with b ≠ 0:** unknown, and not in the table.
- **The −1 that the table feeds to the log must have an exact imaginary 0.** Here it does: exp(iπ) = −1 is a table value. A computed `sin(π)` from decimal.js is ±dust or −0, and would land on the wrong bank or the cut. The table must never call `cos`/`sin`.

### R2: infinities. **Signed off, with two corrections.**

- **Agreed:**
  - An infinity is an exact point only beside a **proved exactly-real** partner. "Proved" means a realness rule (the `one` token, and exp or gate log of a proved-real argument on its continuous side), never a ball and never a side-table sign mark (#35).
  - ln(+∞) = +∞ and ln(+0) = −∞. Both match `lnEml` (+0 gives im +0, so −∞ + 0i).
  - exp(+∞) = +∞ and exp(−∞) = +0.
  - ∞ − ∞ gives a ball/undecided.
  - ∞ beside a non-real or undecided partner gives per-part (re ±∞, im ball) or a refusal, never a real ±∞ or ±∞i.
  - The eml b-cases:
    - b = +0 gives e^a − (−∞) = +∞;
    - b = +∞ gives −∞;
    - b = −∞ doesn't fire as a real infinity (below).

  The partner itself doesn't need to be in D. In `eml(1, 0)`, the partner is e, which is a proved-real finite ball, and the result is the exact real +∞. Only the infinity is the exact point.
- **ln(−∞), corrected.** The gate value is ln(−∞) = **+∞ − iπ**, with the same −π as ln(−1) (`complex.ts:102-108`, `exact.ts:125,133`). That has an imaginary partner of −π, which isn't real. So under the stated domain it is **not in the table**. It can be carried as a per-part value at most (re = +∞ exact, im = −π exact), and it never becomes a real infinity. Then eml(a, −∞) = −∞ + i(π + Im e^a), also per-part at most, which is reviewbot's "−∞ → doesn't fire". If the doc lists it anyway, the row has to say −iπ, not +iπ.
- **Signed zero.** Every rule-produced zero is **+0**: exp(−∞) gives +0 (cos 0 = 1, sin 0 = +0, exactly), and 0 − 0 gives +0. ln 0 fires only on +0. No rule produces −0, so the lnEml branch "re = −0 → −∞ − iπ" is unreachable from the exact layer and can't silently switch banks. This is stricter than `exact.ts` today: `expZ` returns `signedZeroFrom(cos/sin)` for exp(−∞ + iθ), and `:237`, `:263` and `:465` clear to −0. The golden harness should list any row whose text today depends on a −0.
- **Correction: hotfix #32 does not agree with "exp of a non-real infinity is out of the domain" as stated.** On `main`, a directed infinity is *built* as `E(E(+∞, turn), 1)` = exp(+∞ − gate-log(turn)) (`library.ts:519-523`), with turn ∈ {1, −i, −1, i}:
  - for turn = −1, that is exp(+∞ + iπ) = −∞, using gate log(−1) = −iπ;
  - for turn = −i, it is exp(+∞ + iπ/2) = +∞i;
  - for turn = i, it is exp(+∞ − iπ/2) = −∞i.

  These quarter turns are consistent with the −π bank above. But they *are* exp of a non-real infinity, and check.ts locks them as certified: `(inf*i)^3` → `−∞i`, `(inf*i)^5` → `∞i`, `inf*(inf*i)` → `∞i`, `(-inf)^3` → `−∞`. `(inf*i)^-1` → `0` and `(inf*i)^0.5` → unverified are locked the same way. So the doc has to pick one of these, explicitly:
  - **(a)** Add four directed-infinity points ∞·i^k (k mod 4) to the exact layer. The only producing rule is exp(+∞ + i·(kπ/2)), where +∞ is an exact real and kπ/2 is an exact table imaginary part, k ∈ Z. The per-part reading is (±∞, 0) or (0, ±∞), with the 0 exact. exp(+∞ + iθ) for any other θ is undecided, and exp(−∞ + iθ) = +0 for every finite exact θ. The negative-power-is-0 rule then gives +0.
  - **(b)** Keep R2 strict, and list every #32 row in check.ts as moving from certified to unverified, which is a regression that Ben/Jimmy1 would have to accept.

  I recommend **(a)**. It is closed, the quarter-turn values follow from the same table exp(k·iπ/2), and it matches #32. Today's `axisInfinity` 1e-15 snap does the same job unsoundly. Under (a), the zero beside the infinity is exact by construction, not snapped.

**Tests.**
- **Exact-layer values:** `ln(−1)` at the gate gives exactly −iπ, and the screen shows `3.14159265359i`.
- **Directed infinities:** the #32 rows above keep their current text (option a). `(inf*i)^0.5` stays unverified.
- **No real infinity from these:** `ln(ln(0)*i)`, `ln(0)-1`, `ln(0)+i` and `exp(ln(ln(0))*i)` never print a real ±∞ or ±∞i from a non-real partner.
- **ln(−∞):** no row produces a real ∞ from it.
- **Provenance:** every exact point carries its table-row id on the wire, and the worker re-checks it (`WIRE_VERSION` bump).
