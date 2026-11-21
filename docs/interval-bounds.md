# Disk bounds for the sound float mode (mathbot, 2026-11-20 ~11:30 PM ET)

These bounds are for item 3 (sound float mode). A float-key hit only nominates a merge, and exact arithmetic confirms it. A value counts as distinct only when its disk is certified disjoint from every existing class's disk.

## 0. Representation and constants
- Each value is a disk *D(c, r)* = { *z* : |*z* − *c*| ≤ *r* }, where *c* is a pair of IEEE doubles and *r* is a double that is always rounded **up**.
- *u* = 2⁻⁵² (a conservative unit for one correctly rounded + − × ÷ on a component).
- *ε* = the per-call error budget for `Math.exp`, `Math.log`, `Math.log1p`, `Math.expm1`, `Math.cos`, `Math.sin`, `Math.atan2` and `Math.hypot`. JS does not specify accuracy; ECMA-262 calls these "implementation-approximated", so *no ulp figure is guaranteed*. V8 and SpiderMonkey use fdlibm-derived code, which is under 1 ulp in practice, but that is an observation, not a guarantee.
  - **Recommendation: set ε = 2⁻⁴⁰ (relative), about 4096 ulp, not 4 ulp.** It costs essentially nothing, because distinct values that aren't near-collisions are separated by far more than 10⁻¹². It also survives a bad libm. Add a startup self-test against ~200 correctly rounded reference values (from mpmath) that asserts every error is ≤ 2⁻⁴⁸. If the test fails, disable certification, so every candidate goes to exact. Soundness then rests on a measured margin of 256×, not on the spec.
- **Rounding the radius up:** after each radius formula, set *r* ← fl(*r*)·(1 + 8*u*) + 2⁻¹⁰²⁰. The tiny absolute term covers underflow in the radius arithmetic itself.
- **Inconclusive:** any NaN or ±∞ in *c* or *r*, any subnormal component, any |*c*| component > 2⁶⁰, or *r* > 2⁻¹⁰·max(1, |*c*|). An inconclusive value is never certified distinct and goes to exact. A subnormal component is inconclusive because `Math.hypot`'s relative error is not bounded by *ε* below 2⁻¹⁰²². Equal components stay too narrow down to 2⁻¹⁰⁴⁶: `hypot` of the smallest positive double with itself has relative error about 0.29, so a log radius near 10⁻⁹ does not cover the true error ln √2.

## 1. exp
For input *D(c, r)* with *c* = *x* + *iy*:
- **Guards (otherwise inconclusive):** *x* < 700; *x* > −700, since below that the result is subnormal or 0 and relative bounds break; |*y*| < 2²⁰, so argument reduction for cos/sin stays in the well-tested range.
- **Midpoint:** *X* = `exp(x)`, *C* = `cos(y)`, *S* = `sin(y)`, *m* = (*X·C*, *X·S*).
- **Error of the midpoint:** |exp(*c*) − *m*| ≤ *e*^*x*·(ε + 2ε + 4*u*) ≤ *X*(1+ε)·(3ε + 4*u*). This assumes |cos − *C*|, |sin − *S*| ≤ ε absolute and |*X* − *e*^*x*| ≤ ε*e*^*x*.
- **Propagation of the input radius (exact identity):** |exp(*c*+δ) − exp(*c*)| = |exp(*c*)|·|*e*^δ − 1| ≤ *e*^*x*·(*e*^*r* − 1).
- **Output radius:**
  *r*′ = *X*(1+ε) · [ `expm1(r)`·(1+ε) + 3ε + 4*u* ], then round up as in §0.
  (*e*^*r* − 1 ≤ *r* e^*r* is fine too, but `expm1` is tighter.)

## 2. Log (principal or lower cut)
For input *D(c, r)*, ρ = |*c*|:
- **Branch-cut guard (this is the key condition):** the disk must not meet the closed ray (−∞, 0]. Distance from *c* to that ray:
  dist = |Im *c*| if Re *c* < 0, else ρ.
  Require dist·(1 − 4ε) > *r*; otherwise the value is **inconclusive**. Inside such a disk, Log is analytic and both cuts agree.
  - This automatically rejects disks containing 0 and disks that touch or cross the negative real axis. It also removes the IEEE signed-zero problem (atan2(±0, *x* < 0) = ±π), because Im *c* is never 0 when Re *c* < 0.
  - **Consequence:** values exactly on the negative axis (−1, −2, …) **always escalate** in the float path. See §5 for the optional fast path.
- **Propagation (one complex bound, tighter than splitting modulus and argument):** with *w* = δ/*c*, |*w*| ≤ *t* = *r*/ρ < 1,
  |Log(*c*+δ) − Log(*c*)| = |log(1 + *w*)| ≤ −log(1 − *t*) = −`log1p(−t)`.
  This holds because the disk avoids the cut, so Log(*c*+δ) = Log *c* + log(1+*w*) with the principal log1p, and there is no 2π*i* jump.
  - Your split is valid but looser: *r*/(ρ−*r*) = *t*/(1−*t*) ≥ −log(1−*t*) on the modulus part, plus asin(*t*) on the argument part, combined. The single disk bound replaces both.
  - Use *t* = *r*/ρ rounded up, with ρ rounded down: ρ↓ = `hypot(x,y)`·(1 − 2ε).
  - A subnormal hypot, or a hypot that flushes a nonzero input to 0, is inconclusive. The *ε* model does not apply there.
- **Midpoint:** *L* = (`log(hypot(x, y))`, `atan2(y, x)`).
  - Error on Re: ≤ ε (from the hypot relative error, since |ln(1+ε)| ≤ ε·(1+ε)) + ε·|ln ρ| + *u*·|*L*_re|.
  - Error on Im: ≤ ε·π + *u*·π.
  - Near ρ ≈ 1, ln ρ is small and absolute error is what matters, so this absolute form is the right one.
- **Output radius:**
  *r*′ = −`log1p(−t)`·(1+ε) + ε(1 + |ln ρ|) + επ + 2*u*(|*L*_re| + π), then round up. If *t* ≥ 0.5, call it inconclusive rather than trusting log1p near −1.

## 3. eml(a, b) = exp(a) − Log(b)
- Midpoint: *m* = *m*_exp − *m*_log, componentwise.
- Radius: *r* = *r*_exp + *r*_log + *u*·(|*m*_exp| + |*m*_log|)·√2, then round up.
- With the per-class memo (item 1), exp(*a*) and Log(*b*) are each computed once per class, together with their radii. The pair cost is then one subtraction plus a radius addition.
- Specials (Log 0 = −∞, exp(−∞) = 0, overflow) never enter this path; dead-slot masks or the exact engine handle them.

## 4. Certifying "distinct"
- **Disk test, without hypot:** *D*₁ and *D*₂ are disjoint if |Δre| > *R* or |Δim| > *R*, where *R* = (*r*₁ + *r*₂)(1 + 4*u*) and Δ = *c*₁ − *c*₂ computed in floats. Comparing against *R*(1 + 4*u*) + 4*u*·max|*c*| covers the rounding of Δ. A max-norm test is sufficient (slightly weaker) and avoids another libm call.
- **Critical:** a float-key **miss is not a proof.** A new value must be certified disjoint from **every** existing disk that could overlap it, and those can sit in neighbouring key buckets. Two fixes are sound:
  - (a) Bin each component on a grid whose cell width *W* is at least 2× the largest radius allowed (relative grids per binary exponent work). Then check the value's own cell and the 8 neighbours (3×3). Any radius over *W*/2 is inconclusive.
  - (b) Keep the 10-digit key as the index, but compute the keys of *c* ± *r* per component and look up every key in that range (usually 1, at most 4).

  Either way, a new value is certified distinct only if every disk found is disjoint. Otherwise it goes to exact.
- **When exact says the forms differ:** different canonical forms prove the values differ only when balls separate them (emlcore's semantics). Keeping them as separate classes is still *safe* for search: it can over-count, but it never drops a value. Label any count produced that way an upper bound.

## 5. Optional fast path for values on the axis
If the exact side has proven a class to be a real negative number (emlcore's provable-realness flag), then Log on the disk is ln|*z*| ± *i*π by the cut. The bound is radius −log1p(−*t*) on the real part, with the imaginary part exactly ±π (π as a double, error ≤ *u*π). Without this, every Log of −1, −2, … escalates, and those values are common in EML.

## 6. Checks to ship with the PR
- A self-test at startup, as in §0.
- A randomized property test: for 10⁵ random (*a*, *b*) pairs from the pool, evaluate with decimal.js at 50 digits and assert the true value lies inside the disk. Include points within 10⁻⁸ of the negative real axis, |*y*| near 2²⁰, and *x* near ±700.
- A measurement of the escalation rate per level, since that sets the real speedup.
