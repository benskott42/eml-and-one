# rotSub

`rotSub` equals a − b for a, b in ℂ with b ≠ 0, given ln 0 = −∞ and the extended model where infinities carry no phase, so exp(+∞ + iθ) = +∞, for any logarithm that inverts the exponential. b = 0 needs a directed infinity: under the phase-free model, sub(5, 0) and add(5, 0) are NaN. The argument below is from an internal review, and it uses the unwinding number of Corless and Jeffrey, “The unwinding number”, ACM SIGSAM Bulletin 30(2):28–35, 1996, [doi:10.1145/235699.235705](https://doi.org/10.1145/235699.235705). The rotation — multiplying the unwinding term by an imaginary constant so that it becomes real — is this calculator's construction. It is not in that paper as far as we know.

The code uses the lower bank: on a negative real the argument is −π. The cut is the negative real axis. [−π, π) is the range of Im ln, not the cut. The same identity holds for the principal branch, whose argument is +π on that ray and whose imaginary part lies in (−π, π]. Both are instances of one lemma.

## Words

RPN, with `E` popping y then x:

| word | K | meaning |
| --- | --- | --- |
| `x1E` | 3 | exp x |
| `11xE1EE` | 7 | ln |
| `11xE1EEy1EE` | 11 | raw sub, `x − λ(e^y)` |
| `1111xEE1EEyE1EE1E` | 17 | mul |
| `111yEE1EE1xE1EE1E` | 17 | div |
| `111111E1EEEE11E1E1EEE` | 21 | c = +iπ on the lower bank, −iπ on the principal bank |

`rotSub(a, b) = div( raw( mul(c, raw(a, b)), mul(c, raw(b, b)) ), c )`. In `lib/eml/lowering.ts` a minuend that is already an exponential uses eml(H, exp b) instead of eml(ln(exp H), exp b). Those agree on every branch, and the ln is eight tokens. With c the K 21 word the circuit is K 131 and 34 distinct eml nodes, or K 71 and 26 nodes if c is a leaf. The inner subtraction is that shortened word, not another rotSub.

## Statement

Let λ be any logarithm, so e^λ(y) = y, λ depends only on y, and λ(r) = ln r for r > 0. Principal Log and the lower bank are both such functions. Assume, for finite u:

1. λ(0) = −∞
2. u − (−∞) = +∞
3. e^(+∞) = +∞, λ(+∞) = +∞, and +∞ − u = +∞
4. u − (+∞) = −∞
5. e^(−∞) = 0

Let c be a nonzero imaginary number. Then for all a, b in ℂ, given ln 0 = −∞ and the extended model where exp(+∞ + iθ) = +∞, `rotSub(a, b) = a − b`. The forms ∞ − ∞ and 0 · ∞ do not occur. A model that keeps imaginary parts on infinities gives the same results, because only the real parts of the infinite intermediates are read.

In the directed model, `mul(c, 0)` builds exp(+∞ + iθ) with θ = ±π/2. The exponential of a value whose real part is +∞ is an infinity, never NaN. Both evaluators do that. NaN from a raw exact gate is sticky: Log(NaN) is NaN, and it stays NaN through later gates. `raw` multiplication of 0 · ∞ is that indeterminate form, not 0.

## Unwinding number

λ(e^y) = y − 2πi κ(y). For the principal branch, κ = ceil((Im y − π) / 2π). For the lower bank, κ_L = floor((Im y + π) / 2π). If y is real then κ(y) = 0 for every admissible λ.

The lemmas, for those rules:

- **exp.** eml(x, 1) = e^x, including ±∞.
- **ln.** For x ≠ 0, the K 7 word is a logarithm of x. For x = 0 it is −∞, and e raised to that is 0. So the word inverts the exponential for every x, including 0.
- **raw sub.** s(x, y) = x − y + 2πi κ(y). In particular s(y, y) = 2πi κ(y), and s is exact when y is real.
- **mul.** For x ≠ 0 and any y, the K 17 word is xy. The y = 0 case is the chain +∞, +∞, −∞, and the result 0. The case x = e^e is the same chain followed by an exponential, and it returns the product; it does log 0. Branches enter only through exponentials, so the choice of λ does not matter. x = 0 and y infinite is 0 · ∞, which is NaN, not this case.
- **div.** For y ≠ 0 and any x, the K 17 word is x/y. x = 0 runs through +∞, +∞, −∞, and then 0. For y = e^e the word begins with eml(1, y) = 0, then eml(1, 0) = +∞, then the same ∞, ∞, −∞ chain, and the last exponential recovers x/y. That case logs 0.

## Proof

Let k = κ(b). The two raw calls share one node for e^b, so they share one value of λ(e^b). Then

```
r1 = s(a, b) = a − b + 2πi k
r2 = s(b, b) = 2πi k
```

and the branch cancels. `m1 = c · r1` and `m2 = 2πi · c · k`. m2 is real because c is imaginary. With c = ±iπ, m2 = ∓2π² k. κ of a real number is 0, so

```
t = s(m1, m2) = m1 − m2 = c (a − b)
d(t, c) = a − b
```

Any nonzero imaginary c works exactly. |c| only matters in float. A smaller |c|, such as iπ / e^e (K 199), stays exact out to about |Im b| < 3300.

## Where ln 0 is used

e^b is never 0 for finite b. The dependence on ln 0 is generic. For every b in the open strip, κ(b) = 0, so raw(b, b) = 0, and mul(c, 0) logs 0. rotSub therefore needs ln 0 = −∞ in the ordinary case. It is invalid under the policy that disallows that value, and this construction cannot be repaired to avoid it.

The same logarithm of 0 appears in the other edge cases:

- r1 = 0, that is a = b − 2πi k, so mul(c, 0) and then s(0, m2) through ln 0
- a = b, so t = s(m2, m2) = 0 and div(0, c) logs 0
- a = 0, so s(0, b) logs 0
- b = 0, so r2 = s(0, 0) logs 0 and then mul(c, 0) logs it again
- 0 − 0 uses all of these and the result is 0
- the K 21 word for c logs 0 itself

On the cut, Im b = π (mod 2π), the two conventions differ by one in k. k cancels. Arguments inside ln, mul, and div matter only through e^λ, so they are free of the convention. λ(e^m2) has a positive real argument. An adversarial λ that adds 2πi s(z), with s an integer from −2 to 2 and s = 0 on the positive reals, passes the same points.

## What never happens

The only subtractions with an infinite operand are finite − (−∞), +∞ − 0, and finite − (+∞). eml has no multiplication, so 0 · ∞ cannot occur at an eml gate inside this identity. The mul and div words are exact for the arguments the identity feeds them.

## What the calculator evaluates

Both modes evaluate these gates. The evaluator does not substitute a − b. An earlier exact mode did that, and the substitute agreed with the gates on the cases where the identity applies; it was still a different computation from the pressed program, so it is gone. Pasting the raw program is the value on the screen.

A known subtrahend whose real and imaginary parts lie inside the float strip uses unscaled rotSub, which is K 131. An unknown range, or a value outside that strip, is lowered as k · rotSub(a/k, b/k). The scale is inside the circuit. A sum uses the same k, built from b rather than from −b. A known large real away from the cut is scaled by exp(n) first. Neither path divides by the subtrahend.

The code builds k as 1 + √(b²). The log inside that square root has imaginary part in [−π, π] on this branch, so the root has nonnegative real part, Re k ≥ 1, and k ≠ 0. A different branch of that log can put the real part of the root below −1 and make k zero. This is not a claim about every branch.

Proof of the scaled form. Under that same hypothesis, rotSub(u, v) = u − v for every finite u, v. Whenever the mul and div words equal multiplication and division and k ≠ 0,

```
k · rotSub(a/k, b/k) = k · (a/k − b/k) = a − b.
```

Those words equal the field operations in the mul and div lemmas above, including at k = e^e, where the evaluation logs 0. The trace is the one in the div lemma: eml(1, e^e) = 0, then +∞, and the ∞, ∞, −∞ chain plus a final exponential recovers the quotient. Multiplication by e^e recovers the product the same way. So k = e^e is allowed, and the scaled form is still a − b.

For a positive real, k = 1 + b, so k = e^e at b = e^e − 1. That point goes through ln 0 and still equals a − b. At b = 0 the square is 0 and the square root word is 0, so k = 1. A variable bound to 0 runs this same scaled circuit. It is not replaced by the minuend.

## Zero on the scaled path

These are the branch rules the scaled circuit relies on when a runtime subtrahend is zero. They are properties of exp and ln, not a special case in the subtraction circuit. A variable bound to 0 still runs the scaled gates.

- exp(−∞ ± iπ) = −0. The imaginary part is a signed zero in that direction.
- exp(+∞ ± iπ) = −∞ exactly. Float π is an exact half turn, so the angle is not a few ulps off the axis and the exponential is not NaN.
- ln(−∞) and ln(−0) keep an imaginary part of ±π. On the lower bank inside eml that sign is −π. The composed ln, which is the principal logarithm, has +π.

## Float

Float mode is a hardware view. It shows what these gates do in IEEE float64, and it is not adjusted to match the exact value. Exact mode is the default: it evaluates the same circuit, the screen says computing until that finishes, and Cancel clears that result instead of leaving the previous number up. When the two disagree by more than float can claim, the float stays visible and the screen flags “float differs from exact” with the exact value beside it.

Add and subtract share one lift. Below magnitude 10^(−4) the short gates only have about 10^(−16) of absolute accuracy, so both multiply by the power of ten that brings the magnitude up to about 1, and neither uses a power past 10^307. The other cut-offs are named: the short identity stops at magnitude 20, unscaled rotSub stops at a real part of about 700, and a known large real scales by exp(n) only through exp(800).

With the lower bank, c = +iπ, and m2 = −2π² k for k = floor((Im b + π) / 2π):

- k ≤ −36 (Im b < −71π ≈ −223.05) overflows e^m2
- k from −35 to 35, the strip [−71π, 71π), is exact to a few ulps
- k = 36, [71π, 73π), is barely subnormal, about 10^(−15)
- k = 37, [73π, 75π), underflows and is degraded; the measured error is about 10^(−7). This end underflows. It does not overflow
- k ≥ 38 (Im b ≥ 75π) underflows to 0, and then λ(0) = −∞, which is the wrong value

The measured relative error is at most about 2 · 10^(−15) for −223.05 < Im b < 229.3. The real part also has to satisfy about −745 < Re b < 709, and |a| and |r1| must not fall below about 10^(−307) unless they are exactly 0. The scaled circuit pushes a large subtrahend back into that interval until b² overflows float. That happens around |b| > 1.3×10^154, because a float overflows near 10^308 and the square crosses that line near 10^(308/2). Past the strip, or past that scale, the float result is flagged as out of range. It is not labeled indeterminate unless the form really is ∞ − ∞ or 0 · ∞.
