# Minimality checker

`decide.py` re-derives the claims in [docs/minimality.md](../../docs/minimality.md) from scratch, with mpmath interval arithmetic on the lower cut and ln 0 = −∞:

```bash
python decide.py         # 0 at K 7, −1 at K 15 (with ln 0) and K 17 (without), 2 at K 19
python decide.py --open  # tries +iπ at K 21 and −2 at K 25 (README: shortest known)
```

A program is excluded only when it certainly differs from the target. Its value may be ±∞, an invalid ∞ − ∞, or a tower far outside float range, or the target may lie outside the interval rectangle that encloses the value. Three devices keep that decisive:

- exact tags for an imaginary part that is k·π, so the branch cut is decided symbolically;
- a symbolic form per value: an integer combination of `exp(…)`, `ln(…)`, `1` and `iπ` atoms, with ln 1 = 0, ln(exp x) = x for real x, and exp(ln z) = z. When both sides of a subtraction have the same form, the result is an exact 0, not an interval around 0;
- towers kept as ±exp(L), with exp(L) − c rewritten as exp(L + δ). The sign of δ is tracked, so a cancellation that leaves δ is known to be nonzero.

Anything else is reported as undecided, never assumed. On 2026-11-22 every claim in docs/minimality.md came out PROVED. That includes the four K 17 programs that the original certificate settled by hand.
