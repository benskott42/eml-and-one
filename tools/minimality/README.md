# Minimality checker

`decide.py` re-derives the claims in [docs/minimality.md](../../docs/minimality.md) from scratch, with mpmath interval arithmetic on the lower cut and ln 0 = −∞:

```bash
python decide.py         # 0 at K 7, −1 at K 15 (with ln 0) and K 17 (without), 2 at K 19
python decide.py --open         # +iπ at K 21 (K 23 without ln 0), −2 at K 25 (K 27 without ln 0)
python decide.py --open --deep  # the same, and runs deep.py for the two programs that need it
python deep.py                  # those two alone: 5.5 million bits, about 90 minutes
```

A program is excluded only when it certainly differs from the target. Its value may be ±∞, an invalid ∞ − ∞, or a tower far outside float range, or the target may lie outside the interval rectangle that encloses the value. Three devices keep that decisive:

- exact tags for an imaginary part that is k·π, so the branch cut is decided symbolically;
- a symbolic form per value: an integer combination of `exp(…)`, `ln(…)`, `1` and `iπ` atoms, with ln 1 = 0, ln(exp x) = x for real x, and exp(ln z) = z. When both sides of a subtraction have the same form, the result is an exact 0, not an interval around 0;
- towers kept as ±exp(L), with exp(L) − c rewritten as exp(L + δ). The sign of δ is tracked, so a cancellation that leaves δ is known to be nonzero.

Anything else is reported as undecided, never assumed. On 2026-11-22 every claim in docs/minimality.md came out PROVED. That includes the four K 17 programs that the original certificate settled by hand.

A program the first pass leaves undecided goes to `towers.py`. It keeps a value as an exact integer combination of atoms (1, iπ, exp(w), ln(z), and ln(1 + u) for a sum split at a dominant term), so a shared tower cancels exactly, and encloses each atom either as an interval rectangle or as ±exp(W) with W itself an enclosure: a tower, huge or tiny, that keeps its phase. ±exp(W) is never 0. Where the branch of ln(exp w) depends on Im w mod 2π and Im w is too large to reduce, the real part is still exact and the unknown −2πin is kept as a purely imaginary atom. `deep.py` covers the two programs whose real part or modulus itself depends on such a phase (see docs/minimality.md).
