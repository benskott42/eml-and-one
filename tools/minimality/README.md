# Minimality checker

`decide.py` re-derives the claims in [docs/minimality.md](../../docs/minimality.md) from scratch, with mpmath interval arithmetic on the lower cut and ln 0 = −∞:

```bash
python decide.py         # 0 at K 7, −1 at K 15 (with ln 0) and K 17 (without), 2 at K 19
python decide.py --open         # +iπ at K 21 (K 23 without ln 0), −2 at K 25 (K 27 without ln 0)
python decide.py --open --deep  # the same, and deep.py's phases for the programs left open (about 80 minutes on 16 cores)
python decide.py --word WORD --upto K [--strict] [--expect NAME] [--witness WORD]
python deep.py [word ...]       # towers.py with deep.py's phases for these words (default: the K 23 and K 25 programs on T4/z)
```

A program is excluded only when it certainly differs from the target. Its value may be ±∞, an invalid ∞ − ∞, or a tower far outside float range, or the target may lie outside the interval rectangle that encloses the value. Three devices keep that decisive:

- exact tags for an imaginary part that is k·π, so the branch cut is decided symbolically;
- a symbolic form per value: an integer combination of `exp(…)`, `ln(…)`, `1` and `iπ` atoms, with ln 1 = 0, ln(exp x) = x for real x, and exp(ln z) = z. When both sides of a subtraction have the same form, the result is an exact 0, not an interval around 0;
- towers kept as ±exp(L), with exp(L) − c rewritten as exp(L + δ). The sign of δ is tracked, so a cancellation that leaves δ is known to be nonzero.

Anything else is reported as undecided, never assumed. On 2026-11-22 every claim in docs/minimality.md came out PROVED. That includes the four K 17 programs that the original certificate settled by hand.

`--word` takes the target as an EML word. The word is evaluated in the same `reset()` scope as the program, so a tower shared with the target cancels in the exact layer. The witness has to match a named constant (ln 2, −e, 1/e, e + 1, e², 2, +iπ, or −2) in that exact layer, not merely equal itself. `--expect` names which of those constants it has to be (`ln2`, `-e`, `1/e`, `e+1`, `e^2`, `2`, `ipi`, `-2`); a word for a different constant fails before the scan. `--strict` is the claim without ln 0: a program that takes ln of an exact 0 may still hit the target. A value ±exp(e^W) whose only gap is θ = Im W mod 2π gets that phase from deep.py (arb.exp). It is excluded only when an arb enclosure of cos θ is strictly signed: positive excludes a modest target, negative excludes a nonzero target. A program the first pass leaves undecided goes to `towers.py`. It keeps a value as an exact integer combination of atoms (1, iπ, exp(w), ln(z), and ln(1 + u) for a sum split at a dominant term), so a shared tower cancels exactly, and encloses each atom either as an interval rectangle or as ±exp(W) with W itself an enclosure: a tower, huge or tiny, that keeps its phase. ±exp(W) is never 0. Where the branch of ln(exp w) depends on Im w mod 2π and Im w is too large to reduce, the real part is still exact and the unknown −2πin is kept as a purely imaginary atom. A tower can also carry its phase apart from W, and a tower value its exact imaginary part, summed atom by atom; ln(exp w) with Im w a tower keeps Re w exactly beside a purely imaginary unknown, and a program is also excluded when its real part alone misses the target.

`deep.py` is the phase oracle for the programs whose real part or modulus depends on a phase towers.py cannot reduce, such as Im(T4/z) mod 2π. towers.py hands it the subword whose value is the tower's exponent; deep.py evaluates it with interval arithmetic at log2|Im| + 512 bits (up to 5.5 million), with exp(x − ln y) = exp(x)/y so T4 is shared, and returns the phase as a 128-bit interval. `--deep` runs every program the claims need in parallel worker processes that share T2, T3 and T4 through files. It excludes 16 of the 18 K 25 programs without ln 0 that towers.py alone leaves open; the last two need the phase of a tower of towers and stay undecided (see docs/minimality.md).
