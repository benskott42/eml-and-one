# Minimality of 0, −1, and 2

0 at K 7, −1 at K 15, and 2 at K 19 are proved minimal. The proof is computer-assisted. It is unconditional: every tower is included, and it does not use Schanuel's conjecture. The setting is the lower cut, Arg in [−π, π), with ln 0 = −∞. On this cut −iπ becomes +iπ under the principal Log. +iπ is proved minimal at K 21, and at K 23 without ln 0 (below). Every other record in this project is shortest known.

A program is an RPN word on the alphabet {1, E}. A word with n leaves has length K = 2n − 1, so only odd lengths occur. "K ≤ n" means every odd length up to n. Each program was generated directly and decided on its own. Programs were not grouped by value, so it does not matter whether two forms are the same.

The number of programs is the Catalan sequence 1, 1, 2, 5, 14, 42, 132, 429, 1430 at K = 1, 3, 5, 7, 9, 11, 13, 15, 17. That is 4 programs at K ≤ 5, 197 at K ≤ 13, and 2056 at K ≤ 17.

Each program was excluded in one of four ways:

- an Arb ball around the value misses the target
- the imaginary part is certified nonzero
- the value is infinite, or an invalid ∞ − ∞
- a tower is peeled by monotonicity: one real exponential or logarithm is split off, and the target is pulled back into what remains

The certificate was produced with separate verification scripts, which aren't included. One reduces the word by exact identities and then encloses the result. The other evaluates the RPN directly, tracks the imaginary part as an exact multiple of π, and replaces an exponential that overflows with a level and a mean-value bound. Four programs at K 17 that the second script left open were proved by hand. In the ranges below, every program is decided, and none of the exclusions is only numerical.

- **0 at K 7.** All 4 programs with K ≤ 5 are excluded. The word `111E1EE` is 0 with or without ln 0.
- **−1 at K 15, using ln 0.** All 197 programs with K ≤ 13 are excluded. The K 15 word uses ln 0. Without ln 0, −1 is proved minimal at K 17: the only shorter −1 is that K 15 word.
- **2 at K 19.** All 2056 programs with K ≤ 17 are decided, and none of them is 2. The word does not use ln 0.

The same exclusions hold when infinities keep a direction. The two infinity models agree on all 2056 programs with K ≤ 17.

## Reproducing the proof

The verification scripts above are not in this repository. [tools/minimality/decide.py](../tools/minimality/decide.py) is an independent check that is: interval arithmetic (mpmath) with exact k·π tags, symbolic cancellation, and signed tower offsets. Run `python tools/minimality/decide.py` and it reports each claim as PROVED or lists the programs it could not decide. On 2026-11-22 every claim above came out PROVED with nothing undecided: 0 at K 7, −1 at K 15 with ln 0 and at K 17 without it, and 2 at K 19. That includes the four K 17 programs settled by hand above.

## +iπ at K 21, and K 23 without ln 0

`python tools/minimality/decide.py --open` also settles lengths that this document did not claim. **+iπ on this cut (−iπ under the principal log) is minimal at K 21 with ln 0 = −∞**: all 6918 programs with K ≤ 19 are excluded, with nothing undecided. Three of them were tower impostors that differ from +iπ by about 10^(−1656519). The script excludes them because it tracks the sign of the term a tower absorbs, not by numerical comparison, which no precision short of a million digits could do.

**Without ln 0, +iπ is minimal at K 23.** Of the 58786 K 21 programs, the only two that are not excluded take ln 0, and both are +iπ. The first pass of decide.py left 16 K 21 programs undecided. [tools/minimality/towers.py](../tools/minimality/towers.py) decides all 16 (2026-11-24); none is +iπ.

## −2 at K 25

Of the 82500 programs with K ≤ 23, the first pass of decide.py left 188 undecided, all of them towers. towers.py decides 187 of them, and none is −2. The last one, `11E1E1111E1E1EEEE1E1E1E`, is exp(exp(W)) with W = T4/z, where T4 = exp(exp(exp(e))) ≈ 10^1656520 and z = e − ln(e − T2) = e − ln(T2 − e) + iπ. Re W > 10^1656000, so its modulus exp(e^(Re W) cos θ), with θ = Im W mod 2π, is 2 only if |cos θ| < 10^(−1000). θ depends on every digit of T4. [tools/minimality/deep.py](../tools/minimality/deep.py) encloses θ with interval arithmetic at 5.5 million bits, which takes hours, so `--open` reports this program as undecided unless it is run with `--deep`. Until that run certifies |cos θ| > 10^(−6), −2 at K 25 is shortest known, not proved minimal.

Without ln 0, −2 is shortest known at K 27. 18 K 25 programs without ln 0 remain undecided. One of them, `111E1E1111E1E1EEEE1E1E1EE` = e − ln(exp(exp(W))), turns on the same θ (its real part is e − e^(Re W) cos θ), and deep.py decides it with the same run. towers.py leaves the other 17 undecided: each has a tower whose phase it cannot reduce.

## How towers.py decides a tower program

decide.py follows towers only in a few fixed shapes. The programs it left open nest a tower such as T5 = exp(exp(exp(exp(e)))) inside logs, sums and further exponentials, so the value carries a phase within 10^(−1656519) of a multiple of π, or is the difference of two towers. towers.py evaluates each program in two layers:

- **An exact layer.** A value is an integer combination of atoms: 1, iπ, exp(w), ln(z), and ln(1 + u). Equal atoms cancel exactly. The rewrites are exp(ln z) = z, exp(w + kπi) = (−1)^k exp(w), and ln(±exp w) = w, with the multiple of 2πi fixed by the lower cut. When one term t of a sum v is larger than the rest r (|r/t| < 1/e, certified), ln v is split as ln t + ln(1 + r/t), and the 2πi correction comes from the sign of Im(r/t), which the exact layer computes term by term. So ln(e − T5) is exactly T4 − iπ plus a tiny real atom, not an interval.
- **A rigorous enclosure for each atom**: an interval rectangle, or ±exp(W) with W itself an enclosure. ±exp(W) is a tower, huge or tiny, that keeps its phase, and it is never 0. A sum absorbs a term e^50 times smaller into W with a proven bound, and two comparable exponentials exp(w1) ± exp(w2) are combined through w2 − w1 from the exact layer, so a shared tower cancels.
- When a branch is not known, because ln(exp w) depends on Im w mod 2π with Im w a tower, or the sign of a phase below e^(−10^15) is lost, the real part is still exact. The unknown −2πin becomes an atom of its own, purely imaginary, with a range for n.

A program is excluded when value − target is a nonempty combination whose enclosure is ±exp(W), or a rectangle, or an imaginary part summed atom by atom, that misses 0. On each of the 6918 programs with K ≤ 19 and each of the targets 0, −1, 2, −2 and +iπ, no program that one of towers.py and decide.py finds equal to the target is excluded by the other. towers.py excludes a few more, such as −1 + exp(e − exp(exp(e − 1))), which decide.py leaves open. Each of the 4138 finite values that plain 300-bit evaluation reaches away from the cut lies in towers.py's enclosure.
