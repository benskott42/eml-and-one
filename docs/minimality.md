# Minimality of 0, −1, and 2

0 at K 7, −1 at K 15, and 2 at K 19 are proven minimal. The proof is computer-assisted. It is unconditional: every tower is included, and it does not use Schanuel's conjecture. The setting is the lower cut, Arg in [−π, π), with ln 0 = −∞. On this cut −iπ becomes +iπ under the principal Log. Every other record in this project is shortest known.

A program is an RPN word on the alphabet {1, E}. A word with n leaves has length K = 2n − 1, so only odd lengths occur. "K ≤ n" means every odd length up to n. Each program was generated directly and decided on its own. Programs were not grouped by value, so it does not matter whether two forms are the same.

The number of programs is the Catalan sequence 1, 1, 2, 5, 14, 42, 132, 429, 1430 at K = 1, 3, 5, 7, 9, 11, 13, 15, 17. That is 4 programs at K ≤ 5, 197 at K ≤ 13, and 2056 at K ≤ 17.

Each program was excluded in one of four ways:

- an Arb ball around the value misses the target
- the imaginary part is certified nonzero
- the value is infinite, or an invalid ∞ − ∞
- a tower is peeled by monotonicity: one real exponential or logarithm is split off, and the target is pulled back into what remains

The certificate was produced with separate verification scripts, which aren't included. One reduces the word by exact identities and then encloses the result. The other evaluates the RPN directly, tracks the imaginary part as an exact multiple of π, and replaces an exponential that overflows with a level and a mean-value bound. Four programs at K 17 that the second script left open were proved by hand. In the ranges below, every program is decided, and none of the exclusions is only numerical.

- **0 at K 7.** All 4 programs with K ≤ 5 are excluded. The word `111E1EE` is 0 with or without ln 0.
- **−1 at K 15, using ln 0.** All 197 programs with K ≤ 13 are excluded. The K 15 word uses ln 0. Without ln 0, −1 is proven minimal at K 17: the only shorter −1 is that K 15 word.
- **2 at K 19.** All 2056 programs with K ≤ 17 are decided, and none of them is 2. The word does not use ln 0.

The same exclusions hold when infinities keep a direction. The two infinity models agree on all 2056 programs with K ≤ 17.
