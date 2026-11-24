# Minimality of 0, −1, and 2

0 at K 7, −1 at K 15, and 2 at K 19 are proved minimal. The proof is computer-assisted. It is unconditional: every tower is included, and it does not use Schanuel's conjecture. The setting is the lower cut, Arg in [−π, π), with ln 0 = −∞. On this cut −iπ becomes +iπ under the principal Log. +iπ is proved minimal at K 21, and at K 23 without ln 0, and −2 at K 25 with ln 0 (below). Without ln 0, every K 25 program but two is excluded as −2, so −2 at K 27 without ln 0 is shortest known. Every other record in this project is shortest known.

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

Of the 82500 programs with K ≤ 23, the first pass of decide.py left 188 undecided, all of them towers. towers.py decides 187 of them, and none is −2. The last one, `11E1E1111E1E1EEEE1E1E1E`, is exp(exp(W)) with W = T4/z, where T4 = exp(exp(exp(e))) ≈ 10^1656520 and z = e − ln(e − T2) = e − ln(T2 − e) + iπ. Re W > 10^1656000, so its modulus exp(e^(Re W) cos θ), with θ = Im W mod 2π, is 2 only if |cos θ| < 10^(−1000). θ depends on every digit of T4. [tools/minimality/deep.py](../tools/minimality/deep.py) encloses θ with interval arithmetic at 5.5 million bits: exp by Newton's method on mpmath's ln, each enclosure checked with directed-rounding logs, so Im W is known to within 10^(−116). On 2026-11-24 it gave θ = −5.39531064387935195139… and cos θ = 0.63106214288953973449…, in 87 minutes. A plain interval-arithmetic run (mpmath iv.exp, 152 minutes) gave the same enclosure, and so did the general phase oracle below (2026-11-24, the same digits). So this program is not −2, and **−2 is minimal at K 25 with ln 0 = −∞**. `--open` alone reports this program as undecided; `--open --deep` decides it in the same pass.

### Without ln 0: all but two K 25 programs

Of the 208012 K 25 programs, the towers.py of 2026-11-23 left 24 not excluded; 6 of them take ln 0, and 18 are towers without ln 0. Since 2026-11-24, 16 of those 18 are excluded, none is −2, and 2 remain open, so −2 without ln 0 is still only shortest known at K 27. With T5 = exp(T4), T6 = exp(T5), z as above, z2 = e − ln z, and Q the value whose phase matters:

- **Three need no phase.** e − ln(exp(T5/z)) has real part e − Re(T5/z), and Re(T5/z) is a positive tower; exp(T6/z) and T7/z = exp(T6 − ln z) have modulus far from 2. towers.py now keeps the exact imaginary part of a tower such as T6 − ln z (it is −Arg z), and for ln(exp w) with Im w a tower it keeps the exact real part Re w beside a purely imaginary unknown, so these are excluded on their real part or modulus.
- **Nine turn on the phase of exp(Q) with Q = T4/z′,** so on every digit of T4: e − ln(exp(exp(W))) (θ above), exp(exp(W − 1)), exp(exp(W) − 1), exp(exp(W)) − 1, and exp(exp(T4/z′)) for z′ = z2, e − ln(e^(e−1) − e) + iπ, e − ln(T2 − e − 1) + iπ, e − ln(ln(T3 − 1) − e) + iπ, and T2 − ln(T2 − e) + iπ. Each is −2 only if e^(Re Q) cos(Im Q) is ln 2, 1 + ln 2, e + 2 or 0 (or e times ln 2), so only if |cos(Im Q mod 2π)| < 10^(−1000).
- **Four turn on the phase of exp(Q) with Q = exp(T3/z′) or exp(T3/e)/z,** where |Q| is between 10^(120000) and 10^(610000): exp(exp(exp(exp(T2 − ln z′)))) for z′ = z2, e − ln(e^(e−1) − e) + iπ and T2 − ln(T2 − e) + iπ, and exp(exp(exp(T3/e)/z)). These need 0.46 to 2.0 million bits.
- **Two stay open.** exp(exp(exp(W))) and exp(exp(T5/z)) are −2 only if exp(V) = ln 2 + (2k+1)πi for some integer k, with V = exp(W) or T5/z. Re exp(V) = e^(Re V) cos(Im V), and Im V mod 2π is the phase of exp(W) or of T5/z: Im exp(W) = e^(Re W) sin θ is a number with about 10^1656519 digits before the point, and Im(T5/z) has about T4 digits. No enclosure reaches either, so these two are not decided, and −2 without ln 0 at K 27 is not proved minimal.

On 2026-11-24, `python tools/minimality/decide.py --open --deep` took 79 minutes on 16 cores: 9 for the first pass, then 71 for the 16 programs left open, run in parallel. Every phase it found, as Im Q mod 2π:

| Program | Q | Bits | Im Q mod 2π | cos |
|---|---|---|---|---|
| `11E1E1111E1E1EEEE1E1E1E`, `111E1E1111E1E1EEEE1E1E1EE`, and the W − 1, exp(W) − 1, exp(exp(W)) − 1 programs | W = T4/z | 5505024 | −5.39531064387935195139… | 0.63106214288953973449… |
| `11E1E11111E1E1EEEEE1E1E1E` | T4/z2 | 5505024 | 4.36966891183412244724… | −0.33605021259836444642… |
| `11E1E11111EE1E1EEEE1E1E1E` | T4/(e − ln(e^(e−1) − e) + iπ) | 5505024 | −4.05318711084541008586… | −0.61248613989522764165… |
| `11E1E1111E11EE1EEEE1E1E1E` | T4/(e − ln(T2 − 1 − e) + iπ) | 5505024 | −0.73630608175697142980… | 0.74095427927515847694… |
| `11E1E1111E1E11EEEEE1E1E1E` | T4/(e − ln(ln(T3 − 1) − e) + iπ) | 5505024 | −4.08498727538847319626… | −0.58704327776948372476… |
| `11E1E11E111E1E1EEEE1E1E1E` | T4/(T2 − ln(T2 − e) + iπ) | 5505024 | −4.26061385508606062394… | −0.43656325440004063272… |
| `11E11111E1E1EEEEE1E1E1E1E` | exp(T3/z2) | 1835008 | −1.03215521342594717792… | 0.51296998845666208399… |
| `11E11EE1111E1E1EEEE1E1E1E` | exp(T3/e)/z | 2031616 | −3.01681881054677896285… | −0.99222583791345245414… |
| `11E11111EE1E1EEEE1E1E1E1E` | exp(T3/(e − ln(e^(e−1) − e) + iπ)) | 786432 | −0.53084658715667689598… | 0.86237878334081872168… |
| `11E11E111E1E1EEEE1E1E1E1E` | exp(T3/(T2 − ln(T2 − e) + iπ)) | 458752 | 5.39976248839845339597… | 0.63450931751123095246… |

Each phase is known to about 10^(−38) (a 128-bit interval), and every cos is far from 0, so all 14 are excluded. A negative cos makes the value tiny rather than huge, which excludes it as well. A separate run of the four smaller ones, with mpmath's own two-endpoint ln and atan2 in place of the one-evaluation versions, gave the same intervals, and the T4/z phase matches the earlier deep.py runs.

**How deep.py gets a phase.** towers.py keeps exp(Q) as a tower ±exp(W) whose W is an enclosure of Q. When Im W is too wide to reduce mod 2π, towers.py asks deep.py for the phase of the subword whose value is Q. deep.py evaluates that subword with mpmath interval arithmetic at log2|Im Q| + 512 bits, rounded up to a multiple of 65536, using only identities that hold exactly: exp(x − ln y) = exp(x)/y for any branch, so T4/z is computed as exp(T3)/z and T4 is shared; ln(exp x) = x when Im x is in [−π, π); and the principal log on the lower cut, refused when an enclosure touches the cut. Past 50000 bits, exp is Newton's method on mpmath's ln, checked with one directed-rounding log, and each ln or atan takes one directed-rounding evaluation plus the bound ln(b) ≤ ln(a) + (b − a)/a (atan′ ≤ 1). It returns Im Q − 2πn as a 128-bit interval. A subword whose value needs exp of anything past 2^31 is refused, which is what leaves the last two programs open. The programs run in parallel worker processes, which share every result above 50000 bits through files, so T2, T3 and T4 are computed once.

## How towers.py decides a tower program

decide.py follows towers only in a few fixed shapes. The programs it left open nest a tower such as T5 = exp(exp(exp(exp(e)))) inside logs, sums and further exponentials, so the value carries a phase within 10^(−1656519) of a multiple of π, or is the difference of two towers. towers.py evaluates each program in two layers:

- **An exact layer.** A value is an integer combination of atoms: 1, iπ, exp(w), ln(z), and ln(1 + u). Equal atoms cancel exactly. The rewrites are exp(ln z) = z, exp(w + kπi) = (−1)^k exp(w), and ln(±exp w) = w, with the multiple of 2πi fixed by the lower cut. When one term t of a sum v is larger than the rest r (|r/t| < 1/e, certified), ln v is split as ln t + ln(1 + r/t), and the 2πi correction comes from the sign of Im(r/t), which the exact layer computes term by term. So ln(e − T5) is exactly T4 − iπ plus a tiny real atom, not an interval.
- **A rigorous enclosure for each atom**: an interval rectangle, or ±exp(W) with W itself an enclosure. ±exp(W) is a tower, huge or tiny, that keeps its phase, and it is never 0. A sum absorbs a term e^50 times smaller into W with a proven bound, and two comparable exponentials exp(w1) ± exp(w2) are combined through w2 − w1 from the exact layer, so a shared tower cancels.
- When a branch is not known, because ln(exp w) depends on Im w mod 2π with Im w a tower, or the sign of a phase below e^(−10^15) is lost, the real part is still exact. The unknown −2πin becomes an atom of its own, purely imaginary, with a range for n, or with no range when Im w is a tower.
- A tower can carry its phase apart from W, and a tower value its exact imaginary part, both summed atom by atom in the exact layer or, with `--deep`, taken from deep.py.

A program is excluded when value − target is a nonempty combination whose enclosure is ±exp(W), or a rectangle, or an imaginary part summed atom by atom, or a real part without the purely imaginary atoms, that misses 0. On each of the 6918 programs with K ≤ 19 and each of the targets 0, −1, 2, −2 and +iπ, no program that one of towers.py and decide.py finds equal to the target is excluded by the other. towers.py excludes a few more, such as −1 + exp(e − exp(exp(e − 1))), which decide.py leaves open. Each of the 4138 finite values that plain 300-bit evaluation reaches away from the cut lies in towers.py's enclosure.
