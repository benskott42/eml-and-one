# Minimality of 0, −1, and 2

0 at K 7, −1 at K 15, and 2 at K 19 are proved minimal. The proof is computer-assisted. It is unconditional: every tower is included, and it does not use Schanuel's conjecture. The setting is the lower cut, Arg in [−π, π), with ln 0 = −∞. On this cut −iπ becomes +iπ under the principal Log. +iπ is proved minimal at K 21, and at K 23 without ln 0, and −2 at K 25 with ln 0 (below). Without ln 0, every K 25 program but two is excluded as −2, so −2 at K 27 without ln 0 is shortest known. ln 2 at K 25, −e at K 17 (and at K 23 without ln 0), 1/e at K 17 (and at K 19 without ln 0), e + 1 at K 19 (and at K 21 without ln 0), and e² at K 21 are proved minimal the same way: `decide.py --word` prints PROVED for each, with the target passed as an EML word (below). Every other record in this project is shortest known.

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

**Without ln 0, +iπ is minimal at K 23.** Of the 16796 K 21 programs, the only two that are not excluded take ln 0, and both are +iπ. The first pass of decide.py left 16 K 21 programs undecided. [tools/minimality/towers.py](../tools/minimality/towers.py) decides all 16 (2026-11-24); none is +iπ.

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

**How deep.py gets a phase.** towers.py keeps exp(Q) as a tower ±exp(W) whose W is an enclosure of Q. When Im W is too wide to reduce mod 2π, towers.py asks deep.py for the phase of the subword whose value is Q. deep.py evaluates that subword with mpmath interval arithmetic at log2|Im Q| + 512 bits, rounded up to a multiple of 65536, using only identities that hold exactly: exp(x − ln y) = exp(x)/y for any branch, so T4/z is computed as exp(T3)/z and T4 is shared; ln(exp x) = x when Im x is in [−π, π); and the principal log on the lower cut, refused when an enclosure touches the cut. Past 50000 bits, exp, ln, atan, cos and sin are python-flint arb balls whose endpoints are rounded outward into an mpmath interval. exp, ln and atan are monotone, so each endpoint is evaluated on its own; cos and sin are one ball over the whole interval. It returns Im Q − 2πn as a 128-bit interval. A subword whose value needs exp of anything past 2^31 is refused, which is what leaves the last two programs open. The programs run in parallel worker processes, which share every result above 50000 bits through files, so T2, T3 and T4 are computed once.

## ln 2, −e, 1/e, e + 1, and e²

`python tools/minimality/decide.py --word WORD --upto K` takes the target as an EML word. The word is evaluated in the same `reset()` scope as each program, so a tower shared with the target is one atom and cancels. A program is excluded when its enclosure misses that value, or when value − target is a nonempty exact combination that cannot be 0. `--strict` is the claim without ln 0: a program that takes ln of an exact 0 may still equal the target. When the only gap is θ = Im W mod 2π for a value ±exp(e^W), the same command asks deep.py for θ and excludes the program only when an arb enclosure of cos θ is strictly signed: positive makes the value larger than every finite target here, negative makes it smaller than every nonzero one. On 2026-11-28:

- **ln 2 at K 25.** The word `11111111EEE1EE11EE1EEE1EE` does not use ln 0. `decide.py --word 11111111EEE1EE11EE1EEE1EE --upto 23` excludes all 82500 programs with K ≤ 23 and prints PROVED (368 s). The last word is `11E1E1111E1E1EEEE1E1E1E`, exp(exp(T4/z)). That run computes θ = Im(T4/z) mod 2π at 5505024 bits: θ = −5.39531064387935195139… and cos θ = 0.63106214288953973449… > 0 (69 s). The modulus is exp(e^{Re W} cos θ), and a positive cos makes it larger than 1, so it is not ln 2. ln 2 is minimal at K 25 with or without ln 0.
- **−e at K 17, using ln 0.** All 626 programs with K ≤ 15 are excluded. The word is `11111E1EEEE11E1EE`. **Without ln 0, −e is minimal at K 23.** Of the 23714 programs with K ≤ 21, the 21 that equal −e all take ln 0. The K 23 word `1111E11E1EEE1EE11E1E1EE` does not.
- **1/e at K 17, using ln 0.** All 626 programs with K ≤ 15 are excluded. The word is `11111E1EEEE11EE1E`. **Without ln 0, 1/e is minimal at K 19.** The only program with K ≤ 17 that equals 1/e is that K 17 word, and it takes ln 0. The K 19 word is `11111EEE1EE11E1EE1E`.
- **e + 1 at K 19, using ln 0.** All 2056 programs with K ≤ 17 are excluded. The word is `111111E1EEEE11EE1EE`. **Without ln 0, e + 1 is minimal at K 21.** The only program with K ≤ 19 that equals e + 1 is that K 19 word, and it takes ln 0. The K 21 word is `111111EEE1EE11E1EE1EE`.
- **e² at K 21.** All 6918 programs with K ≤ 19 are excluded, with or without ln 0. The word `111111EEE1EE11EE1EE1E` does not use ln 0.

## How towers.py decides a tower program

decide.py follows towers only in a few fixed shapes. The programs it left open nest a tower such as T5 = exp(exp(exp(exp(e)))) inside logs, sums and further exponentials, so the value carries a phase within 10^(−1656519) of a multiple of π, or is the difference of two towers. towers.py evaluates each program in two layers:

- **An exact layer.** A value is an integer combination of atoms: 1, iπ, exp(w), ln(z), and ln(1 + u). Equal atoms cancel exactly. The rewrites are exp(ln z) = z, exp(w + kπi) = (−1)^k exp(w), and ln(±exp w) = w, with the multiple of 2πi fixed by the lower cut. When one term t of a sum v is larger than the rest r (|r/t| < 1/e, certified), ln v is split as ln t + ln(1 + r/t), and the 2πi correction comes from the sign of Im(r/t), which the exact layer computes term by term. So ln(e − T5) is exactly T4 − iπ plus a tiny real atom, not an interval.
- **A rigorous enclosure for each atom**: an interval rectangle, or ±exp(W) with W itself an enclosure. ±exp(W) is a tower, huge or tiny, that keeps its phase, and it is never 0. A sum absorbs a term e^50 times smaller into W with a proven bound, and two comparable exponentials exp(w1) ± exp(w2) are combined through w2 − w1 from the exact layer, so a shared tower cancels.
- When a branch is not known, because ln(exp w) depends on Im w mod 2π with Im w a tower, or the sign of a phase below e^(−10^15) is lost, the real part is still exact. The unknown −2πin becomes an atom of its own, purely imaginary, with a range for n, or with no range when Im w is a tower.
- A tower can carry its phase apart from W, and a tower value its exact imaginary part, both summed atom by atom in the exact layer or taken from deep.py (`--deep`, and `--word` when cos θ is strictly signed).

A program is excluded when value − target is a nonempty combination whose enclosure is ±exp(W), or a rectangle, or an imaginary part summed atom by atom, or a real part without the purely imaginary atoms, that misses 0. On each of the 6918 programs with K ≤ 19 and each of the targets 0, −1, 2, −2 and +iπ, no program that one of towers.py and decide.py finds equal to the target is excluded by the other. towers.py excludes a few more, such as −1 + exp(e − exp(exp(e − 1))), which decide.py leaves open. Each of the 4138 finite values that plain 300-bit evaluation reaches away from the cut lies in towers.py's enclosure.

## Analysis of the two remaining K 25 programs for −2 without ln 0

The unconditional status of −2 without ln 0 at K 27 remains **shortest known (not proved minimal)**. Excluding the two remaining K 25 programs is the sole gap: all 82500 programs with K ≤ 23 are excluded unconditionally (with `--deep`); of the 208012 K 25 programs, 6 take ln 0 and 208004 are excluded unconditionally (including 16 via `deep.py`), leaving only the two words below; and `1111111EEE1EE11EEE1EE11E1EE` is a verified K 27 word for −2 without ln 0 (`towers.decide` returns exact equality).

Let T1 = e, T2 = e^e ≈ 15.15426, T3 = exp(T2) ≈ 3814279.10, T4 = exp(T3) ≈ 10^1656520.37, and T5 = exp(T4). Since e − T2 < 0, on the lower cut (Arg in [−π, π)) we have ln(e − T2) = L − iπ where L = ln(T2 − e) ≈ 2.52059, so

    z = e − ln(e − T2) = e − L + iπ   (Re z ≈ 0.19769 > 0, Im z = π > 0).

Using exp(x − ln y) = exp(x)/y (exact for any branch), the two undecided K 25 words are:

- **w1** = `11E1E1111E1E1EEEE1E1E1E1E` = exp(exp(exp(W))) = exp(exp(V1)), with W = T4/z and V1 = exp(W).
- **w2** = `11E1E1E1111E1E1EEEE1E1E1E` = exp(exp(V2)), with V2 = T5/z.

### Exact algebraic reduction and sign/magnitude structure

For either j ∈ {1, 2}, the equality wj = exp(exp(Vj)) = −2 forces

    exp(Vj) = ln 2 + (2k + 1)iπ   for some k ∈ Z,

equivalently

    e^(Re Vj) cos(Im Vj) = ln 2   and   e^(Re Vj) sin(Im Vj) = (2k + 1)π,

or Vj = ln(ln 2 + (2k + 1)iπ) + 2πim for some k, m ∈ Z.

In neither word does a sign or magnitude bound exclude this identity:

- For **w1**, `deep.py`'s 5.5-million-bit enclosure of θ = Im W mod 2π gives θ = −5.39531064387935195139… (congruent to +0.8878746633… mod 2π), so cos θ = +0.63106214288953973449… > 0 and sin θ = +0.77573228101688673680… > 0. Thus Re V1 = e^(Re W) cos θ > 0 and Im V1 = e^(Re W) sin θ > 0 (both ≈ exp(4.65 × 10^1656518)). Had cos θ been negative, Re V1 would have been huge and negative, forcing |exp(V1)| < ln 2 and excluding w1 immediately; because cos θ > 0, e^(Re V1) ≫ ln 2 and cos(Im V1) = ln 2 · e^(−Re V1) ∈ (0, 1) is not ruled out by magnitude alone.
- For **w2**, Re z / |z|² ≈ 0.019951 > 0 and Im(1/z) = −π / |z|² ≈ −0.317054 < 0, so Re V2 = T5 · Re z / |z|² > 0 and Im V2 = −T5 · π / |z|² < 0. Again, had Re z been negative, |exp(V2)| < ln 2 would have excluded w2 immediately; because Re z > 0, e^(Re V2) ≫ ln 2 and no sign or magnitude obstruction arises.

### Why direct numerical enclosure is infeasible

Excluding wj = −2 via the phase condition |cos(Im Vj)| > ln 2 · e^(−Re Vj) requires enclosing Im Vj mod 2π to better than 1 radian, which needs working precision strictly greater than log2 |Im Vj| bits:

- For **w1**: log10(Re W) = log10(T4) + log10(Re z / |z|²) ≈ 1656518.67, so
  log2 |Im V1| = log2(e^(Re W) sin θ) ≈ Re W / ln 2 ≈ 6.71 × 10^1656518 ≈ 10^1656518.83 bits.
- For **w2**: log10(T4) ≈ 1656520.37, so
  log2 |Im V2| = log2(T5 · π / |z|²) ≈ T4 / ln 2 ≈ 3.36 × 10^1656520 ≈ 10^1656520.53 bits.

Checking the modulus condition e^(Re Vj)/π ≈ |2k + 1| (mod 2) is worse by a further exponential (≈ e^(Re Vj) / ln 2 bits). Both bit counts have over 1.65 million decimal digits — far beyond physical computation — so no numerical enclosure can decide either word.

### Why known unconditional transcendence theorems do not apply

Standard unconditional transcendence results do not refute exp(Vj) = ln 2 + (2k + 1)iπ:

- **Hermite–Lindemann / Lindemann–Weierstrass** require algebraic exponents; neither V1 nor V2 is known to be algebraic (even the irrationality of T2 = e^e is open), and even if Vj were algebraic and nonzero, Hermite–Lindemann would only yield transcendence of exp(Vj), which does not contradict exp(Vj) = ln 2 + (2k + 1)iπ (itself transcendental, since exp(ln 2 + (2k + 1)iπ) = −2 ∈ Q).
- **Gelfond–Schneider** applies to α^β with algebraic α ∉ {0, 1} and algebraic irrational β; neither identity reduces to that form.
- **Baker's theorem** applies to linear forms in logarithms of algebraic numbers; here ln(ln 2 + (2k + 1)iπ) is the logarithm of a transcendental number, and T4, T5, L = ln(T2 − e) are not algebraic.

Deciding w1 ≠ −2 or w2 ≠ −2 unconditionally is an instance of the constant problem for exponential-logarithmic (EL) numbers, which remains open without Schanuel's conjecture.

### Conditional exclusion assuming Schanuel's conjecture

> **Conditional result (not used for project claims).** Per project policy, no minimality claim in this repository depends on Schanuel's conjecture. The proof below is recorded only as a conditional result; unconditionally, −2 without ln 0 at K 27 remains shortest known.

**Proposition (assuming Schanuel's conjecture).** *Neither w1 nor w2 equals −2. Consequently, assuming Schanuel's conjecture, −2 without ln 0 is minimal at K 27.*

*Proof.* Recall Schanuel's conjecture (SC): if α1, …, αn ∈ C are Q-linearly independent, then tr.deg_Q Q(α1, …, αn, e^(α1), …, e^(αn)) ≥ n.

1. **Algebraic independence of T1, T2, T3, T4, T5, L, iπ, ln 2.**
   - By induction on m ∈ {1, …, 5}: T1 = e is transcendental; if T1, …, Tm are algebraically independent over Q, then {1, T1, …, Tm} is Q-linearly independent, so SC gives tr.deg_Q Q(T1, …, T_(m+1)) ≥ m + 1, hence T1, …, T_(m+1) are algebraically independent. In particular T1, T2, T3, T4, T5 are algebraically independent over Q.
   - Next, L = ln(T2 − T1) is Q-linearly independent of {1, T1, T2, T3, T4}: if L = q0 + q1 T1 + q2 T2 + q3 T3 + q4 T4 with qj ∈ Q and common denominator D ≥ 1 (aj = D qj ∈ Z), exponentiating D L yields (T2 − T1)^D = T1^a0 T2^a1 T3^a2 T4^a3 T5^a4. By algebraic independence of T1, …, T5, this must hold in Q(X1, …, X5), which is impossible since the irreducible polynomial X2 − X1 does not divide any Xj. Applying SC to {1, T1, T2, T3, T4, L} (with e^L = T2 − T1 ∈ Q(T1, T2)) shows T1, …, T5, L are algebraically independent over Q.
   - Since 1, T1, T2, T3, T4, L ∈ R while iπ ∈ iR \ {0}, {1, T1, T2, T3, T4, L, iπ} is Q-linearly independent. With e^(iπ) = −1 ∈ Q, SC shows T1, …, T5, L, iπ are algebraically independent over Q.
   - Finally, ln 2 is Q-linearly independent of {1, T1, T2, T3, T4, L, iπ}: taking imaginary parts forces the iπ coefficient to be 0, and exponentiating D ln 2 = a0 + a1 T1 + a2 T2 + a3 T3 + a4 T4 + a5 L (D ≥ 1, aj ∈ Z) gives 2^D = T1^a0 T2^a1 T3^a2 T4^a3 T5^a4 (T2 − T1)^a5. Unique factorization in Q[X1, …, X5] forces a0 = … = a5 = 0, contradicting 2^D > 1. With e^(ln 2) = 2 ∈ Q, SC yields that the 8 numbers T1, T2, T3, T4, T5, L, iπ, ln 2 are algebraically independent over Q.

2. **Exclusion of w2 = −2.**
   Suppose w2 = −2, so exp(T5/z) = ln 2 + (2k + 1)iπ for some k ∈ Z. Let F8 = Q(T1, T2, T3, T4, T5, L, iπ, ln 2) (tr.deg_Q F8 = 8). The 9 numbers {1, T1, T2, T3, T4, L, iπ, ln 2, T5/z} are Q-linearly independent: the first 8 are Q-linearly independent and do not involve T5, whereas T5/z = T5/(T1 − L + iπ) has T5 linearly in the numerator with z ≠ 0, so any relation involving T5/z would place T5 in Q(T1, T2, T3, T4, L, iπ, ln 2), contradicting tr.deg_Q F8 = 8. By SC, the field generated by these 9 numbers and their exponentials has transcendence degree ≥ 9. Yet T5/z ∈ F8 and exp(T5/z) = ln 2 + (2k + 1)iπ ∈ F8, so this field is F8 itself, of transcendence degree 8 — contradiction.

3. **Exclusion of w1 = −2.**
   Suppose w1 = −2, so exp(V1) = ln 2 + (2k + 1)iπ for some k ∈ Z, where V1 = exp(T4/z). Let F7 = Q(T1, T2, T3, T4, L, iπ, ln 2) (tr.deg_Q F7 = 7 by step 1). The 8 numbers {1, T1, T2, T3, L, iπ, ln 2, T4/z} are Q-linearly independent, because the first 7 are Q-linearly independent and do not involve T4 while T4/z = T4/(T1 − L + iπ) involves T4 linearly with z ≠ 0. Applying SC to these 8 numbers gives tr.deg_Q F7(V1) ≥ 8, so V1 is transcendental over F7 and tr.deg_Q F7(V1) = 8. Consequently the 9 numbers {1, T1, T2, T3, L, iπ, ln 2, T4/z, V1} are Q-linearly independent, so SC gives tr.deg_Q F7(V1, exp(V1)) ≥ 9. Yet exp(V1) = ln 2 + (2k + 1)iπ ∈ F7, so F7(V1, exp(V1)) = F7(V1) has transcendence degree 8 — contradiction. □
