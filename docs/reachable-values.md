# Reachable EML values

How many distinct finite complex numbers can be obtained from the constant 1 and the operator `eml(x, y) = exp(x) − ln(y)`, using at most *n* ones?

This note records the convention, the counts through *n* = 10, and how they were obtained. It is a project document, not a sequence submission.

## Convention

Convention used in the project enumerations of November 2026. In brief:

- A **program** is a valid RPN word over the alphabet `{1, E}`. The token `1` pushes the constant 1. The token `E` pops *b* then *a* and pushes `exp(a) − Log(b)`. A program with *n* ones has length *K* = 2*n* − 1 (a full binary tree with *n* leaves and *n* − 1 eml nodes). Counts are indexed by *n*, starting at *n* = 1, not by *K*. Only odd *K* occur.
- **Log** is the principal branch, with imaginary part in (−π, π]. The lower cut, imaginary part in [−π, π), gives the same counts: the value of any program on the lower cut is the complex conjugate of its principal value. The definition can therefore just say “principal.” (The calculator app uses the lower cut, ln(−1) = −iπ; every count below is the same for it.)
- **Log 0 = −∞** and **exp(−∞) = 0**. An infinity keeps its phase: it is stored as ±∞ + *i*·*b* (with *b* exact or a certified ball), or as a directed infinity at angle *t*. The rules, as implemented in emlcore, are:
  - exp(*z*) = 0 whenever Re *z* = −∞.
  - exp(+∞ + *i b*) = +∞ when *b* = 0 exactly; otherwise it is the directed infinity at angle *b*.
  - exp of a directed infinity at angle *t* is 0 when cos *t* < 0, and NaN otherwise.
  - Log(+∞ + *i b*) = +∞.
  - Log(−∞ + *i b*) = +∞ ± *i*π, with the sign of *b*. When *b* = 0 exactly, the branch convention decides: +*i*π on the principal cut, −*i*π on the lower cut.
  - Log of a directed infinity at angle *t* is +∞ + *i t*, with *t* reduced into the branch window.
  - *x* − (±∞ + *i b*) = ∓∞ + *i*(Im *x* − *b*) for finite *x*; exp(+∞ + *i b*) − Log *y* = +∞ + *i*(*b* − Im Log *y*) for finite *y*; +∞ − (−∞) = +∞.
  - ∞ − ∞ with the same sign, and any directed infinity combined with another infinity, are NaN; those programs are discarded. Zero is unsigned.

  A program is counted only if its **final** value is a finite complex number. Programs that pass through −∞ internally and still finish finite are included (for example the length-15 word for −1). Final ±∞ and NaN are not counted. Non-real values are counted.
- Two programs contribute once if and only if their values are **equal as complex numbers**. There is no float tolerance. Float-keyed dumps (for example 2⁻⁴⁰ or long-double buckets) merge values that are actually distinct and **undercount**; they are not used as terms here.

## The counts

Let *a*(*n*) be the number of distinct finite values reachable with **at most** *n* ones (*K* ≤ 2*n* − 1).

| *n* | *K* ≤ | *a*(*n*) | status |
|---:|---:|---:|---|
| 1 | 1 | 1 | proven |
| 2 | 3 | 2 | proven |
| 3 | 5 | 4 | proven |
| 4 | 7 | 9 | proven |
| 5 | 9 | 20 | proven |
| 6 | 11 | 53 | upper bound, exact under the collision conjecture; *L* = 51 |
| 7 | 13 | 156 | upper bound, exact under the collision conjecture; *L* = 144 |
| 8 | 15 | 483 | upper bound, exact under the collision conjecture; *L* = 420 |
| 9 | 17 | 1548 | upper bound, exact under the collision conjecture; *L* = 1276 |
| 10 | 19 | 5059 | upper bound, exact under the collision conjecture; *L* = 3942; R1–R5 cross-check done (see below); independent reproduction pending |

For *n* ≤ 5, every merge in the enumeration is a sound rewrite, and the remaining forms are separated by certified Arb balls, so the count is exact.

For *n* = 6..10, the tabulated *a*(*n*) is a rigorous **upper bound** *U*(*n*): the number of distinct canonical forms. A proven **lower bound** *L*(*n*) is the size of a set of those forms whose Arb balls (2048 or 8192 bits) are pairwise disjoint. *L* is obtained from a greedy independent set, so it is valid but not necessarily the best possible. The gap is mostly towers whose balls overflow, or pairs that differ by about exp(−*e*^*e*^*e*) and are not separated by ball arithmetic alone. For *n* ≥ 6, deciding whether a subtree is exactly 0 (and so whether Log 0 = −∞ applies) rests on the same conditional footing; a missed zero can only add values, so *U* stays an upper bound.

**Two rule sets.** *U*(*n*) comes from emlcore's canonical forms. Every emlcore rewrite is a sound identity:
- exp(0) = 1;
- exp(*f* + *i*π*m*) = (−1)^*m* exp(*f*);
- exp(Log *g*) = *g*;
- Log 1 = 0;
- Log(±exp *g*) = *g* (+ *i*π) − 2π*i k*, with *k* certified;
- Log of a provably negative real = Log of its absolute value ± *i*π, by the cut.

Forms are integer linear combinations of exp and Log atoms, so emlcore has **no rational-function (field) normalisation**. compscibot's R1–R5 is a separate, independent rule set (listed below). It is not the same system, and it is strictly stronger here:
- Through *n* = 9 (*K* ≤ 17) the two give the identical partition into classes, with no missed and no extra merges.
- At *n* = 10 (*K* = 19), R1–R5 merges six pairs that emlcore keeps apart, and nothing goes the other way: 5065 emlcore forms against 5059 R1–R5 classes, with 0 misses.
- All six pairs are true identities. Each pair's two words evaluate to the same closed form, exactly (a cut-aware exact sympy evaluator, on both cuts) and agree to 200 digits. The common values are (*e*^*e* + 1 − *e*)/(*e* − 1), *e*/(*e*^*e* − *e*), *e*^(*e*−1)/(*e* − 1), *e*²/(*e*^*e* − *e*), 1/(*e* − 1) and *e*^(*e*^*e*)/(*e*^*e* − *e*^(*e*^*e*)), from words of lengths 11/19, 15/19, 17/19, 17/19, 17/19 and 19/19.

So *U*(10) = 5065 − 6 = **5059**: emlcore's sound merges plus six proven identities. The earlier figure 5065 is superseded.

The upper bound is exact if the **collision conjecture** holds: two programs with at most 10 ones have equal values only when that equality follows from the rewrite rules R1–R5, so distinct R1–R5 normal forms are distinct numbers. For *n* ≤ 10, every emlcore merge is also an R1–R5 merge, so this is the stronger of the two possible statements. The count it makes exact is the proven bound 5059, not one that rests on R1–R5's numerically decided side conditions. The rules are: R1, Log(exp S) = S when S lies in the branch window; R2, exp(Log T) = T; R3, exp(a + b) = exp(a)·exp(b) and exp(k·m) = exp(m)^k; R4, sums and products are normalised as commutative–associative multisets with rational coefficients; R5, rational-function normalisation, with the Log of a product split into the Logs of its factors plus an explicit unwinding multiple of Log(−1). That is a statement about this rewrite system, not a claim about Schanuel’s conjecture, and it is not derived from Schanuel here.

The values 483 and 1548 quoted elsewhere in the project are *a*(8) and *a*(9). The figure 5065 quoted elsewhere is emlcore's raw count for *n* = 10, before the six field identities; *a*(10) ≤ 5059. Field identities that emlcore lacks first matter at *n* = 10. At *n* = 11 (*K* = 21) even R1–R5 has one miss, so the table stops at *n* = 10. That is why *n* ≥ 6 is stated only conditionally.

The lower cut produces the same *a*(*n*), *L*(*n*), and *U*(*n*) (conjugation).

### Companion counts

Same convention, same proven / upper-bound split (proven for *n* ≤ 5; *n* ≥ 6 exact only under the collision conjecture).

| *n* | *b*(*n*), first appears at *n* | *c*(*n*), some program with exactly *n* ones | *a*₀(*n*), programs that never evaluate Log 0 |
|---:|---:|---:|---:|
| 1 | 1 | 1 | 1 |
| 2 | 1 | 1 | 2 |
| 3 | 2 | 2 | 4 |
| 4 | 5 | 5 | 9 |
| 5 | 11 | 12 | 20 |
| 6 | 33 | 35 | 53 |
| 7 | 103 | 107 | 156 |
| 8 | 327 | 336 | 482 |
| 9 | 1065 | 1089 | 1544 |
| 10 | 3511 | 3596 | 5048 |

*b*(*n*) = *a*(*n*) − *a*(*n* − 1). Both *b*(*n*) and *c*(*n*) are at most the Catalan number *C*(*n* − 1), the number of valid programs of length 2*n* − 1; the first collapse is at *n* = 5 (*C*(4) = 14). The *n* = 10 row includes the six field identities. Before them, emlcore's raw values were 3517, 3599 and 5053. Like *a*(10), independent reproduction is still pending.

*a* and *a*₀ agree through *n* = 7. They first differ at *n* = 8: the value −1, whose shortest word has length 15 and uses Log 0. The first Log-0-free word for −1 has length 17. The differences *a* − *a*₀ are 0, 0, 0, 0, 0, 0, 0, 1, 4, 11.

## How the counts were computed

Every program up to *K* = 19 was enumerated with emlcore and reduced to a canonical form. Two programs are merged only when their canonical forms are identical, so merging is symbolic and never uses a floating-point key; that gives *U*. Distinctness is certified only by disjoint Arb balls; that gives *L*.

compscibot’s independent R1–R5 normal form, on the lower cut, reproduced *a*(6)..*a*(9) = 53, 156, 483, 1548, with no missed and no extra merges. At *n* = 10 it found 5059 classes against emlcore's 5065: the six extra merges are the proven field identities above, and it missed nothing. Its branch side conditions (the R1 window and the unwinding integer) are decided numerically at 60 digits when the signs cannot be certified, so it is an independent cross-check, not a proof. The corrected *n* = 10 counts were recomputed on both cuts by merging the six pairs into emlcore's classes.

The counts were recounted on both cuts through *K* = 19, with no unresolved cases.

Earlier project figures (“per-level new classes … 95, 284, 860, …” and related float-principal lists) came from a float-keyed search dump. Those merge distinct values and undercount (95 vs *b*(7) = 103, 284 vs *b*(8) = 327). They are not terms of *a*, *b*, or *c*. The list “mathbot exact 1, 2, 5, 13, 37, 110” is *c*(*n*) plus infinite special keys, not a disagreement about *a*(*n*).

A program that uses ordinary IEEE complex floating point (for example C `clog` or NumPy) can put on-axis logarithms on the wrong side of the cut, depending on the sign of a zero imaginary part. Reproducing these counts requires exact arithmetic.

## Independent reproduction

**Pending.** An independent reproduction has not been recorded yet and will be added here when it is. Until then, the terms for *n* ≥ 6 should be treated as computed upper bounds  rather than as independently reproduced.

## Not found in the OEIS

These sequences were not found in read-only searches of https://oeis.org on 2026-11-20 (`fmt=json`). The searches returned no match for:

- *a*(*n*): `1,2,4,9,20,53,156,483,1548,5059`, and the prefixes through `1,2,4,9,20,53` and `483,1548,5059`
- *b*(*n*): `1,1,2,5,11,33,103,327,1065,3511` and shorter prefixes
- *c*(*n*): `1,1,2,5,12,35,107,336,1089,3596` and shorter prefixes
- *a*₀(*n*): `1,2,4,9,20,53,156,482,1544,5048` and prefixes including `482,1544,5048`
- the exact-length form counts including infinities, `1,2,5,13,37,110`

Short prefixes alone, as expected, hit unrelated sequences (for example `1,2,4,9,20` matches several entries, such as A000081, A003018 and A006958, that already diverge at the next term). A control query for the Catalan numbers returned A000108.

This note does not propose submitting the sequence.

## Credit

The operator `eml(x, y) = exp(x) − ln(y)` is due to Andrzej Odrzywołek, *All elementary functions from a single binary operator*, [arXiv:2603.21852](https://arxiv.org/abs/2603.21852). The paper and its supplementary information do not contain the counts 483, 1548, or 5065 (5065 is the uncorrected engine count; *a*(10) ≤ 5059), and they were not found in the author’s public toolkit as published counts. As far as we found, those figures come from this project’s enumerations (November 2026). An earlier project write-up labeled the enumeration “PROVEN”; that referred to the enumeration being complete, not to the values being distinct.
