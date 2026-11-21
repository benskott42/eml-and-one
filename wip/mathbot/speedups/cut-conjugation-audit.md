# Item #8 audit: compute one cut, conjugate for the other

mathbot, 2026-11-20 ~11:55 PM ET. A local audit only.
- **Sources (read-only):**
  - `eml-proofs/emlcore.py`, cited as `emlcore:LINE`;
  - app v1.1 at commit **a764c58** ("Count to n (#12)"), extracted with `git archive` from the `compscibot/repo` object store into a scratch directory, never a checkout. Cited as `golf.ts:LINE`, `complex.ts:LINE`, `cut.ts:LINE`, `exact.ts:LINE`, `enclose.ts:LINE`.
- **Checks:** `speedups/checks/conj_audit.py` and `order_audit.py`, plus `checks/golf-conj/`.

## Verdicts
| engine | verdict | basis |
|---|---|---|
| emlcore, `'principal'` and `'lower'` | **Safe to apply 2×** | Code review (§2) and a structural isomorphism checked through *K* = 25 on both cuts (§2.3) |
| golf.ts (float pool) | **Safe with listed fixes** | The pool is bit-exact conjugation-equivariant through *K* = 29 with the hit pipeline off. The hit pipeline is lower-only and changes pool membership (§3) |
| exact.ts | **Safe** for getting principal values by conjugation. The 2× saving doesn't apply, because it only has the lower cut and evaluates one expression at a time (§4) | Code review |

## 1. Theorem
Write conj on extended values as follows: conj(x + iy) = x − iy; conj(±∞ + ib) = ±∞ − ib; conj(D(t)) = D(−t); conj(NaN) = NaN.

**Claim.** Suppose that for all z:
- Log_L(z) = conj(Log_P(conj z)), including z < 0, z = 0 ↦ −∞, and the infinite cases;
- exp(conj w) = conj(exp w), including the infinity rules;
- conj(a − b) = conj a − conj b, including ±∞ arithmetic.

Then val_L(w) = conj(val_P(w)) for every program w. Conjugation is a bijection that preserves equality, so the finite class sets correspond under conj and every count is equal.

*Proof.* Induction on the tree: val(E(a, b)) = exp(val a) − Log(val b), with each operation conj-equivariant by hypothesis. ∎

**The hypotheses hold mathematically for emlcore's rule set:**
- Off the closed negative axis, both cuts are the principal Log, and Log(conj z) = conj Log z.
- On the axis: Log_P(−r) = ln r + iπ and Log_L(−r) = ln r − iπ = conj(Log_P(−r)).
- Log 0 = −∞ with imaginary part exactly 0, which is self-conjugate.
- exp(+∞ + ib) = D(b) for b ≠ 0, which maps to D(−b).
- exp(D(t)) depends on cos t, which is even.
- Log(+∞ + ib) = +∞.
- Log(−∞ + ib) = +∞ + i·sgn(b)·π, and for b = 0 exactly it's +iπ (P) or −iπ (L), which are conjugates.
- Log(D(t)) = +∞ + i·red(t), with red_L(−t) = −red_P(t), including t ≡ π.
- The finite/infinite subtraction rules are linear in the imaginary parts.

The question is only whether each implementation is an exact mirror.

## 2. emlcore.py
### 2.1 Where the cut enters
- `cutsign = 1 if conv == 'principal' else −1` (`emlcore:87`). It is used in only four places:
  - Log(−exp g) for real g (`:369`);
  - Log(−k·exp g) for real g (`:395`);
  - Log of a provably negative real form (`:426-429`);
  - Log(−∞ + i·0) when b is exactly 0 (`:997-998`).

  In each case the result is conj-mirrored: c_im gets ±1 with the other parts unchanged, and forms conjugate as (c_re, c_im, Σ k A) ↦ (c_re, −c_im, Σ k conj A), where conj E(f) = E(conj f) and conj L(f) = L(conj f).
- **Every other branch decision is convention-free:**
  - **Strip integers** (`:371-380`, `:396-403`, exact rule `:315-327`) are decided on the strict window (2k−1)π < Im < (2k+1)π, so the answer is unique and on the conjugate side k′ = shift − k. The float guess `floor(t.mid() + 0.5)` (`:377`) isn't symmetric at ties, but it's only a candidate, and the strict ball test accepts only the unique k. I checked the exact rule's m //2 / (m+1)//2 case split under conj (cim → −cim, si → −si) by hand: it gives k′ = shift − k.
  - **"Off the closed negative axis"** (`:431-436`) is a symmetric predicate (Re > 0, or Im ≠ 0).
  - **Opaque Log enclosures** use Im ∈ [−π, π] for both cuts (`:163`, `:305`), which is symmetric.
  - **Log(D(t))** reduces t only when the result lies strictly inside (−π, π) (`:1010-1014`). Otherwise it uses the symmetric enclosure [−π, π] (`:1016`), and `skey` (common.py) gives such a special a fresh key, so it's never merged. That's consistent on both cuts.
  - **exp(D(t))** tests `cos t < 0` (`:982-987`). cos is even.
  - **Finite − infinite** subtraction is linear in Im (`:1029-1045`).
- **Signs of real forms** (`:461-529`) concern real values, which are conj-invariant. Real forms contain only real atoms (`:115`), so their structure is identical on both cuts.

### 2.2 Possible non-mirror points (none observed)
- Arb balls of conj forms are assumed to be exact mirror images (exp, log and sin/cos of a conjugated ball). If they weren't, one cut could settle a decision at 128 bits and the other at 512 bits. The outcome would be the same certified fact, but an Unresolved/opaque outcome could differ.
- Order-dependent rule choices (R5's first-success loop `:539-563`, R3's tie-break `:575-582`) depend on atom-id order. That order is identical on both cuts as long as every decision mirrors.

### 2.3 Empirical check (`checks/conj_audit.py`)
- I enumerated *n* ≤ 13 (*K* ≤ 25) on both cuts with the reference DP and built the **structural** map φ(principal form) = conj form, looking it up in the lower context without creating anything. The results:
  - φ is total and φ(V_P[n]) = V_L[n] **exactly as sets of form ids at every level**. The finite new classes per level are 1, 1, 2, 5, 11, 33, 103, 327, 1065, 3517, 11806, 40129, 137949 (cumulative 5065 at *K* = 19, 194,949 at *K* = 25).
  - Forms 394,320 = 394,320. Atoms 114,608 = 114,608. Opaque atoms 23 = 23, with matching opaque flags.
  - Special keys per level are equal, of the same kinds.
  - The 3 unresolved words at *K* = 25 are the same words on both cuts.
- Word by word, every principal class's shortest word evaluated on the lower cut lands exactly on φ(v): 194,949 of 194,949. The 2048-bit balls overlap the conjugate. Every special matched in kind, with the imaginary ball conjugated.
- So emlcore's two contexts are isomorphic under conjugation through *K* = 25. The theorem in §1 is a proof for the mathematics. For emlcore's code it's a review plus this check, not a proof.

**Verdict: safe to apply 2×.** Run 'principal' only and report the lower results as conjugates. Keep a regression check (`conj_audit.py`) whenever emlcore's rules change.

## 3. golf.ts (float, lower cut only)
golf.ts has no principal mode. It imports `eml` from complex.ts (`golf.ts:1`), and that eml uses `clog` = lower bank (`complex.ts:128-130, 149-156`). Item #8 would only matter for producing principal results, by conjugation, instead of a second run.

### 3.1 Code review
- **Log** (`complex.ts:114-125`):
  - The axis test `onNegativeCutF` (`cut.ts:4-7`) treats im = ±0 alike, and includes re = −∞. So `Math.atan2(±0, x<0) = ±π` is never reached on the axis, and the signed-zero trap is avoided. I measured atan2(+0, −1) = π and atan2(−0, −1) = −π in node 24.
  - Log(−0 + 0i) gives the bank (`:118`), which mirrors. Log(+0 ± 0i) = −∞ ± 0i (`:119`), which keeps the sign of zero.
  - Off the axis, `Math.atan2` is used. ECMA-262 doesn't guarantee that atan2 is odd in y, or that sin is odd or cos is even. I observed 0 violations in 10⁶ random samples (node v24.22.1).
- **exp** (`complex.ts:58-101`): `reducedTrig` uses `Math.round(im/quarter)` (`:61`). That rounds half toward +∞: Math.round(2.5) = 3 and Math.round(−2.5) = −2, both measured. So at an exact tie, ±im take different code paths (sin vs cos of ±delta). Ties are rare but possible.
- **Signed zeros are not mirrored:**
  - `delta === 0` gives sine = +0 (`:63`);
  - the axis cases at `:66-69` give −0 or +0 by axis, not by the sign of im;
  - `underflowCis` (`:88-91`).

  These don't change any value, key or cut decision: `sig` maps ±0 to the same key (`golf.ts:96`), and `onNegativeCutF` treats ±0 alike.
- **Subtraction:** `cancelled` (`complex.ts:142-147`) is symmetric in sign.
- **Keys** (`golf.ts:94-107, 154-158`): `sig` encodes a sign flag plus |x|, so key(conj z) differs from key(z) only in bit 20 of word 2.
  - The salts (`golf.ts:303-310`) and the overflow marker (`:285-286, 352-353`) are XORs on whole words, and they commute with that bit flip. So the table occupancy is conj-equivariant.
  - **Exception:** an infinite imaginary part. `sig(±∞)` = 1 or 2 (`:95`), which isn't a bit-20 flip, so commuting with salts can fail. That's only reachable through exp(+∞ + iθ), which gives ±∞ components (`complex.ts:74-79`). It's rare.
  - NaN pairs are skipped (`golf.ts:375`), which is symmetric.
- **Hit pipeline:**
  - CONSTANT_TARGETS (`golf.ts:42-54`) is a conj-closed set (real targets, plus `ipi` and `-ipi`). `near`/`watch` use |im| (`:89-92, 290-294`).
  - But `acceptsConstantProgram` (`:74-87`) evaluates with the lower-bank float, exact (`exact.ts`) and ball (`enclose.ts:85`) evaluators.
  - **Pool membership depends on that verdict:** a watched value is kept under its clean key only if accepted (`:348-350`). Otherwise it's demoted to the raw-salted key and possibly removed (`count -= 1`, `:351-353`).

### 3.2 Empirical check (`checks/golf-conj/`)
I made a scratch copy at a764c58 and patched it only to add an `emlPrincipal` = cexp − clogPrincipal and to export the pool arrays.
- **Hit pipeline off:** the principal pool equals the lower pool **index by index**: same (left, right), re bit-identical, im exactly negated. That held at maxK 21, 25 and 29, with pool sizes 16,311, 180,937 and 2,099,314. The only differences are signs of zero imaginary parts: 1,500,142 entries at *K* = 29, with no value or key effect.
- **Hit pipeline on (unchanged acceptance):** the pools diverge at index 7764. The pair (1, −e^e), pool index 4320 as the right operand, gives e − Log(−e^e). That's +iπ on the lower cut, accepted as `ipi@21`. On the principal cut it's −iπ, and the lower-bank acceptance rejects it, which shifts the pool. This is a harness artifact, but it shows the dependency is real.

### 3.3 Fixes required before using conjugation with golf.ts
1. Don't make a second run. The principal hit for target t is the lower hit for conj(t), with the same word, and the target set is conj-closed. Report hits by conjugating the target id (`ipi` ↔ `-ipi`).
2. If a principal float pool is ever computed directly, make `reducedTrig` symmetric: steps = sign(im)·round(|im|/quarter) (`complex.ts:61`). Also run its acceptance on the principal evaluators. Otherwise pool membership differs (§3.1).
3. Optional: make the `sig` encoding of ±∞ (`golf.ts:95`) use the sign flag, so the key map is a pure bit flip.
4. Unrelated to conjugation, and already known: the float keys decide merges (`golf.ts:296-311`). That's item 3 (sound float mode), not this item.

**Verdict: safe with the listed fixes.** Fix 1 alone is enough for the app's use.

## 4. exact.ts (lower cut only, per expression)
- **Cut handling is hard-coded to the lower bank:**
  - `negPi` (`exact.ts:139-146`);
  - on the axis only when im is exactly zero (`:146`);
  - Log(−0) = −∞ − iπ (`:141`);
  - mag = 0 with re < 0 gives −iπ (`:145`);
  - Log(−∞ ± 0i) gives −iπ via `onCut`. Log(−∞ + ib) with b ≠ 0 goes through `D.atan2`, which gives ±π by the sign of b (`:151, 159`). That matches emlcore's rule.
- **Symmetry of the rest:**
  - `atan2Fast` / `atan2Core` (`:174-222`) work on |y| and restore the sign (`:178-182`) or use odd sin and even cos (`:202-210`).
  - decimal.js `D.atan2`: 0 odd-symmetry violations in 2000 random samples (observed).
  - `cosSin` (`:81-93`) uses `toNearest`, whose default rounding is ROUND_HALF_UP = half away from zero. That's symmetric: 2.5 → 3 and −2.5 → −3, measured.
  - The dust and cancellation heuristics are all |·|-based: `cancelled` `:337-346`, `scrubDust` `:356-370`, `nearCut` `:543-547`, `dustPart` `:565-575`, and the cut-side escalation on the decade of |Im| (`:246-260, 908-922`).
  - Signed zeros are not mirrored (`cosSin` returns s = +0 at ±π, `:87-90`; `signedZeroFrom` `:72-74`). As in golf.ts, they only affect the sign of an exactly-zero part.
- **Caveat:** exact.ts's own on-axis decision rests on "imaginary part cancelled to exactly zero" under a 10^(−112) tolerance (`:344`). That's a heuristic about **truth**, not about symmetry. Conjugation preserves whatever exact.ts computes, right or wrong.

**Verdict: safe.** Principal = conj(lower) for any word. The 2× doesn't apply, because exact.ts never evaluates both cuts.

## 5. Summary
Only emlcore actually computes both cuts, and for it the saving is real: one run instead of two. At current sizes that's about 4 s per cut at *K* = 25, measured. The app engines are lower-only. For them, conjugation is a reporting rule (fix 1), not a speedup.
