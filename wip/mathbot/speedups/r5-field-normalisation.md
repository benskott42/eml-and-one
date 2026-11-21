# Field normalisation: the reciprocal rule on top of emlcore (spec + results)

mathbot. **Recreated 2026-11-21 ~08:40 AM ET.** The 23:52 version of this file was removed by someone or something
after 23:52 on Nov 20; the cause is unknown (the whole `eml-hub` tree carries 23:50–23:54 mtimes, and three task-1 logs,
`order_audit_N11.log`, `union_bound.log` and `recip_vs_nf.log`, are also gone; the other speedups docs and checks are
present). This version is rebuilt from my task-1 report and from the scripts and logs in `speedups/checks/` and
`speedups/checks/recip/`. §1–§3 summarise the task-1 findings; §4 onward is the final rule set. Local only, **not reviewed**.

> **The a(11)/a(12) bounds in this file are upper bounds, not for publication.**
>
> Agreed status wording (Jimmy1; to be used only after reviewbot signs off): 'Sound normalisation; no lost emlcore merges and order-independent through K25; termination open; known to lose 2 merges at K27.'

Naming: "emlcore R3–R5" means emlcore's internal rules: `_rule_R3` (emlcore:566-609), R4 inside `exp_f`
(emlcore:262-289, exp(rest + Log w) = w·exp(rest)) and `_rule_R5` (emlcore:531-564). These are **not** compscibot's R1–R5
(`compscibot/integers/rewrite2.py`, `notes.md`). The final rule set is called **"emlcore R3–R5 plus reciprocal rule"**.

## 0. Summary
- **Final rule set** (§4): emlcore, plus the reciprocal rule (★) with a canonical coset representative, plus R6
  ("factor the certified dominant term"), which replaces R5 and, on all-exp forms, R3. Every id-dependent choice
  emlcore makes is replaced by a structural one.
- **Results** (§5, both cuts, identical; **upper bounds**): K19 **5059**, K21 **16847**, K23 **56909**,
  K25 **194602** (+3 unresolved raw pairs, so ≤ 194605).
- **Criteria** (§7): (1) pass, word by word over all 290,512 words through K25 on both cuts. Beyond the brief, it
  fails at K27: 2 emlcore merges are lost there, a two-term-w identity. (2) pass empirically:
  partitions are identical in 5 orders through K25 on both cuts, and canonicity is argued. Termination is **not
  proven** (§6). (3) pass: all 347 new merges come from sound rules. Spot-checks: 343 agree at 200 digits, ≥ 327 are proven exactly by sympy, 0 mismatches. (4) pass: 5059 at K19, 16847 at K21 = union with all
  compscibot K21 merges.
- **New finding: unmodified emlcore is itself order-dependent and non-terminating** on two K25 words in one random
  enumeration order (§6.3). The final rule set removes that loop.
- buggybot's seventh identity, e − log(e^{2e} − e^e) = −log(e^e − 1) (`11111E11EEE11EEE1EE` = `11111E1EEEE11E11EEE`,
  K19), is **already merged by unmodified emlcore** on both cuts (identical raw forms −e − Log(1 − e^{−e})). It is not
  one of the six new K19 merges, and the final key keeps it (`checks/recip/r32.py`).

## 1. The problem (task 1)
At K19, compscibot's normal form merges six engine pairs that emlcore keeps apart (5065 → 5059). All six are instances
of the reciprocal identity

  exp(S − Log w) = exp(S)/w,   with w = c + k·e^f, so  e^{S+f−Log w} = (e^S − c·e^{S−Log w})/k.

emlcore has R4 (a +1 Log coefficient inside exp) but no rule for a −1 coefficient, so it cannot see these.

## 2. Task-1 prototype (superseded)
`checks/recip_rule.py` rewrote forms inside the DP and used a call-stack cycle guard against an R3↔R5 recursion.
It gave 5059 / 16848 / 56917 at K19/K21/K23, but it **lost raw emlcore merges** (1/7/45 at K21/23/25), because rewriting
inside the DP breaks emlcore's shape-matching rules. Its join with raw emlcore gave bounds of 16847 / 56911 / 194612
(task-1 report; `union_bound.log` no longer exists). The stale targets 16870/56992 (compscibot `notes.md` R3.2) count
only the 8 pairs compscibot proved, not all merges.

## 3. Design options (task 1)
(a) a quotient key on top of the unmodified DP (chosen), or (b) a modified engine. The key makes criterion 1 a property
to check rather than something to hope for, and it leaves the raw DP and the hashing layer (`form-hashing-spec.md`)
unchanged: the hash runs on raw forms, the key runs once per new class.

## 4. Final rule set: "emlcore R3–R5 plus reciprocal rule"
Code: `checks/recip/emlcore_recip.py` (subclasses `emlcore.Ctx`; emlcore.py is imported, never edited).

**Layer 0, `CanonCtx` (canonical emlcore).** emlcore with:
- **R6 replaces R5, and replaces R3 on all-exp forms.** For a real v = c + Σ_j k_j E(f_j) > 0 (all f_j exactly real,
  v > 0 certified by emlcore's `sign()` before the rule is called): if one term E(f_D) is certified **strictly dominant**,
  i.e. Re(f_D − f_j) > 0 for all j ≠ D and f_D > ln|c|, then

  Log v = f_D + Log u,   u = v·e^{−f_D} = k_D + c·e^{−f_D} + Σ_{j≠D} k_j e^{f_j−f_D}.

  Dominance is certified by Arb balls at 512 and 2048 bits, and otherwise (needed for towers) by emlcore's certified
  `sign()` on the exact real difference. If the constant is dominant, or no term is certified dominant, there is no
  rewrite. R6 makes **no choice**: a strict dominant is unique. emlcore's R5 is the special case c = 0 when it happens
  to pick the dominant atom. emlcore's R5 instead takes the first success in atom-id order.
- **R3 on forms with non-exp terms**: emlcore's rule unchanged, except that ties are broken by the structural key
  (`akey`), not by atom id.
- No other changes. There is no size block (§6.2) and no call-stack guard.

**Layer 1, `RecipCtx`**: layer 0 plus **(★) in `exp_f`**. For an L atom L(w) with coefficient −1 in g = R − L(w),
where w = c + k·e^f has exactly one E term and k = ±1:

  exp(S + f − Log w) = (exp(S) − c·exp(S − Log w))/k.

(★) is applied at the coset representative R − m·f that minimises **(L1 norm of coefficients, structural key)**. L1 is
convex in m, and the search window −40..40 is checked to contain the minimiser. Moving up (m < 0) divides by c, so it is
allowed only if |c| = 1. If several L atoms qualify, the one with the smallest structural key is used. R4 keeps
priority (fixed order in `exp_f`).

**Key.** N maps a layer-0 form to a layer-1 form by structural recursion: sums exactly,
N(E g) = C1.exp_f(N g), N(L w) = C1.log_f(N w). If layer 1 returns Unresolved, the key falls back to the raw form
(sound; 18 such cases at K25).

### 4.1 Soundness (criterion 3, by rule)
- **(★)** follows from exp(Log w) = w (every branch) and exp(a+b) = e^a·e^b. Its only side condition is w ≠ 0. Every L
  atom satisfies this, because emlcore creates L(w) only for certified nonzero w (emlcore:353-355, 409-456; opaque
  logs need |w| > 0 certified). It is valid on both cuts.
- **R6**: if v > 0 is real and f_D is real, then Log v = ln v = f_D + ln(v e^{−f_D}) on both cuts, since both logs have
  positive real arguments. v > 0 is certified by `sign()`, and f_D's realness is the exact `freal` flag. Dominance is
  needed only for canonicity, not for soundness.
- **R3 tie-break and candidate orders** change which valid emlcore identity is applied, not the identity.
- N replaces subterms by equal-valued forms under the same cut, so value(key) = value(word).

## 5. Results (upper bounds; identical on lower and principal)
Cumulative distinct finite values per K (the convention of the 5065 series). Scripts: `checks/recip/run_orders2.py`,
logs `o2_R6_{10..13}_{lower,principal}.log`.

| K | unmodified emlcore | canonical layer 0 | **final key** | new merges vs emlcore | compscibot NF (`collide2_12.json`) |
|---|---|---|---|---|---|
| 19 | 5065 | 5065 | **5059** | 6 | 5059 |
| 21 | 16871 | 16871 | **16847** | 24 | 16848 (1 miss) |
| 23 | 57000 | 57001 | **56909** | 91 | 56926 (18 misses, 91 over) |
| 25 | 194949 (+3 unresolved) | 194949 (+3) | **194602** (+3 unresolved → ≤ 194605) | 347 | – |
| 27 (extra, word-by-word run only) | 673478 (32 unresolved words) | – | 672176; joined with emlcore's 2 lost merges 672174 (+ ≤ 32 unresolved) | – | – |

The K27 row comes from `allwords.py` on both cuts, which gave the same numbers. It is not order-tested, and the key
alone is not a refinement there (§7, criterion 1). The independent word-by-word run reproduces the DP's key counts
56909 (K23) and 194602 (K25) exactly.

All are upper bounds on the true counts: every merge is a proven identity, and unseen identities only overcount.
The canonical layer alone is not a refinement of emlcore (at K23 and K25 it splits 1 and 7 emlcore classes and makes
other merges instead). The final key repairs every split (§7, criterion 1).
**a(11) = K23 and a(12) = K25 bounds: upper bound, not for publication.**

Timing (measured, 8 jobs on 8 cores): unmodified emlcore DP at K25 takes 3.7–4.4 s; the final variant (layer-0 DP plus
key) takes 17–20 s per order.

## 6. Canonicity (order independence) and termination
### 6.1 Normal-form definition
key(word) = N(C0(word)) is a **function of the expression**, and so independent of the enumeration order, provided
every call terminates:
1. **Hash-consing.** Within a context, a form's id corresponds one-to-one to its structure, because atoms are interned
   by (kind, argument id). So the structural keys `skey`/`akey` are id-independent invariants.
2. **Every decision is structural or value-determined.** Each branch in `exp_f`/`log_f`/`sign`/the rules depends only on
   the structural form, on certified predicates of its value, and on candidate order. emlcore's id-order choices (R5
   first success, R3 ties) are gone: R6 has no choice, R3 ties use `akey`, and (★) uses `akey` and the absolute coset
   minimiser.
3. **Memo tables** cache function values, so they do not change results.

Rewriting-system view: the strategy is deterministic, so no joinability claim is made or needed. Rule overlaps matter only for
completeness (whether two representations of one value meet). Overlaps:

| pair | analysis |
|---|---|
| (★) vs R4 | Disjoint on an atom (R4 needs a +1 Log coefficient, (★) needs −1). When both occur, R4 fires first and (★) acts in the recursive exp(rest). |
| (★) vs (★) | Two qualifying L atoms: `akey` order. The other order is not proven to give the same form; it never arises, because the choice is fixed. |
| (★) vs itself | Cannot re-fire on the same atom in its own output, because the coset minimiser is a coset invariant (it is its own representative). This was the bug fixed today: the old tie-break "smaller \|m\|" was relative, so −e − Lw and −1 − Lw were both "minimal" (lost merge at K25). |
| R6 vs R3 | Disjoint by construction (R3 is off on all-exp forms). |
| R6 vs R5 | R5 is replaced. When emlcore's R5 picks the dominant atom, it computes the same identity and the same D as R6. |
| R6 vs Log(±e^g) strip | Disjoint (the strip rule needs a single term and no constant). |
| (★) vs R6 | (★) acts in exp_f, R6 in log_f. N normalises w by (★) before R6 sees Log w; the order is fixed by structural recursion. |

### 6.2 Termination: **not proven**
- A structural size measure on R3/R5's recursive Log arguments (task-2 first variant, `size_block=True`) is provably
  well-founded. It **loses emlcore merges** (layer-0 K21 16879 vs 16871, plus unresolved pairs), so it fails criterion 1.
- The final set has no measure. What is known: (★) does not re-fire on its own atom (§6.1). R6's output u has the
  constant ±1 as its dominant top term whenever the shifted exponentials stay single atoms, so R6 does not re-fire on u
  itself. The concrete emlcore loop (R5 factoring a non-dominant atom, R3 factoring it back) is impossible under R6.
- Observed: no `RecursionError` and no loop anywhere: 5 orders × K19–K25 × 2 cuts, plus all 290,512 words per cut.

### 6.3 Counterexample: unmodified emlcore is order-dependent
In the `random1` order (`raw_dp(13, conv, 'random', 1)`), unmodified emlcore recurses forever (R3↔R5, a 4-step log_f
cycle) on
- `1111111EEEE11E1EEE11E1EEE` (K25)
- `11111111EEEE11E1EEE1E1EEE` (K25)

on both cuts. In forward/reverse/random2 order, or evaluated alone, they terminate. The loop depends on interning
order through R5's atom-id-order first success. Cycle trace: `checks/recip/loop_repro.py`, `loop_repro_lower.log`.
Consequence: raw emlcore's order independence (task-1 `order_audit.py` through K21) does not extend to K25. The final
layer 0 fixes this.

### 6.4 Remaining id-dependence (flag for review)
Arb ball sums add terms in atom-id order. Radii can differ in the last bits, which could flip a certification near a
threshold (a decision that succeeds in one order and returns Unresolved in another). This was never observed: the
unresolved lists are identical across orders. Fix for production: sum in structural-key order.

## 7. Criteria
1. **Loses no emlcore merge: PASS.** Checked word by word (`checks/recip/allwords.py`) over all 290,512 RPN words with
   ≤ 13 leaves (K ≤ 25), on both cuts, evaluated in unmodified emlcore and in the final key. There are 0 pairs that are
   emlcore-equal but key-different. The 3 words unresolved in emlcore are excluded. Also on W ∪ Wc in
   `run_orders2.py`: 0 splits.
   **Beyond the brief, at K27 (all 742,900 words with 14 leaves): 2 emlcore merges lost on each cut**
   (`allwords_14_*.log`). The two lost classes are negatives of each other. emlcore's form is
   e + e^{−L} − e^{1−L} and the key's form is e^{−L} + e^{1−e−L} − e^{2−e−L}, with
   L = Log W and W = 1 + e^{−e} − e^{1−e}. Both equal (1 + e^{1−e} − e^{2−e})/W. The layer-0 raw form differs from
   emlcore's, and the key cannot repair it, because W has **two** E terms and (★) handles one. This is the same gap as
   compscibot's R3.2 pair 0 (§7.2). So criterion 1 holds through K25 but **fails at K27** for the final set as it
   stands. The fix is a multi-term-w reciprocal rule (§9 item 8).
2. **Order-independent canonical forms: PASS (empirical) + argument §6.1; termination open (§6.2).** Forward, reverse
   and random seeds 1, 2, 3, at K19/21/23/25 on both cuts. Layer-0 partitions, key partitions, cumulative counts and
   unresolved lists are identical in every case.
3. **Every new merge is a true identity: PASS.** By rule: §4.1. Spot-checks (`check_merges.py`, `check_fail.py`) on all
   347 new merge pairs through K25, on each cut: see §7.1. 0 mismatches.
4. **Counts: PASS.** K19 = 5059 (the six pairs). K21 = 16847 = the union of the key with all 24 compscibot K21
   over-merges (`vs_nf2.py`). compscibot's single K21 miss is an emlcore merge, which the key keeps.

### 7.1 Identity spot-checks
`check_merges.py` covers all 347 pairs per cut. It requires Arb balls that overlap at 704 bits (escalating to 8192)
with both radii < 10^−200·max(1, |v|). The exact check is sympy `simplify(A − B) == 0`, or exp(A − B) == 1 exactly
together with a certified ball |A − B| < π. Results are identical on lower and principal.

| check | lower | principal |
|---|---|---|
| 200-digit agreement | 343/347 | 343/347 |
| not resolvable at 200 digits (tower values ~e^{e^{e^{e^e}}}: balls overflow even at 65536 bits; they overlap) | 4 | 4 |
| numeric mismatch | **0** | **0** |
| sympy exact 0 (13 via the exp route) | 325/347 | 325/347 |
| sympy: not simplified to 0 / timeout (10 s) | 11 / 11 | 11 / 11 |

Retry (`check_fail.py`, 120 s, exp-argument canonicalisation, up to 65536 bits) of the 11 "not 0" pairs and the 4
towers, per cut, with identical results on both cuts: 3 more settled exactly (2 "not 0", 1 tower), 9 still "not 0",
3 timeouts. The 11 pairs that timed out at 10 s were not retried. Net result:
- **exact sympy proof for ≥ 327 of 347 pairs per cut**
- 200-digit agreement for 343 of 347
- the 4 towers cannot be evaluated numerically at 200 digits (their balls overflow), and 1 of them is proven exactly
- **no pair is contradicted.**

The remaining ≤ 20 rest on the rule derivation (§4.1). sympy cannot split ln(ab) = ln a + ln b when positivity sits
inside a complex outer Log.

### 7.2 Against compscibot's collide2 lists (`vs_nf2_{lower,principal}.log`)
- K19: 6/6 NF over-merges are also merged by the key.
- K21: 24/24 merged. The 1 NF miss is emlcore-equal, so the key keeps it.
- K23: 37 of the 40 listed NF over-merges (of 91) are merged. The 12 listed misses (of 18) are all emlcore-equal and
  key-equal. Not merged by the key:
  - `11111EEE1E11EEE` = `1111111EEE1E11EEEE1EE1E` (compscibot R3.2 pair 0)
  - `1111EEE11E11EEE` = `111111EEE11E11EEEE1EE1E`
  - `111E11EEE111EEE` = `11111E11EEE111EEEE1EE1E`

  All three need a Log argument w with **two** E terms (outside (★)'s scope), as found for pair 0 in task 1.
  The unlisted 51 over-merges and 6 misses cannot be compared, because the json lists only examples. Equal totals at
  K23 (57000 − 91 = 56909 for us; NF 56926 = 57000 − 91 + 18 − overlap) are a coincidence of counts, not of partitions.
- compscibot R3.2 eight pairs (`r32.py`): pairs 1–7 merged, pair 0 not (see above).

## 8. What is proven, numeric, conjectured
- **Proven:** soundness of (★), R6 and the tie-break changes (§4.1). Hence every key merge is a true identity, given
  emlcore's certified primitives. The counts are upper bounds.
- **Exhaustively checked (finite):** criterion 1 through K25; order independence in 5 orders through K25; 200-digit
  and sympy spot-checks (§7.1).
- **Not proven:** termination of the final log_f/exp_f recursion. Without it, §6.1 is a normal-form definition only
  for inputs on which it terminates. Ball-sum order (§6.4).
- **Conjectured:** that the final set stays loop-free and order-independent beyond K25.

## 9. For reviewbot
1. R6's dominance certification via `sign()` on towers (`_pos`), and the constant comparison f_D > ln|c|
   (`_rule_R6`).
2. (★)'s canonical representative: the convex-L1 + `skey` minimiser, the window assertion, and the m < 0 ⇔ |c| = 1
   restriction (a partial normal form when |c| ≠ 1).
3. That every L atom's argument is certified nonzero, including opaque logs (the side condition of (★)).
4. Termination (§6.2): try to construct an R6/(★) cycle.
5. The emlcore loop counterexample (§6.3). This affects anything that relies on raw emlcore at K ≥ 25 in a non-forward
   order (for example a parallel DP).
6. Ball-sum id order (§6.4).
7. The 4 tower merges with no 200-digit check possible, and the sympy cases settled only via exp(A − B) = 1 plus |A − B| < π.
8. Two-term-w reciprocal identities: R3.2 pair 0 and two more at K23 are unmerged, and 2 emlcore merges are lost at
   K27 (§7). A sound multi-term version of (★) needs a canonical form for Σ p_i e^{g_i − Log W} with W multi-term,
   i.e. polynomial division by W in the exp atoms. Not attempted.

## 10. Files (`speedups/checks/recip/`)
`emlcore_recip.py` (final; superseded switches kept), `run_orders2.py` (orders, counts, criterion 1 on W ∪ Wc),
`allwords.py` (criterion 1 word by word), `check_merges.py` + `check_fail.py` (criterion 3), `vs_nf2.py`,
`r32.py`, `loop_repro.py`, `loop_words.py`, logs `o2_R6_*`, `allwords_*`, `check_*`, `vs_nf2_*`, merges `merges2_R6_*.json`.
`superseded/`: the quotient-over-raw-emlcore runs (`run_orders.py`, `orders_*.log`: these exposed §6.3), and
variants A (akey R5, loses 25+ merges at K25), B (dominant-only R5, loses 1) and C. These were run before the (★)
tie-break fix.
