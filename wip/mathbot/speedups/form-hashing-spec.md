# Item #4: exact class DP with additive form hashing (spec)

mathbot, 2026-11-20 ~11:45 PM ET. A local spec only. Reference engine: `eml-proofs/emlcore.py` (cited as `emlcore:LINE`). Reference DP: `mathbot/schanuel/hunt/common.py` `enumerate_values`. The scripts for every measurement here are in `speedups/checks/`, and their logs sit next to them.

## 0. Summary
- **Soundness holds.** On emlcore's finite pair path the hash is exactly additive, and it cannot cause a wrong merge, because every hash hit is confirmed by full form equality. §2 and §4 give the proofs.
- **The expected speedup is small, and that contradicts the shortlist.** I profiled the reference DP on this box (Python 3.13, python-flint 0.9) at *n* = 13 (*K* = 25):
  - 96% of pairs produce a **new** class (138,523 new out of 144,076 pairs). Only 3.8% are duplicate hits.
  - Time splits roughly 55% `log_f`, 14% `exp_f` and 31% "rest". The "rest" is mostly `intern`, which builds the ball of each new form.
  - The pair-stage key build (`add` called from `eml_val`) is about 8% of runtime (cProfile, *n* = 12).

  So hashing can only remove a share of that ~8–10%. **My estimate for end-to-end gain on the exact class DP is ≤ 1.1×**, not the 3–10× (compscibot) or 10–50× pair-stage (mine) quoted in the shortlist. Those figures assumed the pair stage was dominated by duplicate lookups, and in a class DP it isn't: pairs(*n*) ≈ 1.04 × new(*n*).
- **What hashing is still good for:**
  - a compact, exact-safe dedup layer (8–16 B per class) for a compiled or out-of-core engine;
  - a deterministic shard key for parallel insert;
  - O(1) "certainly different" filtering in *targeted* searches.

  The real costs are per new class: exp/Log construction, sign and strip decisions, and ball evaluation. A speedup has to attack those, for example by compiling the engine or by parallelising new-class construction (§6.2).

## 1. Data model
- **Atom table.** Atom id → (kind ∈ {E, L}, arg form id, real flag, opaque flag, R1[a], R2[a]). Atoms are interned by (kind, arg fid), as at `emlcore:211-220`. The weights R1[a], R2[a] are drawn uniformly from Z_p when the atom is created.
- **Form arena.**
  - Form id → (c_re, c_im, terms sorted by atom id with nonzero integer k), plus the real flag, the PRECS[0] ball, h1 and h2.
  - Forms are interned by exact key (`emlcore:107-123`). The hash table maps (h1, h2) → list of fids, and the key is the confirmation.
- **Per-class memo.**
  - exp_fid[f] and log_fid[f] (`emlcore:250-281`, `341-348`), with h(exp_fid[f]) and h(log_fid[f]) cached beside them.
  - The balls of those forms.
  - The class representative (shortest word).
- **Specials** (`emlcore:935-939`) are not forms. They never enter the arena or the hash. Dedup follows `common.py` `skey`: ±∞ is merged only when its imaginary part is exactly 0, and every other special gets a fresh key.

## 2. The hash
Take p = 2⁶¹ − 1. Draw R_re, R_im and R(A) per atom independently and uniformly from Z_p, and draw two independent weight sets, j = 1, 2:

  h_j(c_re, c_im, Σ k_a A_a) = c_re·R_re,j + c_im·R_im,j + Σ k_a·R_j(A_a)  mod p.

**Lemma 1 (additivity).** For forms F, G and integers s, t, h_j(sF + tG) = s·h_j(F) + t·h_j(G) mod p, where sF + tG is the key returned by `Ctx.add` (`emlcore:222-232`).

*Proof.* `add` computes c_re = s·c₁ + t·c₂ and c_im = s·i₁ + t·i₂ in exact integers, and per atom k = s·k₁ + t·k₂. It then drops the atoms with k = 0 and sorts. h is a Z-linear function of the coefficient vector. Dropping a zero coefficient removes a term 0·R = 0, and sorting doesn't change a sum. ∎

**Lemma 2 (the pair path is pure subtraction).** If neither exp(x) nor Log(y) is special, eml_val returns `intern(add(fkey[ex], 1, fkey[ly], −1))` (`emlcore:1026-1028`). There is no other normalisation on this path, so h(eml(x, y)) = h(E_x) − h(L_y) mod p, where E_x = exp_f(x) and L_y = log_f(y).

**Checked: every non-componentwise step in emlcore is per class, not per pair.** None of these needs additivity. The hash of their output is computed from the output key once per class, at O(#terms).

| step | where | what it does | hash handling |
|---|---|---|---|
| exp(0) = 1, exp(iπm) = ±1 | `emlcore:255-257` | c_im mod 2 becomes a sign | output hashed once per class |
| exp(f + iπm) = (−1)^m exp(f) | `emlcore:255, 277-279` | c_im is **removed** from the E-atom argument | E atom's arg has c_im = 0; output hashed once |
| exp(Log g) = g | `emlcore:258-261` | returns ±g | output = existing form g or −g |
| R4: exp(rest + Log w) expanded | `emlcore:262-275, 283-289` | a sum of new exp forms | output hashed once |
| Log(±exp g), strip integer k | `emlcore:359-385` | g + (shift − 2k)·iπ, with k exact | **the unwinding integer sits in c_im**, exactly (`:385`) |
| Log(k·exp g) | `emlcore:386-408` | adds the atom L(\|k\|) and c_im = shift − 2k | same |
| Log of a negative real | `emlcore:426-429`, `:369`, `:395` | adds `cutsign` to c_im | exact integer ±1 in c_im |
| R5 / R3 Log rewrites | `emlcore:531-609` | new forms built with `add` | output hashed once |
| opaque Log atoms | `emlcore:303-313, 441-452` | Log kept as an atom, with no unwinding | an ordinary atom with its own R |
| zero coefficients | `emlcore:231` | dropped | 0·R = 0 (Lemma 1) |
| real flag, ball | `emlcore:115-122, 125-140` | functions of the key | equal keys give equal data |

- **The 2πi unwinding integer.** emlcore never has a separate 2πi atom. Every branch shift becomes an exact integer in c_im (`:369, 385, 395, 408, 429`). c_im is never reduced inside forms; it's reduced mod 2 only inside exp_f. So forms differing by 2 in c_im are different values (they differ by 2πi), and the hash correctly separates them. An implementation **must not** reduce c_im anywhere except inside exp.
- **Coefficient range.** I measured the maxima at *K* ≤ 25 (lower cut): |c_re| ≤ 3, |k_j| ≤ 3, at most 8 terms, but **|c_im| up to 301,683,689,238** (unwinding integers of towers). The strip predicate caps |t| at 10¹² (`emlcore:375, 398`), so the coefficients stay far below p. Even so, the implementation should assert |coefficient| < 2⁶⁰ at intern. If that ever fails, fall back to the exact key for that form.

## 3. Pair stage
For a level *n* and each split *i* + *j* = *n*, for a ∈ V_i and b ∈ V_j:
1. If exp(a) or Log(b) is special, take the special path (`emlcore:971-1045`) and `skey`. No hash.
2. Compute (H1, H2) = (h1(E_a) − h1(L_b), h2(E_a) − h2(L_b)) mod p. That's 2 subtractions, with no allocation.
3. Look up (H1, H2).
   - **Hit:** confirm by full equality of the stored key against E_a − L_b. Use a merge-walk over the two sorted term lists, with no allocation. If the keys are equal, it's the same class. If not, treat it as a miss (a hash collision).
   - **Miss:** build the key with `add`, intern it (the ball is computed **exactly as `_ball_from_key`**, see §4.4), and record the class.
4. Commit in **pair-index order** (i ascending, then a, then b, which is `common.py`'s order), so ids and representatives match emlcore.

## 4. Soundness theorem
Let F be emlcore's canonicalisation: the sequence of exp_f / log_f / add / intern calls the reference DP makes. The hashed engine makes the same calls in the same order. It only replaces the key → fid dictionary lookup with a lookup by (h1, h2) followed by key comparison.

**(a) It never merges distinct forms.** A merge happens only after step 3's full key equality, which is the same test as `fid_of[key]` (`emlcore:108`). Hash equality alone never merges.

**(b) It never drops a reachable value.** Every pair is evaluated (step 1 or 3). A hash miss always creates a class: a miss is a *proof* of a new key, because equal keys give equal hashes deterministically (Lemma 1). A false hit is caught by the key comparison and becomes a miss. Specials are untouched. Unresolved pairs are recorded, exactly as `common.py` does. Values are dropped only where emlcore drops them (NaN/INVALID, `common.py:35`; unresolved pairs are listed, `common.py:34`).

**(c) It gives the same class partition as emlcore.** By (a) and (b), the set of keys interned and the key → class map are identical, provided F's outputs are identical. F is identical if two conditions hold:
1. **Same call order.** emlcore's canonicalisation has order-dependent choices:
   - R5 takes the first dominant atom that works, in atom-id order (`emlcore:539-563`);
   - R3 breaks ties in term order (`:575-582`).

   Atom ids depend on interning order. I tested this empirically (`checks/order_audit.py`): reversing the DP order (i descending, operands reversed) gives the **same** partition through *K* = 21 on both cuts (16,871 classes, a bijection by word re-evaluation). That's a check, not a proof. A parallel engine must therefore assign ids and commit deterministically (§6.2) or re-validate.
2. **Same PRECS[0] balls.** R3 ranks its dominant atom by `float(li[2].upper())` (`emlcore:580`), and LI reads the PRECS[0] ball (`:634-637`). So computing a new form's ball as ball(E_a) − ball(L_b) is a valid enclosure, and that would be additive too. But it can be wider than `_ball_from_key` (`:125-140`, including the expm1 special case at `:130-134`), which can change R3's choice and therefore the canonical forms. That would be sound, but **not** identical to emlcore. For an identical partition, compute balls as emlcore does. Other ball-driven decisions escalate precision until they're certified (`decide`, `:239-247`), and their outcomes are facts that don't depend on the PRECS[0] radius. The exceptions are opaque/Unresolved, which are reached only after every precision fails, at precisions computed by `_ball_from_key`.

**(d) Collision bound.** Fix distinct keys F ≠ G. Their difference vector d is nonzero, and each |d_i| < p by the assertion in §2, so some d_i ≢ 0 (mod p). h_j(F) − h_j(G) = Σ d_i R_i,j is a nonzero linear form in independent uniform R_i,j, so it is 0 with probability exactly 1/p. The two weight sets are independent, so the probability is 1/p² ≈ 2⁻¹²². The weights never influence which keys get compared, because every hit is confirmed and the engine is deterministic, so the pairs are independent of R. With Q lookups against at most M stored forms, the expected number of false candidates is ≤ QM/p². At K35 scale (Q ≈ M ≈ 2·10⁸, an estimate) that's about 10⁻²⁰. With one 61-bit hash it's about 0.02. False candidates only cost one key comparison; they never affect correctness.

Don't derive R(A) from the argument's hash, as in h(E(f)) := mix(h(f)). That would make collisions in arguments propagate, and the bound above would no longer hold without a random-oracle assumption. Use independent per-atom weights.

## 5. Variants
### 5.1 GPU (hardwarebot's design): proves "different" only
- The GPU holds a sorted array of (h1) or (h1, h2) fingerprints of all classes, plus h(E_a) and h(L_b) per class.
- Per pair, it computes H and binary-searches.
  - **Absent:** certainly not an existing class (Lemma 1).
  - **Present:** a candidate for the CPU to confirm with full key equality.
- Within a level, radix-sort (H, pair index). Singleton runs are certainly distinct from each other. Runs of length ≥ 2 go to the CPU.
- **Memory (estimate):** I extrapolated new classes per level from the measured ratios 3.36, 3.40 and 3.44 (n = 10→13), using 3.45–3.6. That gives about 0.95–1.2·10⁸ classes at *K* ≤ 35, so **0.75–0.95 GB at 8 B** (h1 only) or about 1.1–1.4 GB at 12 B. That's consistent with the 0.6–1.1 GB figure and needs most of the ~3 GB usable VRAM.
- **Soundness:** the GPU never merges, and it decides "different" only from a deterministic hash inequality. The confirm path is §3.3. hardwarebot's TDR chunking and stream double-buffering are needed.
- **Verdict (estimate):** it doesn't pay off for the exact class DP. About 96% of pairs are new classes, and each one still needs CPU form construction (intern + ball), which is the dominant cost. The GPU would only replace a hash probe the CPU does in nanoseconds. It pays off only for **targeted** searches, where most pairs are rejected and never interned.

### 5.2 CPU parallel: partition-then-insert
- Workers compute (H, pair index, a, b) for a block of pairs. They scatter into 256–1024 shards by the top bits of H1. Shard owners then confirm and insert, with batched prefetch (hash 16–32 items, prefetch buckets, then probe).
- **Determinism, required for §4(c):**
  - the pair-index tag travels with each candidate;
  - each shard processes candidates in pair-index order;
  - new fids and atom ids are assigned in a final serial pass sorted by pair index, as golf.ts does for its partition mode (`golf.ts:384-387`).
- New-class construction is the expensive part (exp_f/log_f with sign and strip decisions). It can run in parallel per new class, because every operand is in a lower level and already memoized. But the atoms and forms it interns need the same deterministic id pass, or a proof that F is order-independent (§4(c)1).
- **Speedup estimate:** limited by the serial id pass and by Amdahl on the ~31% "rest". hardwarebot's 6–9× on 16 threads applies to the parallel share, if new-class construction itself is parallelised. Not measured.

## 6. Test plan
1. **Identity with emlcore (required):**
   - finite class counts per level through *K* = 19 on both cuts: raw 1, 2, 4, 9, 20, 53, 156, 483, 1548, **5065** (new per level 1, 1, 2, 5, 11, 33, 103, 327, 1065, 3517);
   - specials per level 0, 0, 0, 0, 1, 1, 1, 2, 5, 15;
   - the same key per word for every representative.

   Because emlcore runs fast here (*K* = 25 in about 4 s per cut, measured), also require *K* = 21, 23 and 25: 16,871, 57,000 and 194,949 finite classes, with the 3 unresolved words at *K* = 25 identical.
2. **Hash checks:**
   - **Injectivity:** with fixed seeds, (h1, h2) must be injective on all interned forms. Measured: 0 collisions among 394,320 forms at *K* ≤ 25, on both cuts, and h1 alone is also injective there (`checks/conj_audit.py`).
   - **Additivity:** assert h(result) = h(E_a) − h(L_b) on every finite pair.
   - **Forced collisions:** a test mode with p = 1009 forces collisions and must still reproduce the exact partition, which exercises the confirm path.
3. **Order test:** shuffle the shard and commit order with a fixed seed and require the same partition. If it differs, that's an order-dependence bug in F, not in the hash.
4. **Performance:** report time per level and the share in the pair stage vs exp/log vs intern, as `checks/pair_stats.py` does. Claim a speedup only from that report.

## 7. Effort (estimates)
- Hash layer on top of emlcore (Python): about 1 day, plus 1 day of tests. Expected gain ≤ 1.1× (estimate from the profile).
- A compiled engine (C/C++/Rust on flint/Arb) with arena, shards and a deterministic id pass: about 2–4 weeks. That's where the real speedup would come from. I haven't estimated it numerically, because it depends on how much of log_f's sign and LI logic gets ported.
- GPU filter: about 1–2 weeks. Not recommended for the class DP (§5.1).
