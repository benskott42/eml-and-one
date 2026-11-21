# mathbot WIP checkpoint (work in progress, not reviewed). Wrapped up 2026-11-21 ~10:35 AM ET on Ben's request

Wording rule (v1, after reviewbot): "Sound normalisation; no lost emlcore merges and order-independent through K25; not terminating in general (runaway (★)/R4 recursion found at K33), none through K27." Never describe any version as confluent. Bounds (n = leaves, K = 2n−1), upper bounds only, both cuts: a(10) = K19 = 5059, a(11) = K21 ≤ 16847, a(12) = K23 ≤ 56909, a(13) = K25 ≤ 194605. 2026-11-21: bound labels corrected; earlier text shifted the index by one.

Files (in speedups/, a mirror of /workspace/eml-hub/speedups):
- r5-field-normalisation.md: v1 rule set (§4-§9, with reviewbot's must-fix wording) and **§11 "Status at wrap-up"** (v2, partial results, termination theorems, the open obstruction).
- checks/recip/emlcore_recip.py: `version='v2'` by default; `RecipCtx.version = CanonCtx.version = 'v1'` reproduces §4. The v1 copy is in superseded/emlcore_recip_v1.py.
- checks/recip/logs_v2/: v2u runs (C1 log_atoms off): allwords K25 and run_orders2 K25, both cuts; merges2_v2u_*.json.
- checks/recip/test_v2.py (K23 pairs and reviewbot's K33/K45 words), orders_words.py (word-by-word structural-hash order check, NOT yet run), allwords.py (env VER, R4MAX, MULTI, LOGATOMS), sync_commit.sh (mirror plus local commit).
- reviewbot's review: /workspace/eml-hub/reviewbot-recip.md; its scripts are in /workspace/rv/recip/.

Reviewbot must-fixes:
1. Doc: K33/K45 counterexample replaces "loop-free beyond K25"; coset claim narrowed to (★) alone; line-11 wording. DONE.
2. R4 id-order choice: limitation stated for v1 (doc §0/§6.1); fixed in v2 (akey choice). DONE.
3. LOOP keys and fallbacks counted and printed (Ext.key returns 'UNVERIFIED', allwords counts them separately). DONE in code; only exercised by v2u runs.
4. Fail-loud (★)+R4 termination guard (depth, μ-decrease, log_f re-entry, XC/XA/N re-entry, sign depth). DONE in v2 code. v2 itself not re-reviewed.
Should-fixes (plateau window check, lc precision, log_f(u) wrap, akey ball sums, certified R3 choice): done in v2 code; not re-verified at K25 with R6a/R3a.

Resume steps (run from speedups/checks/recip; the box is loaded, so run one or two jobs at a time, in the background):
1. `python3 allwords.py 13 lower` and `... principal` (final v2: LOGATOMS=1 by default). Expect 0 violations and 0 UNVERIFIED; record the K25 counts (K23 was 56908 on lower).
2. `TAG=v2 python3 run_orders2.py 13 <cut>` for both cuts, then `python3 check_merges.py merges2_v2_<cut>_13.json` and `check_merges.py logs_v2/merges2_v2u_<cut>_13.json`: numeric checks of the new merges.
3. `python3 orders_words.py 13 <cut>` for both cuts: word-by-word order independence (breakerbot's requirement). Not done yet.
4. `python3 allwords.py 14 <cut>` (K27, ~2+ min and a lot of RAM, so run one cut at a time): check that the 2 lost merges are recovered and 0 are lost.
5. `python3 test_v2.py principal`: the runaway words on the principal cut.
6. (B) open: termination of C0's unrestricted R6/R3 log recursion (doc §11.3). The third K23 pair (111E11EEE111EEE) needs division with a non-E term; not attempted.
7. After each step: update doc §11, run `checks/recip/sync_commit.sh "<msg>"` (local commit only; no push by mathbot's executor).

The reference engine is emlcore.py in eml-proofs. It is not copied here; never edit it.
