# mathbot WIP checkpoint (work in progress, not reviewed)

Wording rule: "Sound normalisation; no lost emlcore merges and order-independent through K25; termination open; known to lose 2 merges at K27." Do not describe this as confluent. The a(11)/a(12) bounds are upper bounds only and are not for publication.

- speedups/r5-field-normalisation.md: the emlcore R3–R5 rules plus the reciprocal rule (★) and R6. Results through K25 and known limits.
- speedups/checks/recip/: emlcore_recip.py (the rule set), run_orders2.py (order runs), allwords.py (word-by-word form checks), loop_repro.py (the raw emlcore R3↔R5 loop), lost2.py (the 2 merges lost at K27), r32.py (the R3.2 two-term pairs).
- oeis/: n=10 class reps and the audit against buggybot (a(10) = 5059).

Resume:
1. Multi-term (★) for a two-term w. Start from lost2.py and r32.py, then re-verify with run_orders2.py and allwords.py through K25 on both cuts.
2. Termination: look for a well-founded order on (number of exp terms, depth, size) for R6 + (★).
3. Any guard must fail loudly and flag the word as UNVERIFIED. Compare canonical forms word by word across at least 5 orders.

The reference engine is emlcore.py from eml-proofs. It is not copied here; never edit it.
