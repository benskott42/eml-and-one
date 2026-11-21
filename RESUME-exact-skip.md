# Exact-skip: stopped here

Branch `cursor/exact-skip-410e`, off v1.1 `304de9a`. No pull request. Do not merge.

The code on this branch is committed and the suite below was run, but it is not ready to open. A later soundness rule (reviewbot on #33) says a skip must not treat an exact 0, or a component that absorbed a smaller term, as already separated. The disk skip below does not obey that rule. The `1` against `0` check in `lib/eml/check.ts` currently requires that skip to fire.

## What is done

- `acceptsConstantProgram` rejects before decimal.js when a conclusive float disk (`circuitDisk` via `emlDisk` / `pointDisk`) is disjoint from the target point. The skip returns false only. It never accepts. Inconclusive disks fall through.
- `enclose` keeps one ball per node in a `WeakMap`. Constant circuits are hash-consed, so a later confirm reuses a prefix it already bounded. The map does not retain nodes. Counters: `ballCacheCounts`.
- `searchConstants(..., { digest: true })` mixes an FNV-1a of committed floats at store time, including a value that a later `count -= 1` rolls back. Off unless `digest` is set.
- `lib/eml/check.ts` locks K17/19/21/23 digests, the K23 run with ln 0 off, and the disk-skip unit check.

Not built, on purpose, after the counts below:

- Sharing one confirm across equal fingerprints. `functionFingerprint` is 8 samples at 6 digits, not a proof, and each target is confirmed only until one accept.
- A lower decimal precision. The ladder is already 40 digits (reject only), then a 300-digit ball, then 280 digits only when the ball is unknown. A cheaper ball cannot certify 240 digits. A cheap value cannot safely reject, because cancellation can make it look far from the target.
- Skipping `enclose` on ln 0. Every passing non-ln-0 candidate was ball-equal, and every passing ln-0 candidate was a 280-digit accept. A ln-0 ball might still return equal in a case these runs did not see, so that skip was not taken.

## Instrumentation (v1.1 confirm probe, before the skip changed control flow)

Probe counted stages and did not return early. Same machine as the timings.

K25, 15 confirms. Wall about 550–620 ms.

| stage | count |
| --- | --- |
| float reject | 0 |
| coarse reject (40 digits, 12-digit test) | 9 |
| ball unequal | 0 |
| ball equal | 3 (e, 0, 2) |
| overflow reject | 0 |
| full accept (280 digits) | 3 (−1, iπ, −2), all ln 0 |
| full reject | 0 |
| disk disjoint | 0 |
| disk inconclusive | 9 |
| disk overlap | 6 |

Stage time: float ~1 ms, disk probe ~1 ms, coarse ~21 ms, ball ~323 ms, full ~55 ms.

Per call, the expensive ones: e ball-equal ~25 ms / 2 nodes; 0 ball-equal ~42 ms / 4; −1 full-accept ~118 ms / 7; 2 ball-equal ~116 ms / 9; iπ full-accept ~76 ms / 9; −2 full-accept ~71 ms / 10. The other iπ, 1/2, −1/2, and −2 candidates were coarse rejects of about 1–4 ms.

K29, 57 confirms. Wall about 1940–2200 ms on that probe.

| stage | count |
| --- | --- |
| coarse reject | 48 (ln 0 off, ~63 ms together) |
| ball unequal | 0 |
| ball equal | 4 (e, 0, 2, 3; none ln 0) |
| full accept | 5, all ln 0: −1 ~74 ms / 7 nodes, iπ ~35 ms / 9, −2 ~13 ms / 10, 1/2 ~42 ms / 12, −1/2 ~95 ms / 12 |
| full reject | 0 |
| disk disjoint | 0 |
| disk inconclusive | 24 |
| disk overlap | 33 |

Disk probe ~1 ms, coarse ~60 ms, ball ~523 ms, full ~95 ms.

### What each trick could skip

1. Disjoint float disk: 0/15 confirms at K25 and 0/57 at K29. The coarse rejects were inconclusive or overlapping, not disjoint. Share: 0.
2. One confirm for equal fingerprints: nothing to share. One accept ends that target, and the rejects are different circuits. A fingerprint is not a proof. Share: 0.
3. Ball cache: this is the time. A first K29 encloses 32 new nodes and reuses 39. The next run in the same process reuses all 9 roots and encloses nothing new.
4. Lazy precision: the existing ladder already does the cheap reject first. Lowering the ball's precision cannot certify the accepts. Share of a further cut: not safe.

## Timings and RSS

Fresh process, four runs, drop the first. v1.1 is `/tmp/eml-v11-now` at `304de9a`, same machine, default `searchConstants`.

| K | this branch, cold then warm | v1.1, cold then warm |
| --- | --- | --- |
| 25 | 429, then 142, 129, 128 | 536, then 391, 375, 387 |
| 27 | 709, then 411, 384, 377 | 858, then 710, 660, 677 |
| 29 | 1942, then 1407, 1429, 1383 | 2727, then 1992, 1951, 1917 |

Pools: K25 180937, K27 613511, K29 2099314. Disk skips on those searches: 0. First-run ball hits/misses: K25 22/18, K27 22/18, K29 39/32. Later runs: 6 or 9 hits and 0 misses.

One K29 in its own process: this branch max RSS 257456 KB, heap about 12 MB, 1980 ms, 57 confirms, 0 disk skips. v1.1 the same way: max RSS 261740 KB, heap about 12 MB, 2268 ms. An earlier v1.1 single was 263176 KB.

## What was run

Passed on this commit's tree: `tsc`, eslint on the three touched files, `npm run eml:parity` (ln 0 on and off), `eml:check:core`, `eml:check:isolate`, `eml:check:props`.

Digests matched: K17 pool 1569 digest 3917316957; K19 pool 5013 digest 418583411; K21 pool 16311 digest 900952470; K23 pool 53982 digest 3518807416; K23 with ln 0 off, pool 44057 digest 3829186137. Sound K21 hits matched the default hits.

Not run: CI. This branch was not pushed when those local checks ran, and there is no pull request.

## Required soundness tests (not written)

Reviewbot on #33: a lost term that lands in an exact-0 component never retriggers, so #33 certifies values v1.1 does not. This branch must not grow the same hole. A skip may not treat an exact 0, or any absorbed component, as already separated. The disk skip and the `1` vs `0` check do that today and have to be narrowed before any PR.

Add these as soundness rows. They are calculator expressions, not constant-search hits. Assert the exact result the way v1.1 does (not certified where v1.1 is not certified). Never accept, and never reject early, because a component is exact 0.

- `((1+10^(-130))-1)+i/2` shows 0.5i and #33 calls it a match
- `(i*(1+10^(-130))-i)*i+i/2`
- `((1+10^(-110))-1)+i*10^10/3`
- `((1+10^(-136))-1)+i*3/2` — v1.1 says not certified, #33 certifies
- `k = 124..132` crossed with `c` in `{1/2, 1/3, 3/2, −1/2}` (42 certified-wrong rows out of 1,314 cross-component rows on #33)
- cancellation-born zero components in general, not only the rows above

Pre-existing on v1.1 as well, so it is not a regression test for this branch's skip: `(i*(1+10^(-124))-i)*i+i*10^10/3` drops its real part `−10^(−124)`. That known-failing row lives on `cursor/gate-absorb-retry-410e`, not here.

## Next steps

1. Stop treating an exact-0 component, on the disk or on the target, as a separation. The constant targets all have a zero part, so a correct guard makes the disk skip fire on none of them. Re-check the `1` vs `0` unit test after that.
2. Add the rows above. A full decimal.js confirm remains the only accept.
3. Re-run the digest rows, parity both ways, and sound K21 after the guard. The ball cache does not change a verdict; the disk guard must not either.
4. Only then open a draft PR into v1.1. The body has to say why every remaining skip is implied by the full confirm.
