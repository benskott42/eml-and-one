# Architecture plan

Written 2026-11-25, after 1.0.3 and the audit that followed it. This is a work plan for whoever picks the engine up next, person or model. Each step is small enough for one pull request, and each says how to tell it is done. Update the status table at the end as steps land.

## Why

Exact mode evaluates a circuit at 120 to 480 digits and then decides whether to certify the result. That decision rests on facts recorded beside the nodes while the circuit is built: this node is the integer 3, this one is 2π, this infinity points along +i, this one dropped a series term, this one must not be certified.

Those facts live in about 38 `WeakMap` and `WeakSet` tables spread over `library.ts`, `lowering.ts`, `node.ts` and `exact.ts`. Each table is written by some builders and read by others, and each has to be carried by hand through every operation and across the worker wire. Most of the wrong or refused results fixed in 1.0.3 came from one of three causes:

1. **A fact was lost on the way.** arctan(i) lost its direction because i·i was not recorded as −1. sinh(−0) left a mark on a shared leaf that leaked into later expressions. A new fact has to be threaded through add, sub, mul, div, neg and the wire by whoever adds it, and nothing says when one was missed.
2. **A rule stood in for a proof.** "A result far below a value past 10^308 is suspect" refused ln(10^400). A float that rounded to 0 was read as an exact 0.
3. **A check looked only at the root.** A refused node below the root was ignored until 1.0.3.

The plan removes cause 1 by construction, replaces the rules behind cause 2 with the enclosure that already exists, and makes the tests and CI easier to work in.

## Rules for every step

- **No behavior change unless the step says so.** A refactor step must leave `lib/eml/golden/golden.txt` and `golden-wire.txt` untouched and keep every check block passing. If a golden row changes, stop and explain it in the PR.
- **Soundness beats coverage.** A step may turn a certified result into "couldn't verify" only with a reason. It must never certify something it cannot prove.
- **Run before pushing:** `npx tsc --noEmit -p .`, `npx eslint --max-warnings=0 .`, all six `EML_SHARD=i/6 npm run eml:check`, all four `GOLDEN_SHARD=i/4 npm run eml:golden` with and without `-- --wire`, and `npm run eml:smoke`. On 16 cores the lot takes about 10 minutes run in parallel.
- **One pull request per step**, with a CHANGELOG line under Unreleased only when a user could see the change. Commit as benskott42 with the GitHub noreply address. Merging to main deploys the site.
- **Check blocks:** `lib/eml/check.ts` blocks carry numeric ids; a new block needs a weight in `check-shards.json`. Two open pull requests that add blocks will conflict there (see step 4).

## Step 1: one facts record per node

**Goal.** Every build-time fact about a node sits in one record, and one function per operation says what the result's facts are, given the operands' facts. Adding a fact means adding a field and its rule for each operation in one file, where a missing rule is visible.

**Where.** `lib/eml/facts.ts`. It owns the table, `factsOf(node)`, `learn(node, facts)`, and `derive(op, out, a, b)` for `add`, `sub`, `mul`, `div` and `neg`. Builders in `library.ts` call `derive` once where they used to set several tables.

**Order of migration.** One fact per pull request, simplest first. A fact is migrated when its old table is deleted, its readers use `factsOf`, and its combination rules are in `derive`.

| # | Fact | Old tables | Crosses the wire | Notes |
|---|---|---|---|---|
| 1a | angle: q·π or q·π·i, and the unit ±i | `piCoeff`, `imagPiCoeff` (library.ts) | no | Done first. |
| 1b | direction of an infinity | `directedInfinity` (library.ts), `poleSign`, `nonfiniteNode`, `maybeInfinite` (lowering.ts) | `inf`, `nfr`, `nfi` | Four tables for one idea. Fold into `infinity: { kind, quarter?, magnitude? }`. |
| 1c | exact decimal | `exactDecimals` (library.ts) | no | Already has add, sub, neg rules in `userSum` and `userNeg`. Add mul. |
| 1d | exact integer | `provenBig` (node.ts), `markedExactInt` (lowering.ts), `Range.int` | `int`, `pint` | Three ways to say "this is an integer". The largest step; do it after the others have settled the pattern. |
| 1e | refused marks | `unverifiedNodes`, `exactUnsureNodes`, `dependsCache` (node.ts) | `unver`, `xu` | `derive` propagates "depends on a refused node" at build time, which removes the walk in `dependsOnUnverified`. |
| 1f | series shortcuts | `seriesShortcuts`, `seriesErrorExps` (node.ts), `lostTiny`, `decades`, `twoScaled`, `scaledShell`, `liftedCombines` (lowering.ts) | `lead`, `se`, `dec`, `shell`, `lc`, `lift` | Group as `scale` facts. |
| 1g | structure memos | `cosArg`, `expArg`, `sqrtArg`, `onePlus`, `oneMinus` (library.ts), `realSum`, `realSub`, `negationOf`, `negOf` (lowering.ts) | no | These remember how a node was built. They can stay as they are, or become one `builtFrom` fact. Lowest priority. |

**The wire.** `wire.ts` packs and unpacks facts field by field. When a fact that crosses the wire is migrated, give `facts.ts` a `packFacts` and `unpackFacts` pair so `wire.ts` stops knowing each one by name. The `--wire` golden run is the test.

**Shared leaves.** `input` leaves are interned and are not reset by `isolateCircuit`. A fact must never be learned on a leaf that other expressions share, unless it is true of the leaf itself. `learn` should refuse a derived fact on an `input` node. This is the sinh(−0) bug.

**Done when** the tables in the "old tables" column are gone, and `grep -c "new WeakMap\|new WeakSet" lib/eml/library.ts lib/eml/lowering.ts lib/eml/node.ts` is in single figures.

## Step 2: the enclosure as the certifier

**Goal.** "Certified" means an enclosure proves it. `exact-ball.ts` evaluates the gates as balls, a center with a rigorous error radius. Today it runs only when the size rule in `refusedResult` would refuse. The other rules in `refusedResult`, `hidesBeside`, `carriesLoss` and the absorbed-term retries approximate what a radius states directly.

**How.**
1. Measure first. Run the ball on every golden expression and on a fuzz set, and record how often it confirms what the current rules certify, how often it is unsure where they certify, and the time cost. Put the numbers in the pull request.
2. Where the ball confirms every certified golden row, make the ball the first judge, and keep the old rules only as a fallback for results the ball is unsure of.
3. Delete each old rule once a fuzz shows no result depends on it.

**Starting point (fuzz of 2026-11-25).** docs/known-limitations.md lists the 10 results still certified wrong (second-order terms near 10^(−240) and smaller, and tanh, arctan and ln(tanh) of tiny imaginary or complex arguments) and the kinds of correct results the stricter rules now refuse (38 in a random set of 3,200, such as hypot(10^400, 10^400)). A rule-based fix for the first group was tried and also refused sin(2/exp(200)), where the tiny angle is noise and not data. Both groups are the test set for this step: the wrong ones must become right or refused, and the refused ones certified.

**Risks.** Speed: the ball runs at 180 digits or more. The exact worker is off the main thread, so a slower certify is acceptable up to a point; measure the p95 on the golden set. Coverage: the ball cannot take ln of a 0 it cannot prove exact, which is why hypot(10^160, −1) is still refused. Step 1's exact-zero facts are what feed it.

**Done when** `refusedResult` is a call to the ball plus the trig large-angle check, and a 5,000-expression fuzz against mpmath shows no certified wrong value and no certified value lost.

## Step 3: say what a shortcut is

Several results are recognized instead of computed: x^0, an odd function at 0, sin and cos at multiples of π/6, exp(i·kπ/2), i^n. Each returns a short program (0, 1, −1, 1/2, i) in place of the function's circuit. The answers are right, and the K shown is then the short program's, which bends the claim that every key runs its own circuit.

**Do.** Write the policy in `docs/` (which recognitions exist, why each is exact). Mark the result node with a `recognized` fact (step 1 makes this one field), and show "recognized exactly" in the note under the screen. Add a check that lists every recognition, so a new one cannot be added without the note.

**Done when** each recognition shows the note and the policy lists them all.

## Step 4: split the test file

`lib/eml/check.ts` is about 4,900 lines with about 90 numbered blocks. Two pull requests that each add a block conflict in `check.ts`, in `check-shards.json`, and in `CHANGELOG.md`, every time.

**Do.** One file per block or per topic under `lib/eml/checks/`, discovered by a glob. Derive each file's shard weight from a timing file written by the run, in place of hand-kept numbers. Keep `EML_SHARD` and `EML_ONLY_BLOCK` working, since CI and people use them. For the CHANGELOG, `merge=union` in a committed `.gitattributes` removes the conflict.

**Done when** adding a check is adding one file, and two branches that each add one merge cleanly.

## Step 5: the browser test as a script

`.github/workflows/ci.yml` holds the headless Chrome test inline, about 500 lines of JavaScript in YAML. It cannot be run locally as it stands, so a change to what the screen prints is found by CI after a push.

**Do.** Move it to `scripts/site-check.mjs`, taking the site URL and Chrome path as arguments. The workflow calls it. Add `npm run eml:site` for local use, with the Windows note that the static build needs `PAGES_BASE_PATH` set from PowerShell.

**Done when** the workflow step is one line and the script passes locally against `out/`.

## Step 6: the calculator's state

`EmlCalculator.tsx` keeps its model in React state, in refs (`modelRef`, `historyRef`, `modeRef`), and in a queue for presses made during a rebuild. Handlers that wait a task and then commit have twice overwritten a newer model with a stale copy. A single reducer, with async results delivered as actions that carry the row they belong to, would make that class of bug impossible. Not urgent: the site checks cover the known cases.

## Step 7: shrink the limitations list

`docs/known-limitations.md` is the list of caveats a reader has to trust. Steps 1 and 2 should remove entries from it. After each of those steps, re-test every entry and delete or reword the ones that no longer hold, with a check row for each one removed. Entries known to be reachable:

- hypot(2×10^(−160), 1)-style results that pass through a 0 that only the snap in the gates makes exact (step 2 with exact-zero facts).
- 1/10 + 2/10 − 3/10, 0.1·3 − 0.3 and 0.5² − 0.25 say "couldn't verify": exact decimals are followed through sums only (step 1c: add products, quotients by an integer, and integer powers).
- sinh(0.00005i) in float mode prints 0.0000499999999792i with no flag, just under the 12-digit bound, while the screen shows 12 digits. Decide whether the flag bound or the float display should move, as was done for 13- to 15-digit integers.
- Float mode drops the "this is e" naming and the rotation notice of a loaded word when a row is rebuilt by Undo or a mode switch. The 1.0.3 audit says notices are kept; re-test, and fix what is left.

## Step 8: housekeeping

Small, independent, and each its own pull request:

- **Release 1.0.4** once the fuzz of the audit (below) is clean: date the CHANGELOG section, bump `package.json` and `package-lock.json`, merge, wait for the Pages deploy, tag the merge commit, publish the GitHub release from the CHANGELOG section. The X post needs the owner to approve the exact text.
- **Fuzz after every engine step.** `tools/` has no committed fuzz. The scripts used for 1.0.3 (random trees over every function, huge and tiny leaves, cut-adjacent and pole inputs, compared with mpmath at 2,500 digits, in-process and through the wire) should be committed as `tools/fuzz/` with a README, so each step in this plan can run the same set and compare certified counts before and after.
- **Dependency bumps.** Dependabot pull requests that touch `.github/workflows` (#16, #17, #18, #20) need a token with the `workflow` scope to merge, or a click by the owner. #19 is merged.
- **Old branches.** Close the v1.1 pull requests listed below after copying anything still wanted into an issue.
- **Commit identity.** One audit commit and 14 older commits on main carry the personal email of the owner, who has said to leave them. New work uses the noreply address; a local `git config user.email` check before each commit is the guard.
- **The long-task site check.** It fails on any main-thread task over 50 ms and has tripped by chance several times. 1.0.3 and 1.0.4 removed the causes found (key captions, the submit compile, closed fold text). If it trips again, read the task list the check prints before re-running, since each past failure was a real stall.

## Not in this plan

- The two K 25 programs that keep −2 without ln 0 from being proved minimal at K 27. They turn on the phase of a tower of towers, which no precision reaches. That needs an argument, not code.
- The v1.1 branches (pull requests #1 to #5, #15, #33 to #37). They are 90 to 150 commits behind main and overlap this work. Close them, and re-derive anything still wanted on top of main.

## Status

| Step | State | Pull request |
|---|---|---|
| 1a angle facts | done | #90 |
| 1b infinity facts | open | |
| 1c exact decimal | open | |
| 1d exact integer | open | |
| 1e refused marks | open | |
| 1f scale facts | open | |
| 1g structure memos | open | |
| 2 enclosure as certifier | open | |
| 3 shortcut policy | open | |
| 4 split check.ts | open | |
| 5 site check script | open | |
| 6 calculator reducer | open | |
| 7 limitations list | open | |
| 8 housekeeping (fuzz tool, bumps, old branches) | open; 1.0.4 released | |
