# Golden Output Parity Harness

The golden-output parity harness (`npm run eml:golden`) is a regression test that ensures EML and One's behavior stays consistent across refactors and fixes. It's step 0 of the refactor plan: every later fix or refactor PR must run it, and its output must stay byte-identical unless the PR explicitly calls out the intended change with a reason.

## What it tests

For a fixed corpus of expressions, the harness records:

- **Exact-mode display text**: The result shown in exact mode (120–480 digit arithmetic)
- **Certification flags**: `certified`, `couldn't verify`, `singular:<type>`, `ln0`, `series-shortcut`
- **Float-mode display text**: The result shown in float mode
- **Float flags**: `differs-from-exact`, `underflowed`, `overflowed`, `near-cut`, `unverified`
- **Press/RPN count**: The button-press length of the compiled program
- **Pack/unpack round-trip**: Whether `packCircuit` → `unpackCircuit` preserves the exact text, the singular flag, and the unverified flag
- **Second evaluation** (wire file only): the same child evaluates the unpacked node twice. `eval2` is that repeat

The output is deterministic (no timings, no generated timestamp), sorted, and stored line-by-line. The `# rows:` header is the expression count. `.gitattributes` forces LF for the golden files so a Windows checkout does not fail every row.

## How to run it

### Check against golden output (CI mode)

```bash
npm run eml:golden              # In-process mode
npm run eml:golden -- --wire    # Fresh-process wire mode
```

Compares the current output against the checked-in golden files. Exits with code 0 if they match, code 1 with a readable diff if they differ.

- **In-process mode** (`golden.txt`): Evaluates here, then round-trips `packCircuit` → `unpackCircuit` in the same process (200k node budget)
- **Wire mode** (`golden-wire.txt`): Packs here and sends the circuit to a new Node process per row, using `v8.serialize` (signed zero and NaN survive; JSON would not). The child unpacks and reports through `reportUnpacked`, the same path as `exact.worker.ts`, at the worker's 80k node budget. It evaluates that node twice and records both screens. The `eml-wire-*` bundle directory is removed when the run finishes. A shared child is not used: an earlier row can raise working precision and make a later `cos(1e100)` or `sin(1e22)` look certified instead of `argument too large to reduce`

### Regenerate golden output

```bash
npm run eml:golden -- --update              # In-process mode
npm run eml:golden -- --update --wire       # Wire mode
```

Evaluates the corpus and writes new golden files. Use this when you've made an intentional behavior change. `--update` refuses to run when `CI` is set, so a workflow cannot rewrite the file.

### Include heavy test cases

```bash
npm run eml:golden -- --heavy
npm run eml:golden -- --heavy --wire
```

Adds slow cases (not run in CI by default). Use for thorough local testing before opening a PR.

## The PR-note rule

**Every changed line in the golden output must be explained in the PR description.**

When you run `npm run eml:golden` and see differences, you must:

1. Review each changed expression
2. Verify the change is intentional (a bug fix, optimization, or refactor goal)
3. Document why each output changed in your PR description

Example PR note:

```
Golden output changes:

- `6.103e-120*i+6.103e-120*i`: Fixed v1.1 bug where exact mode showed half the sum
  (was: 6.103×10^−120i, now: 1.2206×10^−119i). Removed KNOWN-BUG annotation.

- `ln(1+10^-130)`: Improved precision (was: 1×10^−130, now: 1.0000×10^−130)
```

Do not merge a PR that changes golden output without documenting every change.

## Known bugs

Lines marked with `# KNOWN-BUG <id>` document current wrong outputs. When you fix one:

1. Run `npm run eml:golden` to see the diff
2. Update the `BUGS` map in `lib/eml/golden/harness.ts`
3. Run `npm run eml:golden -- --update` to regenerate without the annotation
4. Document the fix in your PR description

Current known bugs:

- **v1.1-complex-half**: `6.103e-120*i+6.103e-120*i` shows half the sum in exact mode (no flag)
- **A1-real-drop**: `(i*(1+10^(-124))-i)*i+i*10^10/3` drops its real part
- **wire-real-drop** (severity-1, owned by bigfixer). Direct evaluation, the same-process round trip, and a fresh child all certify these with the real part gone:
  - `((1+10^(-130))-1)+i/2` and `((1+10^(-130))-1)+i*(1+10^(-130))/2` drop a real part near 1e-130 and show `0.5i`
  - `((1+10^(-136))-1)+i*3/2` drops a real part near 1e-136 and shows `1.5i`
- **folded-zero**: `sinh(1e-7)-1e-7` and `artanh(1e-7)-1e-7` are certified `0`
- **roundtrip**: `6*i+(-6*i)` changes text across pack/unpack. `1-cos(sqrt(1/10^130))` does too, and its second evaluation in the same process is a certified `0` (`roundtrip+cache-second`)
- **cache-second**: a fresh child reports `argument too large to reduce` for `cos(1e100)`, `cos(1e7)`, `sin(1e22)`, `tan(1e100)`, and `tan(1e22)`. The repeat in that same child certifies the same number. The first column is the fresh result
- **repeat-cache**: `cos(1e119)` repeats as a certified `−0.9849923936` (true value `−0.37226`). `sin(1e150)` repeats as a certified `−0`
- **pole-wording**: `tan(pi/2)` and `tan(3*pi/2)` are `near a pole` on a fresh eval. The repeat says `indeterminate (∞ − ∞ or 0 · ∞)`. A shared child used to show that indeterminate wording on the first pass
- **residue-stable**: `1e-100*1.5/1.5-1e-100` and `1e-50*1.5/1.5-1e-50` are exact 0 and are certified as a nonzero residue. `1e-400*1.5/1.5-1e-400` and `1e-400/2*2-1e-400` stay tagged residue-stable; the recorded exact text is 0. `exp(ln(1e-400))-1e-400` and `1e-500*e/e-1e-500` are exact 0 and are certified 0. The literal `-5e-801` row is that number, not one of these identities
- **inf-finite**: `inf+1`, `ln(0)-1`, and `ln(0)+i` show `−∞i` with `singular:uses ln 0 = −∞`. `(inf*i)/2` and `ln(ln(0)*i)` show `∞` with the same warning. `ln(0)+0` stays `−∞` with that warning and is not tagged
- **jimmy1**: `1e-320*(1+1e-100)-1e-320` (certified residue; the value is 1e-420), `exp(ln(ln(0))*i)` (`∞` with `singular:uses ln 0 = −∞`), and `exp(800)-exp(800)` (`−∞` with `singular:passed through a non-finite value`; the value is 0)

The literal `-5e-801` is `−5×10^−801`. `1e-500`, `exp(-1200)`, `1e-400*(1+1e-100)-1e-400`, `1e-400*pi+1e-400`, `exp(-1000)-exp(-1001)`, and both `−1×10^−450` forms (`1e-400-1e-400*(1+1e-50)` and `(1e-400)*3/3-(1e-400)*(1+1e-50)`) are recorded as they are today. `sqrt(-0)` is the signed-zero wire row.

`sin(9e-13+1e-120*i)` is the tripwire for the exact-zero sibling check in `residueParts` (`exact.ts`, `10^(work−12)`). Certified text is `9×10^−13 + 1×10^−120i`. The imaginary part is an exact 0 at 120 digits, and the real sibling (~9×10^−13) sits under that guard and not under `10^(work−13)`. Removing the check, or tightening the guard by one, drops the imaginary part. `sin(1e-18+1e-120*i)` also moves if the check is removed, and does not move for a one-step change of the guard. `(1+1e-20*i)-1` hits the same branch and was removed: its certified text stays `1×10^−20i` either way.

## How to add test cases

Edit `lib/eml/golden/corpus.ts`:

1. Add your expression to the appropriate array:
   - `basicExpressions`: Simple, fast cases
   - `transcendentalEdgeCases`: ln, sin, cos, tan, etc.
   - `complexEdgeCases`: Complex arithmetic edge cases
   - `infinityPowers`: Powers of directed infinities
   - `poleCases`: Poles and singularities
   - `precisionCases`: High-precision or series-shortcut cases
   - `heavyCorpus`: Slow cases (not run in CI)

2. Run `npm run eml:golden -- --update` and, when the row is wire-sensitive, `npm run eml:golden -- --update --wire`

3. Commit the corpus change and both golden files together. Explain every changed line in the PR

## Corpus

The list lives in `lib/eml/golden/corpus.ts`. `getAllCorpus` drops duplicate expressions, and the comparer rejects a golden file that still has a duplicate key or a line it cannot parse. `npm run eml:golden -- --self-test` checks that editing a row, deleting a row, repeating a key, and writing a garbage line all fail. The expression count is the `# rows:` line in the golden file.

## Cache check

`EML_NOCACHE` is read once, when `exact.ts` loads. The harness starts a child with that variable already set and evaluates `1+1`, `sqrt(-0)`, and `1-cos(sqrt(1/10^130))` twice each. With the flag on, the repeat matches the first result. Without it, the repeat of `1-cos(sqrt(1/10^130))` is a certified `0`. A child that did not see the variable fails the run.

## CI integration

The golden harness runs in `.github/workflows/ci.yml` after `eml:check`:

```yaml
- run: npm run eml:golden         # In-process mode
- run: npm run eml:golden -- --wire  # Fresh-process wire mode
```

Both modes run in CI to catch bugs in either evaluation path. Heavy cases (`--heavy`) are not run in CI.
