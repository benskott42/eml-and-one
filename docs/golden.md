# Golden Output Parity Harness

The golden-output parity harness (`npm run eml:golden`) is a regression test that ensures EML and One's behavior stays consistent across refactors and fixes. It's step 0 of the refactor plan: every later fix or refactor PR must run it, and its output must stay byte-identical unless the PR explicitly calls out the intended change with a reason.

## What it tests

For a fixed corpus of expressions, the harness records:

- **Exact-mode display text**: The result shown in exact mode (120–480 digit arithmetic)
- **Certification flags**: `certified`, `couldn't verify`, `singular:<type>`, `ln0`, `series-shortcut`
- **Float-mode display text**: The result shown in float mode
- **Float flags**: `differs-from-exact`, `underflowed`, `overflowed`, `near-cut`, `unverified`
- **Press/RPN count**: The button-press length of the compiled program
- **Pack/unpack round-trip**: Whether `packCircuit` → `unpackCircuit` preserves the exact result

The output is deterministic (no timings), sorted, and stored line-by-line for readable diffs.

## How to run it

### Check against golden output (CI mode)

```bash
npm run eml:golden
```

Compares the current output against the checked-in `lib/eml/golden/golden.txt`. Exits with code 0 if they match, code 1 with a readable diff if they differ.

### Regenerate golden output

```bash
npm run eml:golden -- --update
```

Evaluates the corpus and writes a new `lib/eml/golden/golden.txt`. Use this when you've made an intentional behavior change.

### Include heavy test cases

```bash
npm run eml:golden -- --heavy
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
2. Update `lib/eml/golden/harness.ts` to remove the bug from the `knownBugs` map
3. Run `npm run eml:golden -- --update` to regenerate without the annotation
4. Document the fix in your PR description

Current known bugs:

- **v1.1-complex-half**: `6.103e-120*i+6.103e-120*i` shows half the sum in exact mode (no flag)
- **A1-real-drop**: `(i*(1+10^(-124))-i)*i+i*10^10/3` drops its real part

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

2. Run `npm run eml:golden -- --update` to regenerate

3. Commit the corpus change and the updated golden output together

## Corpus

The corpus includes:

- **Basic**: `1+1`, `pi`, `e`, `i`, arithmetic
- **Cancellations**: `((1+10^(-k))-1)+i*c` and `(i*(1+10^(-k))-i)*i+i*c` for k ∈ {110,124,126,128,130,132,136} and c ∈ {1/2, 1/3, 3/2, -1/2, 10^10/3}
- **Transcendental edges**: `ln(1+10^-130)`, `tan(1e100)`, `cos(1e7)`, `sin(1e22)`, `sinh(1e-7)-1e-7`, etc.
- **Complex edges**: `6.103e-120*i+6.103e-120*i`, `0.00005*i+0.00005*i`
- **Infinities**: `ln(0)^2`, `(ln(0)*i)^3`
- **Poles**: `tan(pi/2)`, `1/0`, `ln(0)`
- **Precision**: `exp(1e-432)-1`, `tan(10^(-5000))`

Total: 152 expressions (standard corpus, < 2 minutes runtime)

## Cache consistency

The harness also checks COLD vs WARM cache consistency for a sample of expressions. This detects bugs like the v1.1 cache issue with `ln(1+10^-130)` (where loading the 671-press word could show exact 0 depending on cache state).

Known cache issues are logged but do not fail the harness (they're tracked separately for v1.1 fixes).

## CI integration

The golden harness runs in `.github/workflows/ci.yml` after `eml:check`:

```yaml
- run: npm run eml:golden
```

It does not run with `--heavy`, so heavy cases stay out of CI.
