# Engine Fuzzer (`tools/fuzz`)

Deterministic expression fuzzer for comparing EML exact-engine behavior in-process, across the worker wire (`packCircuit` → `unpackCircuit`), and against 2,500-digit `mpmath`.

## Quick start

Run 500 deterministic expressions (random trees, huge/tiny scales, cut-adjacent points, and poles/exact angles) in-process and through the worker wire:

```bash
npx tsx tools/fuzz/fuzz.ts --count 500 --seed 1
```

Save a JSON report to compare certified/unverified counts before and after an engine change, or to check every certified value against `mpmath`:

```bash
npx tsx tools/fuzz/fuzz.ts --count 1000 --seed 1 --json /tmp/fuzz.json
python3 tools/fuzz/oracle.py /tmp/fuzz.json
```

## Exit codes

- `fuzz.ts` exits with `1` if any expression disagrees between in-process evaluation and worker-wire evaluation.
- `oracle.py` exits with `1` if any certified finite value differs from 2,500-digit `mpmath` by more than `1e-10` relative error. It also checks each part on its own: a part certified as exact 0 is wrong when the true part is above the 480-digit cap (`1e-470` relative to the value), and a nonzero part must match to `1e-10` of itself. The whole-value test cannot see a dropped tiny part (`-5` against `-5 - 1e-236 i`).

## Input robustness (`parse-fuzz.ts`)

Random and mangled text into the expression field, the x and y fields, and the program field, through the same calls the calculator makes (`compileSubmission` + `entry`, `parseProgramInput` + `unrankProgram` / `nodeFromRpn`):

```bash
npx tsx tools/fuzz/parse-fuzz.ts --count 20000 --seed 1
```

Every input must work or fail with the calculator's own error (an `EmlError`, or a `RangeError` from the program field). Any other exception, which would reach the screen as an internal message, and any input slower than `--slow-ms` (default 4000) is a finding, and the run exits with `1`. `FUZZ_FULL=1` prints long inputs whole. It found that `x·x·…·x` with `x = 1e1000000` took 32 s to compile on the page's main thread (check 116).

