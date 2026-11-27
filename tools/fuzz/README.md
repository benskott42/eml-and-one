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
