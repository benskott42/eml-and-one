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
- `oracle.py` exits with `1` if any certified finite value differs from 2,500-digit `mpmath` by more than `1e-10` relative error.
