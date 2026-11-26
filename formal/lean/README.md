# Machine-Checked Lean 4 Formalization (`formal/lean/`)

This directory contains zero-`sorry` Lean 4 proofs of core **EML and One** theorems:

- [`Eml/Basic.lean`](Eml/Basic.lean) — Axiomatic `EmlModel` over any field with `exp`/`ln` and an explicit principal strip `inStrip` (no hidden branch-cut assumptions):
  - `cE_eq_exp_one`: `eml(1, 1) = exp(1)`
  - `cZero_eq_zero`: `eml(1, eml(eml(1, 1), 1)) = 0`
  - `emlExp_eq`: `eml(x, 1) = exp(x)`
  - `emlLn_eq`: `eml(1, eml(eml(1, x), 1)) = ln(x)` under `inStrip (exp 1 - ln x)`
  - `append0xc_eq`: `eml(x, eml(1, 1)) = exp(x) - 1`
  - `rawSub_eq`: `eml(ln a, exp b) = a - b` under `nonzero a` and `inStrip b`
- [`Eml/Binary.lean`](Eml/Binary.lean) — Pure inductive proofs (zero axioms) of the binary representation (`docs/binary.md`):
  - `valid_one`, `valid_e`, `valid_zero`
  - `valid_append_0xc`: appending `1100₂` (`0xc`) to any valid EML program yields a valid EML program
  - `valid_eml_combine`: `p ++ q ++ [false]` is valid whenever `p` and `q` are valid

## Building locally

With [elan](https://github.com/leanprover/elan) installed:

```bash
cd formal/lean
lake build
```
