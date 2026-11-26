# Machine-Checked Lean 4 Formalization (`formal/lean/`)

This directory contains zero-`sorry` Lean 4 proofs of core **EML and One** theorems:

- [`Eml/Basic.lean`](Eml/Basic.lean) — Axiomatic `EmlModel` over any field with `exp`/`ln` and an explicit principal strip `inStrip` (no hidden branch-cut assumptions):
  - `cE_eq_exp_one`: `eml(1, 1) = exp(1)`
  - `cZero_eq_zero`: `eml(1, eml(eml(1, 1), 1)) = 0`
  - `emlExp_eq`: `eml(x, 1) = exp(x)`
  - `emlLn_eq`: `eml(1, eml(eml(1, x), 1)) = ln(x)` under `inStrip (exp 1 - ln x)`
  - `append0xc_eq`: `eml(x, eml(1, 1)) = exp(x) - 1`
  - `rawSub_eq`: `eml(ln a, exp b) = a - b` under `nonzero a` and `inStrip b`
- [`Eml/Arithmetic.lean`](Eml/Arithmetic.lean) — Elementary arithmetic constructed from `eml` and `1` under explicit `nonzero` and `inStrip` hypotheses:
  - `emlMul_eq`: `exp(ln a + ln b) = a * b`
  - `emlDiv_eq`: `exp(ln a − ln b) = a / b`
  - `emlInv_eq`: `exp(−ln x) = x⁻¹`
  - `emlAdd_eq`: `eml(ln a, exp(−b)) = a + b`
- [`Eml/Binary.lean`](Eml/Binary.lean) — Pure inductive proofs (zero axioms) of the binary representation (`docs/binary.md`):
  - `valid_one`, `valid_e`, `valid_zero`
  - `valid_append_0xc`: appending `1100₂` (`0xc`) to any valid EML program yields a valid EML program
  - `valid_eml_combine`: `p ++ q ++ [false]` is valid whenever `p` and `q` are valid
  - `valid_program_starts_true`: every valid program starts with `1`
  - `valid_program_odd_length`: every valid program has `ones = zeros + 1` and odd length `2 * zeros + 1`
  - `evalRpn_append_0xc`: formal RPN stack semantics bridge proving `p ++ 0xc` evaluates to `op v (op one one)`
- [`Eml/RotSub.lean`](Eml/RotSub.lean) — Formal proof of rotated subtraction (`docs/rotsub.md`):
  - `rotSub_cancels_unwinding`: `rotSub(a, b) = a − b` for any unwinding offset `unwind b`
- [`Eml/RpnSoundness.lean`](Eml/RpnSoundness.lean) — End-to-end soundness bridge between binary Dyck-prefix programs and RPN evaluation:
  - `evalRpn_some_of_runDepth`: `runDepth xs st.length = some r` implies `evalRpn` succeeds with stack length `r`
  - `valid_program_evals_singleton`: every valid binary EML program never underflows and returns a singleton `[v]`
  - `evalRpn_0x1`, `evalRpn_0x6`, `evalRpn_0x74`: concrete RPN stack proofs for `1`, `e`, and `0`
  - `evalRpn_append_0xc_value`: appending `0xc` (`1100₂`) to any program evaluating to `v` evaluates to `exp(v) − 1`
- [`Eml/Transcendental.lean`](Eml/Transcendental.lean) — Transcendental constructions from `eml` and `1`:
  - `emlCos_eq`, `emlSin_eq`, `emlCosh_eq`, `emlSinh_eq`, `emlPow_eq`, `emlSqrt_eq`, `emlLogBase_eq`

## Continuous verification

Every push or pull request touching `formal/lean/` is machine-checked by `.github/workflows/lean.yml` (`lake build` on Lean 4.14).

## Building locally

With [elan](https://github.com/leanprover/elan) installed:

```bash
cd formal/lean
lake build
```
