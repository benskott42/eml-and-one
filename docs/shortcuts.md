# Shortcuts and exact recognitions

Every calculator key normally builds its value from `1` and `eml(x, y) = exp(x) − ln(y)`. Two kinds of shortcuts exist in `lib/eml/library.ts`, and both are disclosed in the note under the calculator screen:

1. **Series shortcuts** (`series shortcut: ...`): for tiny arguments where the full circuit would lose digits below 480-digit working precision, a truncated Taylor or asymptotic series is used. Because a tail term is dropped, exact mode refuses any later cancellation that would make the result 0 or expose the dropped error term.
2. **Exact recognitions** (`recognized exactly`): for a small, closed set of identities whose result is mathematically exact, the library returns a short program (`0`, `−0`, `1`, `−1`, `1/2`, `−1/2`, `i`, `−i`, `π`, `±π/2`, `±iπ/2`) in place of the full function circuit. Because the short program has a smaller `K` than the full circuit, the result node is marked with `Facts.recognized = true` and the screen note shows **`recognized exactly`**.

## Exact recognitions

Every exact recognition in `lib/eml/library.ts` is listed below, along with why it is exact and what guard prevents false matches on approximate floats:

| Recognition | Where | Returned program | Why it is exact & guard |
|---|---|---|---|
| `x^0 = 1`, `x^(−0) = 1` | `tPow` | `1` (fresh `ONE` node) | IEEE `pow(x, ±0) = 1` for every proven-finite `x` (including `0^0 = 1`); infinite or unverified bases keep the power circuit. |
| `0·a` when `a` is a certified real | `tMul` | `0` or `−0` | IEEE `sign(0·a) = sign(a)`. A factor whose sign is not certified stays unverified, proven finite or not (`(−π)^3·0`, `0·(−(exp(0.5)^2))`, `(exp(0.5))^2·((−0.5)·0)`). A signed zero times a non-real factor stays unverified, so `(0·cos(2))·i` and `i·(0·cos(2))` are the same refusal and `((−2/3)·0)·(−1+i)` is unverified. `+0·(±i)` stays `+0`. `cos` of a certified zero is `1`. |
| `(±i)^n` | `tPow` → `unitPower` | `1`, `i`, `−1`, `−i` | Exact 4-periodic cycle for a node with recorded `imaginaryUnit` (`±i`) and a proven integer exponent `n`. |
| `exp(i·kπ/2) = i^k` | `tExp` → `unitPower` | `1`, `i`, `−1`, `−i` | Euler's formula on recorded imaginary angle multiples `k·(π/2)·i` (not floats near `π/2`). |
| Odd functions at `0` or `−0` (`sin`, `tan`, `sinh`, `tanh`, `arcsin`, `arctan`, `arsinh`, `artanh`) | `oddAtZero` (and `tArsinh` zero check) | `0` or `−0` (fresh leaf) | Every listed function is odd and satisfies `f(±0) = ±0` (IEEE sign preservation); only proven integer `0` or the `−0` leaf match, never a float that underflowed to `0`. |
| `sin` and `cos` at multiples of `π/6` with rational values (`0`, `±1/2`, `±1`) | `sinAtPiMultiple` (from `tSin`, `tCos`) | `0`, `1`, `−1`, `1/2`, `−1/2` | Exact trigonometric values on recorded `q·π` angles (`factsOf(t).angle`); irrational values (`±√3/2`) and perturbed angles (`π + 10^(−30)`) keep their circuits. |
| `tan` at `kπ`, `π/4 + kπ`, `3π/4 + kπ` | `tTan` | `0`, `1`, `−1` | Exact tangent values on recorded `q·π` angles; odd multiples of `π/2` keep the pole path. |
| `arcsin(±1) = ±π/2` | `tArcsin` | `±π/2` | Exact endpoints of the principal `arcsin` branch for known exact `±1`. |
| `arccos(1) = 0`, `arccos(−1) = π` | `tArccos` | `0`, `π` | Exact endpoints of the principal `arccos` branch for known exact `±1` (values near `±1` such as `1 + 10^(−16)` use `arccosNearOne`). |
| `arsinh(±i) = ±i·π/2` | `tArsinh` | `±i·π/2` | Exact branch endpoints for recorded `imaginaryUnit` (`±i`). |

## Adding a new recognition

Any new exact recognition in `lib/eml/library.ts` must:
1. Wrap its returned node in `recognized(...)` so `Facts.recognized` is set without mutating shared `ONE` or interned `input` leaves.
2. Be documented in the table above.
3. Be covered in the recognition check in `lib/eml/check.ts` (block 99).
