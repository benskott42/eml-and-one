# Binary Representation of Constant EML Programs

Every constant EML program built from the two keys `1` and `EML` has an exact binary encoding:

- `1` key → bit **`1`**
- `EML` key → bit **`0`**

Reading the RPN press string as an unsigned binary integer turns every constant EML circuit into a positive integer.

## The Dyck-Prefix Binary Sequence

A `(2g + 1)`-bit integer `N` is a valid constant EML program of `g` gates without rotation if and only if:

1. Its bit length is odd (`2g + 1`),
2. Its popcount is `g + 1` (one more `1` than `0`), and
3. Every prefix has strictly more `1`s than `0`s (so the RPN stack height stays `≥ 1` and finishes at `1`).

For `g = 0, 1, 2, 3, ...`, the count of valid `(2g + 1)`-bit integers is the Catalan number $C_g$:

| Gates `g` | Length `K = 2g + 1` | Count $C_g$ | Valid binary integers (decimal) |
|---:|---:|---:|---|
| 0 | 1 | 1 | `1` |
| 1 | 3 | 1 | `6` (`0x6`) |
| 2 | 5 | 2 | `26`, `28` |
| 3 | 7 | 5 | `106`, `108`, `114`, `116`, `120` |

Within a fixed length `K = 2g + 1`, the Catalan program rank `#N` (`1 < E`) and the binary integer value (`1 > 0`) are **strictly anti-monotonic**: higher program number means lower binary value. `lib/eml/binary.ts` provides the exact bijection (`binaryToRank` / `rankToBinary`) and an $O(K)$ stepper (`nextBinaryProgram`).

## Cycle Lemma Orbits

There are $\binom{2g+1}{g+1} = (2g+1) C_g$ bitstrings of length `2g + 1` with `g + 1` ones. By Raney's Cycle Lemma, they partition into $C_g$ disjoint cyclic-shift orbits of size `2g + 1`, each containing **exactly one** valid EML program.

For example, `0x4e` (`1001110₂`) is not a valid program as written, but rotating left by 3 bits produces `1110100₂ = 0x74 = 116` (`0`). The calculator's program loader accepts `0x...` hex and `0b...` binary strings directly and applies this rotation automatically.

## Bit-Level Algebraic Patterns

- **The `0xc` (`1100₂ = 11EE`) nibble computes `exp(X) − 1`:**
  - `0x7d0` (`−∞`, K 11) + nibble `0xc` → `0x7d0c` (`−1`, K 15) = $\exp(-\infty) - 1$
  - `0x1fa1a8` (`+iπ`, K 21) + nibble `0xc` → `0x1fa1a8c` (`−2`, K 25) = $\exp(i\pi) - 1$
- **Integer increment pattern (`2, 3, 4`):**
  - `2` (K 19) = `0x7e264`
  - `3` (K 29) = `0x1fe26264`
  - `4` (K 39) = `0x7fe2626264`
  Each step inserts one `26` byte and shifts the leading `1`-run by 2 bits.

## Binary Atlas of `best-known.json` Constants

| Constant | `K` | Depth | Max stack | Hex (`0x…`) | Program `#` |
|---|---:|---:|---:|---|---:|
| `1` | 1 | 0 | 1 | `0x1` | `#0` |
| `e` | 3 | 1 | 2 | `0x6` | `#1` |
| `0` | 7 | 3 | 3 | `0x74` | `#5` |
| `−∞` | 11 | 5 | 5 | `0x7d0` | `#24` |
| `−1` | 15 | 6 | 5 | `0x7d0c` | `#242` |
| `2` | 19 | 8 | 6 | `0x7e264` | `#2431` |
| `+iπ` | 21 | 7 | 6 | `0x1fa1a8` | `#7948` |
| `−2` | 25 | 8 | 6 | `0x1fa1a8c` | `#98362` |
| `ln 2` | 25 | 11 | 8 | `0x1fe2644` | `#85587` |
| `3` | 29 | 12 | 8 | `0x1fe26264` | `#1086729` |
| `1/2` | 29 | 10 | 7 | `0x1df43522` | `#2246702` |
| `−1/2` | 29 | 10 | 7 | `0x1fd0c6a2` | `#1131653` |
| `−3` | 35 | 12 | 8 | `0x7f8991a8c` | `#52112013` |
| `1/3` | 35 | 12 | 8 | `0x77e863522` | `#108304485` |
| `4` | 39 | 16 | 10 | `0x7fe2626264` | `#664559518` |
| `2/3` | 39 | 14 | 9 | `0x77f1323522` | `#1473445293` |
| `−1/3` | 41 | 14 | 9 | `0x1dfc4c8d48c` | `#5474536393` |
| `−iπ` | 45 | 11 | 7 | `0x1f50fa1f50a8` | `#51983093531` |
| `i` | 57 | 15 | 9 | `0x1ff13213fa1a84a` | `#99292101684726` |
| `√2` | 61 | 16 | 10 | `0x1ff13213fe26444a` | `#1432982456885549` |
| `π` | 93 | 17 | 10 | `0x1ffa1a844ff89909fd0d4252` | `#3125315318547434611379164` |
