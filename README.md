# EML and One

a two-button calculator

Two keys. The 1 key is the bit 1. The EML key is the bit 0. Every other key is a shortcut that presses those two. A program is a circuit of the operator

```
eml(x, y) = exp(x) − ln(y)
```

with the constant 1. EML is the operator introduced in arXiv:2603.21852, [https://arxiv.org/abs/2603.21852](https://arxiv.org/abs/2603.21852).

Exact mode is the default. It evaluates the circuit you see with 120-digit decimal arithmetic, raised up to 480 digits when a cancellation would otherwise hide a value. Within one working precision, a residual smaller than about 10^(−(digits−8)) relative to its operands is treated as 0. That is not a fixed snap at 10^(−112), and it is not symbolic mathematics or an interval proof. A literal that spells its exponent, such as 1e-433 or 1e-5000, is exact at any size, and (1e-433+1)−1 still recovers 10^(−433). A sum such as 1e-432+1, which is 1 to every digit shown, says it could not verify. A power such as 10^(−400) records its decade when that still fits in 480 digits, and division carries that decade, so ln(1+10^(−400)), 0−10^(−400), and 0−1/10^400 keep the small term. Past that cap, 0−10^(−500) is negation and still prints the value. A logarithm the circuit collapses, such as ln(1−10^(−500)) or ln(1±exp(−1000)), says it could not verify instead of a confident 0. An exact 0 times a finite factor stays a certified 0. See [docs/known-limitations.md](docs/known-limitations.md). Float mode is a hardware view of the same gates. When the two disagree beyond what float can claim, the float stays on screen and the exact value is shown beside it.

## Branch

Inside eml, the log of a negative real, including both signs of zero, uses argument −π. The composed logarithm is the principal logarithm, so its imaginary part lies in (−π, π].

`rotSub(a, b)` is the construction used for variable subtraction, and the same scale is used for addition. It needs ln 0 = −∞. Infinities in the rest of that argument carry no phase: exp(+∞ + iθ) = +∞. That phase-free model is not enough when b = 0. sub(5, 0) and add(5, 0) are NaN unless the infinity from ln 0 keeps a direction, so b = 0 needs directed infinities. The argument uses the unwinding number of Corless and Jeffrey, “The unwinding number”, ACM SIGSAM Bulletin 30(2):28–35, 1996, [doi:10.1145/235699.235705](https://doi.org/10.1145/235699.235705). The proof, including that exception, is in [docs/rotsub.md](docs/rotsub.md).

The log-as-floor device is due to Cappallo, arXiv:2609.10592, [https://arxiv.org/abs/2609.10592](https://arxiv.org/abs/2609.10592). What this project claims is the construction of subtraction for b ≠ 0, not that device. b = 0 needs a directed infinity.

## Records

K is the RPN length: one token for each leaf and each eml. Every record below is on the lower cut, Arg in [−π, π), with ln 0 = −∞. On this cut −iπ becomes +iπ under the principal Log. 0, −1, 2, +iπ on this cut, and −2 are proved minimal, as summarized in [docs/minimality.md](docs/minimality.md). Everything else below is shortest known. A record that uses ln 0 = −∞ says so. No record here depends on Schanuel's conjecture.

These lengths were already public. They are not claimed as first discoveries. The search in this project also finds them, under the ln 0 policy named with each one.

- ±iπ at K 21 was posted on Hacker News before this project. On this cut the K 21 word is +iπ. Under the principal log it is −iπ. With ln 0 = −∞ that word is proved minimal at K 21: `python tools/minimality/decide.py --open` excludes all 6918 programs with K ≤ 19 (2026-11-22). Without ln 0, +iπ on this cut is proved minimal at K 23: the only K 21 programs that are not excluded take ln 0 (2026-11-24, with [tools/minimality/towers.py](tools/minimality/towers.py) for 16 tower programs).
- 3 at K 29 ties Kaseorg's code-golf answer.
- 0 at K 7, −1 at K 15 and K 17, and 2 at K 19 tie the paper. They are proved minimal on the lower cut, Arg in [−π, π), towers included, with ln 0 = −∞. On this cut −iπ becomes +iπ under the principal Log. The proof is computer-assisted: [docs/minimality.md](docs/minimality.md). 0 at K 7 excludes every program with K ≤ 5. −1 at K 15 is proved minimal and uses ln 0. Without ln 0, −1 is proved minimal at K 17. 2 at K 19 excludes every one of the 2056 programs with K ≤ 17.

Ours, labelled as above:

| value | K | status |
| --- | --- | --- |
| −2 | 25 | proved minimal, with ln 0 = −∞ ([docs/minimality.md](docs/minimality.md); the tower programs take runs of up to 5.5 million bits). Without that value, K 27 is shortest known: all but two K 25 programs are excluded. |
| −1/2 | 29 | shortest known, with ln 0 = −∞ |
| ±1/2 | 31 | shortest known, without ln 0 |
| −iπ on the lower cut | 45 | shortest known, not proven minimal, lower cut, Arg in [−π, π), with ln 0 = −∞. Not the K 21 word. Under the principal Log this value is +iπ. |
| −iπ on the lower cut | 47 | shortest known, not proven minimal, without ln 0. Found by inverting the last gate against every value with K ≤ 35 (2026-11-22); it replaces K 55. |
| 4 | 39 | shortest known, not proven minimal |
| 2/3 | 39 | shortest known, not proven minimal |
| −1/3 | 41 | shortest known, not proven minimal |
| −3 | 35 | shortest known, not proven minimal |
| 1/3 | 35 | shortest known, not proven minimal, with ln 0 = −∞ |
| 1/3 | 37 | shortest known, not proven minimal, without ln 0 |
| scaled subtraction | 565 | shortest known construction, with ln 0 = −∞ |
| scaled addition | 655 | shortest known construction, with ln 0 = −∞ |

The words are in [lib/eml/best-known.json](lib/eml/best-known.json): −iπ at K 45 is `-ipi`, −iπ without ln 0 at K 47 is `-ipi-strict`, and 1/3 at K 37 is `1/3-strict`. K 21 and K 23 are +iπ on this cut. i at K 57, π at K 93, √2 at K 61, and ln 2 at K 25 are constructions, not search records.

## Encoding

The ranking of programs is the classical ranking of binary trees and prefix codes: Łukasiewicz, Ruskey and Hu, and Zaks. The contribution here is applying that ranking to EML programs. Within one length, 1 comes before E, so a higher program number is a lower binary value. The program loader also accepts `0x…` hex and `0b…` binary strings directly (applying Raney's Cycle Lemma rotation when needed); see [docs/binary.md](docs/binary.md).

## Interactive tools & formal proofs

- **Tree, Dyck path & step player** (`components/calculator/CircuitInspector.tsx`): step-by-step 2-button RPN stack replay (`Start`, `Prev`, `Play/Pause`, `Next`, `End`, scrubber), synchronized inline SVG binary tree (`K ≤ 63`), Dyck-path stack-height chart (`K ≤ 201`), live deductive algebraic proofs (`lib/eml/proof.ts`), and one-click export to `eml(x, y)`, LaTeX, and Lean 4 term syntax (`lib/eml/export.ts`).
- **Complex-plane map & live minimality certifier** (`components/calculator/ComplexMap.tsx`, `lib/eml/certificate.ts`): interactive SVG plot of all distinct finite constant EML circuits for `K ≤ 11` (65 trees) and `K ≤ 13` (197 trees) — click any point to load it — plus an in-browser directed-rounding minimality certifier over Catalan trees.
- **Circuit golf & target finder** (`components/calculator/widgets.tsx`, `lib/eml/golf.ts`): Web Worker constant search up to `K = 21` with clickable load chips, plus a reverse-EML target finder that locates the 5 closest finite circuits (`K ≤ 19`) to any real, complex, or fractional target.
- **Machine-checked Lean 4 + Mathlib formalization** ([formal/lean/README.md](formal/lean/README.md)): zero-`sorry` (`warningAsError := true`), zero-custom-axiom Lean 4.28 + Mathlib proofs over `ℂ` on the lower branch cut (`Arg ∈ [−π, π)`), covering **17 modules** with **all `Eml.*` declarations automatically axiom-audited** and **CI-verified UI theorem links + proof-carrying certificates**: core EML identities & Corless–Jeffrey unwinding (`Eml.Basic`), genuine `eml`-word arithmetic (`Eml.Arithmetic`), rotated and scaled subtraction including the phase-free `b = 0` failure vs. directed-infinity + signed-zero `b = 0` proof (`Eml.RotSub`, `Eml.Extended`, `Eml.DirectedInf`), **all 28 concrete RPN constant records** from `best-known.json` (`1`, `e`, `0`, `−1`, `2`, `+iπ`, `−iπ` K 45 & K 47, `ln 2`, `3`, `−3`, `4`, `2/3`, `−1/3`, `1/2`, `−1/2`, `1/3`, `√2`, `−∞`, `−2`, `i`, `π`, etc.), genuine `eml`-word `cos`/`sin`/`tan`/`cosh`/`sinh`/`tanh`/`σ`/`pow`/`sqrt`/`logBase` (`Eml.Transcendental`) and inverse trig/hyperbolic branch cuts (`Eml.InverseTrig`: `artanh` for `|x| > 1`, `arctan` on `|Im| > 1`, `arcsin`/`arccos` on `x > 1`), the full `EmlTree ≃ IsValidProgram` bijection, Raney's Cycle Lemma & Catalan counting (`Eml.Binary`, `Eml.TreeBijection`, `Eml.CycleLemma`, `Eml.RpnSoundness`), unconditional minimality of `0` at K = 7 (`Eml.MinimalityZero`), and a kernel-checked certificate evaluator with proved rectangle bounds (`Eml.Cert`, `Eml.CertBox`), built, audited, and cross-checked against the UI automatically in `.github/workflows/lean.yml`.

## Prior art

[pmocz/two_button_calculator](https://github.com/pmocz/two_button_calculator) and [LeaderOnePro](https://eml-calculator.vercel.app/) are earlier two-button calculators. This project drew on those ideas only. None of their code was used.

## References

The algebraic structure, and the raw subtraction word, are from Stachowiak, arXiv:2604.23893. rotSub, the subtraction this calculator uses away from that word's strip, is a construction of this project.

Carney, arXiv:2605.01636, is cited here only for the fact that every EML value is computable.

An independent K 19 tree for 2 is due to Lopez Montoya, Zenodo record 21469737.

## Known limitations

Unfinished work is listed in [docs/known-limitations.md](docs/known-limitations.md). It does not block this version.

Float is a hardware view. Each component is compared with the exact value at the 12 digits on screen, and a dropped component is flagged. The exact reference raises its precision, up to 480 digits, when a cancellation would otherwise become 0. When the spelling stores the exponent, a known magnitude of 10^(−432) still resolves. 10^(−433) in that spelling says it could not verify. A series shortcut keeps the leading term only when the next term is past that cap: |x| ≤ 10^(−241) for sin, tan, tanh, arctan, and cos(x)−1, and |x| ≤ 10^(−480) for ln(1+x), exp(x)−1, and sqrt(1+x)−1. Sin keeps odd powers for |x| ≤ 10^(−61). tan, tanh, and arctan keep odd powers, and cos(x)−1 keeps even powers, for |x| ≤ 10^(−20), until the next term is past the cap. A one-digit literal such as tan(1e-5000) or exp(1e-1000)−1 prints that value. The power spellings tan(10^(−5000)) and exp(10^(−1000))−1 do not resolve inside the cap, so they say could not verify rather than 0. A zero from a series shortcut is not certified. These float results are still wrong, and the flag says so: a variable just off the branch cut, a dropped real or imaginary part, tan of a large real such as 50000, exp(10^(−6)) − 1, and cos(10^(−200)) − 1. arccos(2) is +i·arcosh(2). arctan(−2i) is −π/2 − (artanh 2)i on this cut, in both modes, matching mpmath. A relative error at or below about 5×10^(−12), a signed zero at the smallest positive float, and a cancellation with no known leaf at that scale are not flagged. artanh of a real greater than 1 is ½ ln|(1+x)/(1−x)| − iπ/2, matching mpmath atanh. C99 catanh of that real with a +0 imaginary part returns +iπ/2.

## License

The code is under the MIT license in [LICENSE](LICENSE). The font file `public/fonts/VT323-Regular.ttf` is VT323, copyright 2011, The VT323 Project Authors (peter.hull@oikoi.com). It is bundled under the SIL Open Font License, Version 1.1, not under the MIT license. The MIT license does not apply to that font. The full OFL 1.1 text is in `public/fonts/VT323-OFL.txt`.

## Develop

```bash
npm ci
npm run dev
npm run eml:check
npm run eml:smoke
```

`npm run eml:golf` is the K = 35 search, about 75 s on one core ([docs/golf-k35.md](docs/golf-k35.md)). It is not part of the publish check. [tools/emlsearch](tools/emlsearch) is a much faster independent search in Rust, with an mpmath checker. It reaches K 41 in about five minutes on 16 cores, and its results are in [docs/search-k41.md](docs/search-k41.md). `npm run build` writes a static site to `out/`.

`EML_SHARD=i/N npm run eml:check` runs shard i (from 0) of N. CI runs 6 shards in parallel. `EML_BLOCK_TIMES=1` prints each block's time. Copy those times into `lib/eml/check-shards.json` to rebalance the shards.

`npm run eml:golden` checks the recorded exact output. `GOLDEN_SHARD=i/N` checks every Nth row from row i; shard 0 also checks for rows that were removed. `npm run eml:golden -- --update` rewrites it. An update needs a PR note that explains every changed line. See [docs/golden.md](docs/golden.md).

## Publish

The workflow in `.github/workflows/pages.yml` typechecks, lints, runs the fast checks, and deploys `out/` to GitHub Pages. For a project site the workflow sets the base path from `actions/configure-pages`. Publishing means copying this directory to its own repository and enabling GitHub Pages from Actions. This tree does not create that repository.
