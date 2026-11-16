# EML and One

a two-button calculator

Two keys. The 1 key is the bit 1. The EML key is the bit 0. Every other key is a shortcut that presses those two. A program is a circuit of the operator

```
eml(x, y) = exp(x) − ln(y)
```

with the constant 1. EML is the operator introduced in arXiv:2603.21852, [https://arxiv.org/abs/2603.21852](https://arxiv.org/abs/2603.21852).

Exact mode is the default. It evaluates the circuit you see with 120-digit decimal arithmetic, raised up to 480 digits when a cancellation would otherwise hide a value. Within one working precision, a residual smaller than about 10^(−(digits−8)) relative to its operands is treated as 0. That is not a fixed snap at 10^(−112), and it is not symbolic mathematics or an interval proof. A known magnitude of 10^(−432) still resolves. 10^(−433) is past the cap, and the screen says it could not verify. Float mode is a hardware view of the same gates. When the two disagree beyond what float can claim, the float stays on screen and the exact value is shown beside it.

## Branch

Inside eml, the log of a negative real, including both signs of zero, uses argument −π. The composed logarithm is the principal logarithm, so its imaginary part lies in (−π, π].

`rotSub(a, b)` is the construction used for variable subtraction, and the same scale is used for addition. It needs ln 0 = −∞. Infinities in the rest of that argument carry no phase: exp(+∞ + iθ) = +∞. That phase-free model is not enough when b = 0. sub(5, 0) and add(5, 0) are NaN unless the infinity from ln 0 keeps a direction, so b = 0 needs directed infinities. The argument uses the unwinding number of Corless and Jeffrey, “The unwinding number”, ACM SIGSAM Bulletin 30(2):28–35, 1996, [doi:10.1145/235699.235705](https://doi.org/10.1145/235699.235705). The proof, including that exception, is in [docs/rotsub.md](docs/rotsub.md).

The log-as-floor device is due to Cappallo, arXiv:2609.10592, [https://arxiv.org/abs/2609.10592](https://arxiv.org/abs/2609.10592). What this project claims is the construction of subtraction for b ≠ 0, not that device. b = 0 needs a directed infinity.

## Records

K is the RPN length: one token for each leaf and each eml. 0, −1, and 2 are proved minimal, as summarized in [docs/minimality.md](docs/minimality.md). Everything else below is shortest known. A record that uses ln 0 = −∞ says so. No record here depends on Schanuel's conjecture.

These lengths were already public. They are not claimed as first discoveries. The search in this project also finds them, under the ln 0 policy named with each one.

- ±iπ at K 21 was posted on Hacker News before this project. On this cut the K 21 word is +iπ. Under the principal log it is −iπ. With ln 0 = −∞ that word is shortest known at K 21, and without ln 0, +iπ on this cut is shortest known at K 23. Unresolved tower trees remain, so neither length is proven minimal.
- 3 at K 29 ties Kaseorg's code-golf answer.
- 0 at K 7, −1 at K 15 and K 17, and 2 at K 19 tie the paper. They are proved minimal on the lower cut, towers included. The proof is computer-assisted: [docs/minimality.md](docs/minimality.md). 0 at K 7 excludes every program with K ≤ 5. −1 at K 15 is proved minimal and uses ln 0. Without ln 0, −1 is proved minimal at K 17. 2 at K 19 excludes every one of the 2056 programs with K ≤ 17.

Ours, labelled as above:

| value | K | status |
| --- | --- | --- |
| −2 | 25 | shortest known, with ln 0 = −∞. Unresolved tower trees remain. Without that value, K 27 is shortest known. |
| −1/2 | 29 | shortest known, with ln 0 = −∞ |
| ±1/2 | 31 | shortest known, without ln 0 |
| −iπ on the lower cut | 45 | shortest known, not proven minimal, with ln 0 = −∞. Not the K 21 word. |
| 4 | 39 | shortest known, not proven minimal |
| 2/3 | 39 | shortest known, not proven minimal |
| −1/3 | 41 | shortest known, not proven minimal |
| −3 | 35 | shortest known, not proven minimal |
| 1/3 | 35 | shortest known, not proven minimal, with ln 0 = −∞ |
| 1/3 | 37 | shortest known, not proven minimal, without ln 0 |
| scaled subtraction | 565 | shortest known construction, with ln 0 = −∞ |
| scaled addition | 655 | shortest known construction, with ln 0 = −∞ |

The words are in [lib/eml/best-known.json](lib/eml/best-known.json): −iπ at K 45 is `-ipi`, and 1/3 at K 37 is `1/3-strict`. K 21 and K 23 are +iπ on this cut. i at K 57, π at K 93, √2 at K 61, and ln 2 at K 25 are constructions, not search records.

## Encoding

The ranking of programs is the classical ranking of binary trees and prefix codes: Łukasiewicz, Ruskey and Hu, and Zaks. The contribution here is applying that ranking to EML programs. Within one length, 1 comes before E, so a higher program number is a lower binary value.

## Prior art

[pmocz/two_button_calculator](https://github.com/pmocz/two_button_calculator) is prior art for a two-button calculator. This project uses the idea only. It does not use that code.

## Known limitations

Unfinished work is listed in [docs/known-limitations.md](docs/known-limitations.md). It does not block this version.

Float is a hardware view. Each component is compared with the exact value at the 12 digits on screen, and a dropped component is flagged. The exact reference raises its precision, up to 480 digits, when a cancellation would otherwise become 0. A known magnitude of 10^(−432) still resolves. 10^(−433) says it could not verify. A series shortcut keeps the leading term only when the next term is past that cap: |x| ≤ 10^(−241) for sin, tan, tanh, arctan, and cos(x)−1, and |x| ≤ 10^(−480) for ln(1+x), exp(x)−1, and sqrt(1+x)−1. Sin keeps odd powers for |x| ≤ 10^(−61). tan, tanh, and arctan keep odd powers, and cos(x)−1 keeps even powers, for |x| ≤ 10^(−20), until the next term is past the cap. A one-digit literal such as tan(1e-5000) or exp(1e-1000)−1 prints that value. The power spellings tan(10^(−5000)) and exp(10^(−1000))−1 do not resolve inside the cap, so they say could not verify rather than 0. A zero from a series shortcut is not certified. These float results are still wrong, and the flag says so: a variable just off the branch cut, a dropped real or imaginary part, tan of a large real such as 50000, exp(10^(−6)) − 1, and cos(10^(−200)) − 1. arccos(2) is +i·arcosh(2). arctan(−2i) is −π/2 − (artanh 2)i on this cut, in both modes, matching mpmath. A relative error at or below about 5×10^(−12), a signed zero at the smallest positive float, and a cancellation with no known leaf at that scale are not flagged. artanh of a real greater than 1 is ½ ln|(1+x)/(1−x)| − iπ/2, matching mpmath atanh. C99 catanh of that real with a +0 imaginary part returns +iπ/2.

## Develop

```bash
npm ci
npm run dev
npm run eml:check
npm run eml:smoke
```

`npm run eml:golf` is the slow K = 35 search. It is not part of the publish check. `npm run build` writes a static site to `out/`.

## Publish

The workflow in `.github/workflows/pages.yml` typechecks, lints, runs the fast checks, and deploys `out/` to GitHub Pages. For a project site the workflow sets the base path from `actions/configure-pages`. Publishing means copying this directory to its own repository and enabling GitHub Pages from Actions. This tree does not create that repository.
