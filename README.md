# EML and One

a two-button calculator

Two keys. The 1 key is the bit 0. The EML key is the bit 1. Every other key is a shortcut that presses those two. A program is a circuit of the operator

```
eml(x, y) = exp(x) − ln(y)
```

with the constant 1. EML is the operator introduced in arXiv:2603.21852, [https://arxiv.org/abs/2603.21852](https://arxiv.org/abs/2603.21852). An expression such as `3+4` or `2^3-1` compiles into presses of those two keys. The screen shows the sequence and its length.

Exact mode is the default. It evaluates the circuit you see with 120-digit decimal arithmetic, raised up to 480 digits when a cancellation would otherwise hide a value. Within one working precision, a residual smaller than about 10^(−(digits−8)) relative to its operands is treated as 0. That is not a fixed snap at 10^(−112), and it is not symbolic mathematics or an interval proof. When the spelling stores the exponent, as in 1e-432, a known magnitude of 10^(−432) still resolves. 1e-433 shows 1×10^(−433), and so do (1+1e-433)−1 and ln(1+1e-433). A power such as 10^(−400) records its decade when that still fits in 480 digits, and division carries that decade, so ln(1+10^(−400)) and 0−10^(−400) keep the small term. 0−1/10^400 and 0−10^(−500) say they could not verify. ln(1+exp(−1000)) shows the value. A logarithm the circuit collapses, such as ln(1−10^(−500)) or ln(1−exp(−1000)), says it could not verify instead of a confident 0. A product of an exact 0 and a finite factor is not always certified: 0*10^(−500), 0*exp(−1000), and (1−1)*sin(1) say they could not verify. A pasted literal can run to 4,000 digits. Those digits are the value, so a rounded float is not folded in, and sqrt of a pasted 1.000…1 minus 1 is not certified as 0. Arithmetic on a pasted literal that needs more than 480 digits says it could not verify. See [docs/known-limitations.md](docs/known-limitations.md). Float mode is a hardware view of the same gates. When the two disagree beyond what float can claim, the float stays on screen and the exact value is shown beside it.

## Branch

Inside eml, the log of a negative real, including both signs of zero, uses argument −π. The composed logarithm is the principal logarithm, so its imaginary part lies in (−π, π].

`rotSub(a, b)` is the construction used for variable subtraction, and the same scale is used for addition. It needs ln 0 = −∞. Infinities in the rest of that argument carry no phase: exp(+∞ + iθ) = +∞. That phase-free model is not enough when b = 0. sub(5, 0) and add(5, 0) are NaN unless the infinity from ln 0 keeps a direction, so b = 0 needs directed infinities. The argument uses the unwinding number of Corless and Jeffrey, “The unwinding number”, ACM SIGSAM Bulletin 30(2):28–35, 1996, [doi:10.1145/235699.235705](https://doi.org/10.1145/235699.235705). The proof, including that exception, is in [docs/rotsub.md](docs/rotsub.md).

The log-as-floor device is due to Cappallo, arXiv:2609.10592, [https://arxiv.org/abs/2609.10592](https://arxiv.org/abs/2609.10592). What this project claims is the construction of subtraction for b ≠ 0, not that device. b = 0 needs a directed infinity.

## Records

K is the RPN length: one token for each leaf and each eml. Every record below is on the lower cut, Arg in [−π, π), with ln 0 = −∞. On this cut −iπ becomes +iπ under the principal Log. 0, −1, and 2 are proven minimal, as summarized in [docs/minimality.md](docs/minimality.md). Everything else below is shortest known. A record that uses ln 0 = −∞ says so. No record here depends on Schanuel's conjecture.

These lengths were already public. They are not claimed as first discoveries. The search in this project also finds them, under the ln 0 policy named with each one.

- ±iπ at K 21 was posted on Hacker News before this project. On this cut the K 21 word is +iπ. Under the principal log it is −iπ. With ln 0 = −∞ that word is shortest known at K 21, and without ln 0, +iπ on this cut is shortest known at K 23. Unresolved tower trees remain, so neither length is proven minimal.
- 3 at K 29 ties Kaseorg's code-golf answer.
- 0 at K 7, −1 at K 15 and K 17, and 2 at K 19 tie the paper. They are proven minimal on the lower cut, Arg in [−π, π), towers included, with ln 0 = −∞. On this cut −iπ becomes +iπ under the principal Log. The proof is computer-assisted: [docs/minimality.md](docs/minimality.md). 0 at K 7 excludes every program with K ≤ 5. −1 at K 15 is proven minimal and uses ln 0. Without ln 0, −1 is proven minimal at K 17. 2 at K 19 excludes every one of the 2056 programs with K ≤ 17.

Ours, labelled as above:

| value | K | status |
| --- | --- | --- |
| −2 | 25 | shortest known, with ln 0 = −∞. Unresolved tower trees remain. Without that value, K 27 is shortest known. |
| −1/2 | 29 | shortest known, with ln 0 = −∞ |
| ±1/2 | 31 | shortest known, without ln 0 |
| −iπ on the lower cut | 45 | shortest known, not proven minimal, lower cut, Arg in [−π, π), with ln 0 = −∞. Not the K 21 word. Under the principal Log this value is +iπ. |
| −iπ on the lower cut | 55 | shortest known, not proven minimal, without ln 0. The word lies on the negative axis and comes out as +iπ under the principal Log at some precisions. |
| 4 | 39 | shortest known, not proven minimal |
| 2/3 | 39 | shortest known, not proven minimal |
| −1/3 | 41 | shortest known, not proven minimal |
| −3 | 35 | shortest known, not proven minimal |
| 1/3 | 35 | shortest known, not proven minimal, with ln 0 = −∞ |
| 1/3 | 37 | shortest known, not proven minimal, without ln 0 |
| scaled subtraction | 565 | shortest known construction, with ln 0 = −∞ |
| scaled addition | 655 | shortest known construction, with ln 0 = −∞ |

The words are in [lib/eml/best-known.json](lib/eml/best-known.json): −iπ at K 45 is `-ipi`, −iπ without ln 0 at K 55 is `-ipi-strict`, and 1/3 at K 37 is `1/3-strict`. K 21 and K 23 are +iπ on this cut. i at K 57, π at K 93, √2 at K 61, and ln 2 at K 25 are constructions, not search records.

## Encoding

The ranking of programs is the classical ranking of binary trees and prefix codes: Łukasiewicz, Ruskey and Hu, and Zaks. The contribution here is applying that ranking to EML programs. Within one length, 1 comes before E. Bits are written E = 1 and the 1 key = 0, so a higher program number is a higher binary value. A program ID is those bits with a 1 in front, so 11E is 001 and its ID is 1001 = 9.

## Prior art

[pmocz/two_button_calculator](https://github.com/pmocz/two_button_calculator) and [LeaderOnePro](https://eml-calculator.vercel.app/) are earlier two-button calculators. This project drew on those ideas only. None of their code was used.

John Haas's [eml-calculator](https://github.com/j0hnhaas/eml-calculator) (MIT; [demo](https://j0hnhaas.github.io/eml-calculator/)) is the source of the typed-expression playback: an ordinary sum compiled into presses of 1 and EML, with the short recipes used only where they were checked. None of that source was copied. The recipes are the words in [lib/eml/best-known.json](lib/eml/best-known.json). His multiply word is the same string as ours (`1111xEE1EEyE1EE1E`). His add word is that string with the two operands exchanged (`1111x1EEE1EEy1EE1EE` there, `1111y1EEE1EEx1EE1EE` here). Both of our words were already in best-known.json in commit 91f4360 (2026-11-15, message “EML and One v1.0.0”), found independently of his source. The domains in [lib/eml/exprSeq.ts](lib/eml/exprSeq.ts) are what this project's exact engine accepts on the lower bank. A nonzero integer sum or difference with both operands in −8…8 uses the short word, and each such pair was certified. An add or a sub whose value is exactly 0 is the certified 7-press 0 word: a printed 0 is not certified for every spelling.

## References

The algebraic structure, and the raw subtraction word, are from Stachowiak, arXiv:2604.23893. rotSub, the subtraction this calculator uses away from that word's strip, is a construction of this project.

Carney, arXiv:2605.01636, is cited here only for the fact that every EML value is computable.

An independent K 19 tree for 2 is due to Lopez Montoya, Zenodo record 21469737.

## Known limitations

Unfinished work is listed in [docs/known-limitations.md](docs/known-limitations.md). It does not block this version.

Float is a hardware view. Each component is compared with the exact value at the 12 digits on screen, and a dropped component is flagged. The exact reference raises its precision, up to 480 digits, when a cancellation would otherwise become 0. When the spelling stores the exponent, a known magnitude of 10^(−432) still resolves. 10^(−433) in that spelling shows 1×10^(−433). A series shortcut keeps the leading term only when the next term is past that cap: |x| ≤ 10^(−241) for sin, tan, tanh, arctan, and cos(x)−1, and |x| ≤ 10^(−480) for ln(1+x), exp(x)−1, and sqrt(1+x)−1. Sin keeps odd powers for |x| ≤ 10^(−61). tan, tanh, and arctan keep odd powers, and cos(x)−1 keeps even powers, for |x| ≤ 10^(−20), until the next term is past the cap. A one-digit literal such as tan(1e-5000) or exp(1e-1000)−1 prints that value. The power spellings tan(10^(−5000)) and exp(10^(−1000))−1 resolve, to 1×10^(−5000) and 1×10^(−1000). A pasted literal stops at 4,000 digits. Past 480 digits of working precision the exact screen says it could not verify, and a pasted decimal is not folded as its rounded float. A zero from a series shortcut is not certified. These float results are still wrong, and the flag says so: a variable just off the branch cut, a dropped real or imaginary part, tan of a large real such as 50000, exp(10^(−6)) − 1, and cos(10^(−200)) − 1. arccos(2) is +i·arcosh(2). arctan(−2i) is −π/2 − (artanh 2)i on this cut, in both modes, matching mpmath. A relative error at or below about 5×10^(−12), a signed zero at the smallest positive float, and a cancellation with no known leaf at that scale are not flagged. artanh of a real greater than 1 is ½ ln|(1+x)/(1−x)| − iπ/2, matching mpmath atanh. C99 catanh of that real with a +0 imaginary part returns +iπ/2.

## License

The code is under the MIT license in [LICENSE](LICENSE). The font file `public/fonts/VT323-Regular.ttf` is VT323, copyright 2011, The VT323 Project Authors (peter.hull@oikoi.com). It is bundled under the SIL Open Font License, Version 1.1, not under the MIT license. The MIT license does not apply to that font. The full OFL 1.1 text is in `public/fonts/VT323-OFL.txt`.

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
