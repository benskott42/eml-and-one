# Resume

Stopped before any M1–M3 code change. Head before this note was `c8d2a72`.

## Done

- Quarter-turn products, negation, squaring, and integer powers are on this branch.
- Regression rows for those cases run in float, exact, and the packed path.
- `docs/known-limitations.md` mentions `∞^0` and exponents written `3.0` or `6/2`.

## Left

- **M1.** `directionOf` and `positiveRealInfinity` still treat a real-infinity sign mark as a pure real ±∞. On this branch that mark allows a finite imaginary part, so `ln(ln(0))` and `ln(-inf)` collapse (for example `ln(ln(0))*i` becomes 0). Accept the mark only when the imaginary part is proven 0, or drop the fallback. Rows must not come out finite.
- **M2.** `tLn`, `tLogBase`, `tSqrt`, and `tDiv` still ignore an odd (imaginary) turn. `ln(ln(0)*i)`, `(inf*i)/2`, `(ln(0)*i)/2`, `(inf*i)/(1+i)`, and `sqrt(ln(0)*i)` are confident and wrong. Carry the turn, or mark those results unverified.
- **M3.** Add the M1 and M2 rows to `check.ts` in exact, float, and packed form. Pin `inf^0`, `(-inf)^0`, `(-inf)^3.0`, and `(-inf)^(6/2)` as unverified.
- **Docs.** The screen says "couldn't verify". The known-limitations line should say that, and that it applies to an infinite base. After M2, list the ln, sqrt, and division gaps if they stay unverified.
