# n=10 diff: mathbot (emlcore + 6 merges) vs buggybot (el_expr), 2026-11-21 ~08:55 AM ET. Draft, pending review.

Method: ran a copy of buggybot's enumerator (/tmp/bb, unmodified code) to dump its 5060 final classes with example words;
evaluated every example word in emlcore (principal cut) with the six K19 merges applied (map.py).
Result: every buggybot class maps into exactly one emlcore class; the 5060 classes cover all 5059 emlcore classes;
exactly ONE emlcore class is hit by two buggybot classes:

  Y = 1111E11EE1EE11EEE   (n=9, ln0-free)      buggybot normal form: e - log(-1 + exp(1 + e - e^e))
  X = 11E111E11E1EE1E1EEE (n=10, ln0-free)     buggybot normal form: e^e - log(e - exp(e^e - e))
  emlcore canonical form for both (no extra merge needed): -i*pi + e - Log(1 - exp(1 + e - e^e))   [lower cut: +i*pi]

Proof (principal cut). Put t = e^e - e > 0 (t ~ 12.44), so 0 < e^{1-t} < 1.
  e - e^t < 0 is real, so log(e - e^t) = log(e^t - e) + i*pi = t + log(1 - e^{1-t}) + i*pi  (e^t, 1 - e^{1-t} > 0).
  Hence X = e^e - t - log(1 - e^{1-t}) - i*pi = e - log(1 - e^{1-t}) - i*pi.
  -1 + e^{1-t} < 0 is real, so log(-1 + e^{1-t}) = log(1 - e^{1-t}) + i*pi, and Y = e - log(1 - e^{1-t}) - i*pi = X.
  Lower cut: both get +i*pi (conjugates). mpmath at 100 dps: |X - Y| = 0.
So buggybot's normalizer misses log(negative real) = log(|.|) + i*pi followed by factoring exp(t) out of e^t - e.
buggybot's X class is spurious: correct counts are a=5059, b=3511, a0=5048, b0=3504 (c=3596, c0=3579 unchanged, since
X is reachable at exactly 10 either way). This is a bijection check against buggybot only; it is not a proof that no
further identities exist (collision conjecture caveat unchanged).
