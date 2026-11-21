# Offline check of the counting words

`scripts/count_mpmath.py` evaluates every integer-table word, and every integer program in `lib/eml/best-known.json` that the table does not already contain, at 130 decimal digits. Each word is run on the lower cut and under the principal Log. `ln 0` is −∞ on both. A word passes when it is within 10^(−110) of its integer and, for a table word, uses `ln 0` only as the table says.

The script is not part of CI. The CI image does not install Python. From a checkout with `mpmath`:

```bash
python3 scripts/count_mpmath.py
```
