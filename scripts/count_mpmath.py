# Offline 130-digit check of the counting words. Not part of CI: the CI image has no Python.
# Words come from the checked-in integer table and from best-known.json. Hub paths are not in this checkout.
import json
import os
import sys

import mpmath as mp

mp.mp.dps = 130


def ln(z, lower):
    if z == 0:
        return mp.mpf("-inf")
    value = mp.log(z)
    if lower and mp.im(z) == 0 and mp.re(z) < 0:
        value = mp.mpc(mp.re(value), -mp.pi)
    return value


def ev(word, lower):
    stack = []
    used0 = False
    for ch in word:
        if ch == "1":
            stack.append(mp.mpc(1))
            continue
        y = stack.pop()
        x = stack.pop()
        if y == 0:
            used0 = True
        ex = mp.mpf(0) if (x == mp.mpf("-inf") or (isinstance(x, mp.mpc) and mp.re(x) == mp.mpf("-inf"))) else mp.exp(x)
        stack.append(ex - ln(y, lower))
    return stack[0], used0


here = os.path.dirname(os.path.abspath(__file__))
root = os.path.join(here, "..", "lib", "eml")
rows = json.load(open(os.path.join(root, "integer-table.json"), encoding="utf-8"))
known = json.load(open(os.path.join(root, "best-known.json"), encoding="utf-8"))
bad = []
worst = mp.mpf(0)
seen = set()
for entry in rows:
    for word, claim0 in ((entry["word"], entry["usesLn0"]), (entry["wordNoLn0"], False)):
        if word in seen:
            continue
        seen.add(word)
        for lower in (True, False):
            try:
                value, used0 = ev(word, lower)
            except Exception as err:
                bad.append((entry["n"], lower, repr(err)))
                continue
            err = abs(value - entry["n"])
            worst = max(worst, err)
            if err > mp.mpf(10) ** -110:
                bad.append((entry["n"], lower, mp.nstr(value, 25)))
            if used0 != claim0:
                bad.append((entry["n"], lower, f"ln0 flag mismatch: mpmath {used0}, table {claim0}"))

for key, word in known["programs"].items():
    if key.endswith("-strict"):
        n = int(key[: -len("-strict")])
    elif key.lstrip("-").isdigit():
        n = int(key)
    else:
        continue
    if word in seen:
        continue
    seen.add(word)
    for lower in (True, False):
        value, _used0 = ev(word, lower)
        err = abs(value - n)
        worst = max(worst, err)
        if err > mp.mpf(10) ** -110:
            bad.append((key, lower, "program", mp.nstr(value, 25)))

print(
    f"mpmath cross-check: {len(seen)} distinct words, {'PASS' if not bad else 'FAIL'}; "
    f"worst |v − n| = {mp.nstr(worst, 3)} (130 digits; lower cut and principal Log)"
)
for item in bad:
    print("  bad", item)
sys.exit(1 if bad else 0)
