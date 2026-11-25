#!/usr/bin/env python3
"""
Compare certified finite results from `tools/fuzz/fuzz.ts --json` against mpmath
at 2,500 digits of precision.

Usage:
  npx tsx tools/fuzz/fuzz.ts --count 1000 --seed 1 --json fuzz.json
  python3 tools/fuzz/oracle.py fuzz.json
"""
import json
import sys
import mpmath as mp

mp.mp.dps = 2500

ENV = {
    "pi": mp.pi,
    "e": mp.e,
    "i": mp.mpc(0, 1),
    "inf": mp.inf,
    "exp": mp.exp,
    "ln": mp.log,
    "sqrt": mp.sqrt,
    "sin": mp.sin,
    "cos": mp.cos,
    "tan": mp.tan,
    "sinh": mp.sinh,
    "cosh": mp.cosh,
    "tanh": mp.tanh,
    "asin": mp.asin,
    "acos": mp.acos,
    "atan": mp.atan,
    "asinh": mp.asinh,
    "acosh": mp.acosh,
    "atanh": mp.atanh,
}


def eval_mp(source: str):
    py_expr = source.replace("^", "**")
    return mp.mpc(eval(py_expr, {"__builtins__": {}}, ENV))


def main():
    if len(sys.argv) < 2:
        print("Usage: python3 tools/fuzz/oracle.py <fuzz.json>", file=sys.stderr)
        sys.exit(2)
    with open(sys.argv[1], "r", encoding="utf-8") as f:
        data = json.load(f)

    checked = 0
    wrong = []
    skipped = 0
    for row in data["rows"]:
        if row["status"] != "certified" or "re" not in row or "im" not in row:
            continue
        try:
            want = eval_mp(row["source"])
            if not (mp.isfinite(want.real) and mp.isfinite(want.imag)):
                skipped += 1
                continue
            got = mp.mpc(mp.mpf(row["re"]), mp.mpf(row["im"]))
            checked += 1
            scale = max(abs(want), mp.mpf("1e-300"))
            err = abs(got - want) / scale
            if err > mp.mpf("1e-10"):
                wrong.append((row["source"], row["exact"], mp.nstr(want, 12), mp.nstr(err, 4)))
        except Exception:
            skipped += 1

    print(f"mpmath oracle (dps={mp.mp.dps}): checked={checked} skipped={skipped} wrong={len(wrong)}")
    for source, got_s, want_s, err_s in wrong[:25]:
        print(f"  WRONG {source}: got={got_s} want={want_s} rel_err={err_s}")
    sys.exit(1 if wrong else 0)


if __name__ == "__main__":
    main()
