"""Write scripts/fixtures/program-id-vectors.json from mathbot's program_id_ref.py.

Usage: python3 scripts/program_id_vectors.py /path/to/program_id_ref.py
The reference file is not copied into this repo; only its outputs are.
"""
import importlib.util, json, random, sys

spec = importlib.util.spec_from_file_location("ref", sys.argv[1])
ref = importlib.util.module_from_spec(spec); spec.loader.exec_module(ref)
sys.setrecursionlimit(100000)

valid = [i for i in range(1, 1 << 14) if ref.is_valid_id(i)]
small = {
    "valid": [[i, ref.index_of(ref.id_to_word(i))] for i in valid],
    "nav": [[i, ref.prev_valid(i), ref.next_valid(i), ref.nearest_valid(i)] for i in range(0, 1 << 13)],
}
rng = random.Random(20261120)
def random_word(K):
    # uniform-ish random valid word by greedy random choice among feasible keys
    w, d = "", 0
    for p in range(K):
        rem = K - p - 1
        can1 = ref.completions(rem, d + 1) > 0
        canE = d >= 2 and ref.completions(rem, d - 1) > 0
        c = rng.choice([x for x, ok in (("1", can1), ("E", canE)) if ok])
        w += c; d += 1 if c == "1" else -1
    return w
big = []
for K in [21, 41, 81, 161, 201, 401, 801]:
    for _ in range(3):
        w = random_word(K)
        i = ref.word_to_id(w)
        big.append({"word": w, "id": str(i), "index": str(ref.index_of(w)),
                    "prev": str(ref.prev_valid(i)), "next": str(ref.next_valid(i)),
                    "programAtIndexPlus1": ref.program_at(ref.index_of(w) + 1)})
json.dump({"source": "program_id_ref.py", "small": small, "big": big}, open("scripts/fixtures/program-id-vectors.json", "w"))
print(len(valid), "valid ids;", len(small["nav"]), "nav rows;", len(big), "long words")
