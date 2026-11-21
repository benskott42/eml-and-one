"""orders_words.py NMAX conv -- breakerbot's order-independence check, WORD BY WORD.
Every RPN word with <= NMAX leaves is evaluated in the canonical layer C0 and keyed into C1, in 5 enumeration orders
(forward, reverse, random seeds 1-3; random = the whole level's word list shuffled), each in a fresh Ext.  For every word
the structural hash of its C0 form and of its key form (id-independent: blake2b over (cre, cim, sorted (kind, hash(arg), k)))
is compared with the forward order.  UNVERIFIED keys, Unresolved words and raw-form fallbacks are counted separately.
Config via env: VER (v2), R4MAX (None), MULTI (1)."""
import sys, os, time, random, hashlib
sys.path.insert(0, '.')
from emlcore_recip import *
NMAX = int(sys.argv[1]); conv = sys.argv[2]
RecipCtx.version = CanonCtx.version = os.environ.get('VER', 'v2')
_r4 = os.environ.get('R4MAX', 'None'); RecipCtx.r4_max = None if _r4 == 'None' else int(_r4)
RecipCtx.multi = os.environ.get('MULTI', '1') == '1'
RecipCtx.log_atoms = os.environ.get('LOGATOMS', '1') == '1'
print(f"config: version={RecipCtx.version} C1 r4_max={RecipCtx.r4_max} multi={RecipCtx.multi} C1 log_atoms={RecipCtx.log_atoms}", flush=True)
# canonical word list per level: (ia, ib, i) with i = split (leaves of left child)
levels = {1: [None]}
for n in range(2, NMAX + 1):
    levels[n] = [(i, ia, ib) for i in range(1, n) for ia in range(len(levels[i])) for ib in range(len(levels[n - i]))]
def word(n, j):
    if n == 1: return '1'
    i, ia, ib = levels[n][j]; return word(i, ia) + word(n - i, ib) + 'E'
def shash(C, fid, memo):
    r = memo.get(fid)
    if r is None:
        cre, cim, terms = C.fkey[fid]
        t = sorted((C.akind[a], shash(C, C.aarg[a], memo), k) for a, k in terms)
        r = hashlib.blake2b(repr((str(cre), cim, t)).encode(), digest_size=10).hexdigest()
        memo[fid] = r
    return r
def run(order, seed):
    rng = random.Random(seed); X = Ext(conv); m0, m1 = {}, {}
    val = {1: [X.C0.ONE]}; out = {}; pm = {}; kmemo = {}
    cnt = dict(unres=0, unverified=0, fallback_words=0, special=0)
    for n in range(2, NMAX + 1):
        idx = list(range(len(levels[n])))
        if order == 'reverse': idx.reverse()
        elif order == 'random': rng.shuffle(idx)
        vals = [None] * len(idx); hs = [None] * len(idx)
        for j in idx:
            i, ia, ib = levels[n][j]; a, b = val[i][ia], val[n - i][ib]
            if a is None or b is None or a in ('NAN', 'INVALID') or b in ('NAN', 'INVALID'):
                v = None
            else:
                k = (repr(a) if is_special(a) else a, repr(b) if is_special(b) else b)
                if k not in pm:
                    try: pm[k] = EC.eml_val(X.C0, a, b)
                    except EC.Unresolved: pm[k] = 'UNRES'
                    except (Unverified, RecursionError): pm[k] = 'UNVER'; X.C0._depth = 0
                v = pm[k]
            if v == 'UNRES': cnt['unres'] += 1; hs[j] = 'UNRES'; v = None
            elif v == 'UNVER': cnt['unverified'] += 1; hs[j] = 'UNVER-C0'; v = None
            elif v is None or v in ('NAN', 'INVALID'): hs[j] = str(v)
            elif is_special(v): cnt['special'] += 1; hs[j] = 'SPECIAL:' + str(v[0]) + str(v[2] if len(v) > 2 else '')
            else:
                if v not in kmemo: kmemo[v] = X.key(v)
                kk = kmemo[v]
                if kk[0] == 'UNVERIFIED': cnt['unverified'] += 1; hs[j] = 'UNVER-key'
                else:
                    if kk[0] == 'R': cnt['fallback_words'] += 1
                    hs[j] = (shash(X.C0, v, m0), kk[0] + ':' + (shash(X.C1, kk[1], m1) if kk[0] == 'N' else shash(X.C0, kk[1], m0)))
            vals[j] = v
        val[n] = vals; out[n] = hs
    return out, cnt, X
t = time.time()
base, cnt, X = run('forward', 0)
print(f"[{conv}] forward: {cnt}  key classes (finite, verified) {len(set(h[1] for n in base for h in base[n] if isinstance(h, tuple)) )}  {time.time()-t:.0f}s", flush=True)
for order, seed in [('reverse', 0), ('random', 1), ('random', 2), ('random', 3)]:
    t = time.time(); o, c, _ = run(order, seed)
    d0 = dk = ds = 0; ex = []
    for n in base:
        for j, (h1, h2) in enumerate(zip(base[n], o[n])):
            if h1 == h2: continue
            if isinstance(h1, tuple) and isinstance(h2, tuple):
                d0 += h1[0] != h2[0]; dk += h1[1] != h2[1]
            else: ds += 1
            if len(ex) < 5: ex.append(word(n, j))
    print(f"[{conv}] {order}{seed or ''}: {c}; words with different C0 form {d0}, different key form {dk}, other status differences {ds}; examples {ex}  {time.time()-t:.0f}s", flush=True)
print(f"[{conv}] words checked per order: {sum(len(base[n]) for n in base)}")
