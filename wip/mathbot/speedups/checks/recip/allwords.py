"""allwords.py NMAX conv -- criterion 1 word by word: every RPN word with <= NMAX leaves (all Catalan trees, not one
per class) is evaluated in unmodified emlcore (reference) and in the final key; checks ref-equal => key-equal."""
import sys, time
sys.path.insert(0, '.')
from emlcore_recip import *
NMAX = int(sys.argv[1]); conv = sys.argv[2]
import os
RecipCtx.version = CanonCtx.version = os.environ.get('VER', 'v2')
_r4 = os.environ.get('R4MAX', 'None'); RecipCtx.r4_max = None if _r4 == 'None' else int(_r4)
RecipCtx.multi = os.environ.get('MULTI', '1') == '1'
RecipCtx.log_atoms = os.environ.get('LOGATOMS', '1') == '1'
print(f"config: version={RecipCtx.version} C1 r4_max={RecipCtx.r4_max} multi={RecipCtx.multi} C1 log_atoms={RecipCtx.log_atoms}", flush=True)
n_unv_words = 0; unv_classes = set()
t = time.time()
Cr = EC.Ctx(conv, 'allowed'); X = Ext(conv)
def ev(C, memo, a, b):
    k = (h(a), h(b))
    if k not in memo:
        if a in ('NAN', 'INVALID') or b in ('NAN', 'INVALID') or a is None or b is None:
            memo[k] = None
        else:
            try: memo[k] = EC.eml_val(C, a, b)
            except EC.Unresolved: memo[k] = 'UNRES'
            except RecursionError: memo[k] = 'LOOP'
        if memo[k] in ('NAN', 'INVALID', 'UNRES', 'LOOP'):
            pass
    return memo[k]
mr, mc = {}, {}
H = {}
def h(v):
    if isinstance(v, int) or v is None or isinstance(v, str): return v
    k = ('S', repr(v)); H[k] = v; return k
def uh(k):
    return H[k] if isinstance(k, tuple) and k and k[0] == 'S' else k
lev = {1: {(Cr.ONE, X.C0.ONE): 1}}           # per n: list of (ref value, canon value) for every word
cnt = {1: 1}
keys_seen = set(); ref2key = {}; viol = []; n_words = 0; n_bad = {'UNRES': 0, 'LOOP': 0}; keymemo = {}
def kkey(v):
    if v not in keymemo: keymemo[v] = X.key(v)
    return keymemo[v]
from collections import Counter
for n in range(2, NMAX + 1):
    # group words by (ref, canon) value pair with multiplicity, so identical subtrees are not re-evaluated
    cur = Counter()
    for i in range(1, n):
        for (ra, ca), ma in lev[i].items() if isinstance(lev[i], dict) else Counter(lev[i]).items():
            for (rb, cb), mb in lev[n - i].items() if isinstance(lev[n - i], dict) else Counter(lev[n - i]).items():
                r = h(ev(Cr, mr, uh(ra), uh(rb))) if not (isinstance(ra, str) or isinstance(rb, str) or ra is None or rb is None) else None
                c = h(ev(X.C0, mc, uh(ca), uh(cb))) if not (isinstance(ca, str) or isinstance(cb, str) or ca is None or cb is None) else None
                cur[(r, c)] += ma * mb
    lev[n] = cur
    for (r, c), m in cur.items():
        n_words += m
        if r in n_bad or c in n_bad:
            n_bad[r if r in n_bad else c] += m; continue
        if r is None or c is None or (isinstance(r, str) and r in ('NAN', 'INVALID')): continue
        if not isinstance(r, int) or not isinstance(c, int):
            continue                       # specials (+-inf etc.) are handled by skey_special, not by forms
        k = kkey(c)
        if k[0] in ('UNVERIFIED', 'LOOP'):          # loud: counted separately, never stored as an ordinary key
            n_unv_words += m; unv_classes.add(r); continue
        keys_seen.add(str(k))
        if ref2key.setdefault(r, k) != k:
            viol.append((n, r, c, k, ref2key[r]))
    print(f"[{conv}] n={n} K={2*n-1}: words {sum(cur.values())}, distinct (ref, canon) value pairs {len(cur)}, "
          f"ref classes so far {len(ref2key)}, key classes so far {len(keys_seen)}, violations so far {len(viol)}, unresolved/loop word counts {n_bad}, "
          f"UNVERIFIED-key words {n_unv_words} (ref classes {len(unv_classes)}), C1-unresolved raw fallbacks {getattr(X, 'n_fallback', 0)}, "
          f"maxdepth C0 {X.C0.__dict__.get('_maxdepth')} C1 {X.C1.__dict__.get('_maxdepth')}  {time.time()-t:.0f}s", flush=True)
print(f"[{conv}] TOTAL words {n_words + 1}: ref-equal but key-different: {len(viol)}; UNVERIFIED-key words {n_unv_words}")
print(f"[{conv}] C1 stats", {k: v for k, v in X.C1.stats.items() if k.startswith(('rule', 'guard', 'R3_', 'R6_'))})
print(f"[{conv}] C0 stats", {k: v for k, v in X.C0.stats.items() if k.startswith(('rule', 'guard', 'R3_', 'R6_'))})
for v, why in X.unverified[:10]: print('   UNVERIFIED', why, X.C0.show(v)[:200])
for v in viol[:10]:
    sk = lambda k: X.C1.show(k[1]) if k[0] == 'N' else str(k)
    print('   n', v[0], '\n     ref form :', Cr.show(v[1])[:400], '\n     canon    :', X.C0.show(v[2])[:400], '\n     key A    :', sk(v[3])[:400], '\n     key B    :', sk(v[4])[:400])
