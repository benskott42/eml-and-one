"""conj_audit.py N -- cut-conjugation audit of emlcore (speedups/cut-conjugation-audit.md).
Enumerates n <= N on both cuts with the reference class DP (hunt/common.py enumerate_values), then checks:
 (1) per-level finite class counts and special-key kinds agree;
 (2) STRUCTURAL map: phi(principal form) = conj form looked up (never created) in the lower context;
     phi(V_P[n]) must equal V_L[n] exactly, as sets of form ids;
 (3) every principal class's shortest word, evaluated on the lower cut, gives phi(v), and its 2048-bit ball
     overlaps conj(principal ball);
 (4) specials: kind and conj imaginary ball agree word by word.
 Also: additive hash checks (two Mersenne-61 hashes) -- injectivity on all interned forms of each context."""
import sys, time, random
sys.path.insert(0, '/workspace/eml-hub/mathbot/schanuel/hunt')
from common import *
N = int(sys.argv[1])
t0 = time.time()
CP, VP, bestP, _, unP = enumerate_values(N, 'principal', True)
t1 = time.time()
CL, VL, bestL, _, unL = enumerate_values(N, 'lower', True)
t2 = time.time()
print(f"time principal {t1-t0:.1f}s lower {t2-t1:.1f}s; unresolved P {len(unP)} L {len(unL)}")
print(f"forms P {len(CP.fkey)} L {len(CL.fkey)}; atoms P {len(CP.akind)} L {len(CL.akind)}; opaque P {len(CP.__dict__.get('aopaque',()))} L {len(CL.__dict__.get('aopaque',()))}")
fmemo, amemo = {}, {}
class Missing(Exception): pass
def phi_f(f):
    if f in fmemo: return fmemo[f]
    cre, cim, terms = CP.fkey[f]
    t2 = []
    for a, k in terms:
        t2.append((phi_a(a), k))
    key = (cre, -cim, tuple(sorted(t2)))
    g = CL.fid_of.get(key)
    if g is None: raise Missing(('form', CP.show(f)))
    fmemo[f] = g; return g
def phi_a(a):
    if a in amemo: return amemo[a]
    b = CL.aid_of.get((CP.akind[a], phi_f(CP.aarg[a])))
    if b is None: raise Missing(('atom', a))
    if (a in CP.__dict__.get('aopaque', ())) != (b in CL.__dict__.get('aopaque', ())): raise Missing(('opaque-flag', a))
    amemo[a] = b; return b
tot_ok = True
for n in range(1, N + 1):
    fP = [v for k, v in VP[n].items() if k[0] == 'F']; fL = {v for k, v in VL[n].items() if k[0] == 'F'}
    sP = sorted(str(k[0]) + (k[1] if len(k) > 1 and isinstance(k[1], str) else '') for k in VP[n] if k[0] != 'F')
    sL = sorted(str(k[0]) + (k[1] if len(k) > 1 and isinstance(k[1], str) else '') for k in VL[n] if k[0] != 'F')
    miss = 0; img = set()
    for v in fP:
        try: img.add(phi_f(v))
        except Missing as e: miss += 1; print('  missing', e)
    ok = (miss == 0 and img == fL and len(fP) == len(fL) and sP == sL)
    tot_ok &= ok
    print(f"n={n} K={2*n-1}: finite new P {len(fP)} L {len(fL)}; phi missing {miss}; phi(V_P)==V_L {img == fL}; specials P {len(sP)} L {len(sL)} same-kinds {sP == sL} -> {'OK' if ok else 'FAIL'}")
# (3)/(4) word-by-word
bad = spec_bad = n_chk = 0
for n in VP:
    for k, v in VP[n].items():
        w = bestP[k]; v2 = EC.eval_tree(CL, EC.parse_rpn(w))
        if k[0] == 'F':
            n_chk += 1
            if EC.is_special(v2) or v2 != fmemo.get(v) or not CP.ball(v, 2048).conjugate().overlaps(CL.ball(v2, 2048)):
                bad += 1; print('  word mismatch', w)
        else:
            v1 = v
            if isinstance(v1, str) or isinstance(v2, str) or not EC.is_special(v2):
                if v1 != v2: spec_bad += 1; print('  special mismatch', w, v1, v2)
                continue
            if v1[0] != v2[0]: spec_bad += 1; print('  special kind mismatch', w, v1, v2); continue
            if v1[0] in ('P', 'N'):
                if v1[2] != v2[2] or not (-v1[1]).overlaps(v2[1]): spec_bad += 1; print('  special imag mismatch', w, v1, v2)
            elif v1[0] == 'D':
                if not (-v1[1]).overlaps(v2[1]): spec_bad += 1; print('  dir mismatch', w, v1, v2)
print(f"word check: finite {n_chk}, mismatches {bad}; special mismatches {spec_bad}")
# additive hash injectivity
P61 = (1 << 61) - 1
def hashes(C, seed):
    rng = random.Random(seed); out = []
    for _ in range(2):
        Rre, Rim = rng.randrange(1, P61), rng.randrange(1, P61)
        Ra = [rng.randrange(1, P61) for _ in range(len(C.akind))]
        hs = [ (cre * Rre + cim * Rim + sum(k * Ra[a] for a, k in t)) % P61 for (cre, cim, t) in C.fkey ]
        out.append(hs)
    return list(zip(*out))
for name, C in (('principal', CP), ('lower', CL)):
    hs = hashes(C, 12345)
    d = {}
    coll = 0
    for f, h in enumerate(hs):
        if h in d and C.fkey[d[h]] != C.fkey[f]: coll += 1
        d.setdefault(h, f)
    single = len({h[0] for h in hs})
    print(f"hash[{name}]: forms {len(hs)}, distinct (h1,h2) {len(d)}, collisions {coll}, distinct h1 alone {single}")
print('ALL STRUCTURAL CHECKS', 'PASS' if tot_ok and bad == 0 and spec_bad == 0 else 'FAIL')
