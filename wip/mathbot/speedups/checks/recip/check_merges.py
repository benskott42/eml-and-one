"""check_merges.py merges_<conv>_<N>.json [sympy_timeout_s] -- criterion 3 spot checks for every new merge group:
 (a) 200-digit agreement: Arb balls of both raw emlcore forms at >= 704 bits (escalating to 8192), require that they
     overlap and that both radii are < 1e-200 * max(1, |value|) -- otherwise reported as 'not resolved at 200 digits';
 (b) exact sympy: form -> sympy (exp/log atoms, explicit i*pi), simplify(A - B) == 0 with a timeout."""
import sys, json, signal
sys.path.insert(0, '/workspace/eml-hub/mathbot/schanuel/hunt')
from common import form_to_sympy
sys.path.insert(0, '.')
from emlcore_recip import EC
from flint import arb, ctx
import sympy as sp
d = json.load(open(sys.argv[1])); TO = int(sys.argv[2]) if len(sys.argv) > 2 else 20
C = EC.Ctx(d['conv'], 'allowed')
class TO_(Exception): pass
def alarm(*a): raise TO_()
signal.signal(signal.SIGALRM, alarm)
sym_exp = [0]
ok200 = unres200 = bad = sym_ok = sym_fail = sym_to = sym_skip = 0
for g in d['merges']:
    fids = [EC.eval_tree(C, EC.parse_rpn(w)) for w in g]
    for w, f in zip(g[1:], fids[1:]):
        f0 = fids[0]; res = None
        for p in (704, 2048, 8192):
            b0, b1 = C.ball(f0, p), C.ball(f, p)
            scale = max(arb(1), abs(b0).upper())
            tol = scale * arb(10) ** -200
            if not b0.overlaps(b1):
                res = 'MISMATCH'; break
            if b0.rad() < tol and b1.rad() < tol:
                res = 'ok'; break
        if res is None: unres200 += 1; print('  not resolved at 200 digits:', g[0], w)
        elif res == 'ok': ok200 += 1
        else: bad += 1; print('  MISMATCH:', g[0], w)
        try:
            A = form_to_sympy(C, f0, {}); B = form_to_sympy(C, f, {})
        except ValueError:
            sym_skip += 1; continue
        signal.alarm(TO)
        try:
            z = sp.simplify(A - B)
            if z == 0: sym_ok += 1
            else:
                z2 = sp.simplify(sp.together(sp.expand(sp.powsimp(sp.expand_log(z, force=False)))))
                if z2 == 0: sym_ok += 1
                else:
                    # exp route: exp(A) = exp(B) exactly gives A - B in 2*pi*i*Z; the 704-bit ball |A - B| < pi then forces 0
                    e = sp.simplify(sp.powsimp(sp.expand(sp.exp(A - B))))
                    dball = C.ball(f0, 704) - C.ball(f, 704)
                    if e == 1 and abs(dball).upper() < arb.pi():
                        sym_ok += 1; sym_exp[0] += 1
                    else: sym_fail += 1; print('  sympy did not reach 0:', g[0], w)
        except TO_:
            sym_to += 1
        finally:
            signal.alarm(0)
print(f"{d['conv']} K<={2*d['NMAX']-1}: merge pairs {ok200+unres200+bad}: 200-digit ok {ok200}, unresolved-at-200 {unres200}, MISMATCH {bad}; "
      f"sympy exact 0: {sym_ok} (of which via exp(A-B)=1 plus ball |A-B|<pi: {sym_exp[0]}), not simplified to 0: {sym_fail}, timeout({TO}s): {sym_to}, skipped(opaque): {sym_skip}")
