"""check_fail.py conv log -- retry the pairs check_merges.py could not settle: 200-digit at up to 65536 bits,
exact sympy with 120 s and the exp route tried first (exp(A-B) == 1 exactly plus a certified ball |A-B| < pi)."""
import sys, re, signal
sys.path.insert(0, '/workspace/eml-hub/mathbot/schanuel/hunt'); sys.path.insert(0, '.')
from common import form_to_sympy
from emlcore_recip import EC
from flint import arb
import sympy as sp
conv, log = sys.argv[1], sys.argv[2]
pairs = re.findall(r'(sympy did not reach 0|not resolved at 200 digits|timeout): (\S+) (\S+)', open(log).read())
C = EC.Ctx(conv, 'allowed')
class TO(Exception): pass
signal.signal(signal.SIGALRM, lambda *a: (_ for _ in ()).throw(TO()))
for kind, w1, w2 in pairs:
    f1, f2 = (EC.eval_tree(C, EC.parse_rpn(w)) for w in (w1, w2))
    print(kind, w1, w2, '\n   A =', C.show(f1)[:200], '\n   B =', C.show(f2)[:200], flush=True)
    if kind.startswith('not resolved'):
        for p in (16384, 65536):
            b1, b2 = C.ball(f1, p), C.ball(f2, p)
            tol = max(arb(1), abs(b1).upper()) * arb(10) ** -200
            print(f'   {p} bits: overlap {b1.overlaps(b2)}  rad1 {float(b1.rad()):.3g} rad2 {float(b2.rad()):.3g} |v| {float(abs(b1).mid()):.3g}'
                  f'  ok200 {b1.overlaps(b2) and b1.rad() < tol and b2.rad() < tol}', flush=True)
    A, B = form_to_sympy(C, f1, {}), form_to_sympy(C, f2, {})
    signal.alarm(120)
    try:
        e = sp.simplify(sp.powsimp(sp.expand(sp.exp(A - B))))
        d = C.ball(f1, 704) - C.ball(f2, 704)
        if e == 1 and abs(d).upper() < arb.pi():
            print('   sympy: exact via exp route'); continue
        def canon_exp(x):     # bring every exp argument to one rational function, bottom-up
            for _ in range(6):
                y = x.replace(sp.exp, lambda a: sp.exp(sp.cancel(sp.together(sp.expand(a)))))
                if y == x: break
                x = y
            return x
        z = sp.simplify(A - B)
        if z != 0:
            z = sp.simplify(canon_exp(z))
        if z != 0:
            z = sp.simplify(canon_exp(sp.expand(sp.powsimp(canon_exp(A - B)))))
        print('   sympy:', 'exact 0' if z == 0 else 'not 0: ' + str(z)[:200])
    except TO:
        print('   sympy: timeout 120 s')
    finally:
        signal.alarm(0)
