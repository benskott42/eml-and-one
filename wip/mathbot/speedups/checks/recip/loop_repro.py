"""loop_repro.py conv: reproduce unmodified emlcore's R3<->R5 non-termination (random1 DP order, K25) and print the cycle."""
import sys
sys.path.insert(0, '.')
from emlcore_recip import EC, raw_dp
conv = sys.argv[1]
class Trace(EC.Ctx):
    def log_f(self, fid):
        st = self.__dict__.setdefault('_st', [])
        st.append(fid)
        try:
            return EC.Ctx.log_f(self, fid)
        except RecursionError:
            if not self.__dict__.get('_dumped'):
                self._dumped = True
                seen = {}
                for i, f in enumerate(st):
                    if f in seen:
                        print(f'  log_f({f}) re-entered: first at depth {seen[f]}, again at {i}; cycle length {i - seen[f]}')
                        self._cycle = list(st[seen[f]:i + 1]); self._pre = list(st[:seen[f]])
                        break
                    seen[f] = i
                else:
                    print('  no exact repeat in stack; depth', len(st), 'last args:')
                    for g in st[-6:]: print('    ', self.show(g)[:300])
            raise
        finally:
            st.pop()
C, V, best, unres = raw_dp(13, conv, 'random', 1, C=Trace(conv, 'allowed'))
print('loop words:', [u for u in unres if u.startswith('LOOP')])
for g in C._pre: print('  outer Log arg:', C.show(g))
for g in C._cycle:
    r3 = None
    print('  cycle Log arg:', C.show(g))
