import json
rows=json.load(open('/workspace/eml-hub/oeis/mathbot-scripts/n10-audit/rows.json'))
assert len(rows)==5059
def clean(s):
    s=s.strip()
    return s
def unres(r): return r['src']!='mpmath' and (r.get('acc') is None or r['acc']<200)
NU=sum(unres(r) for r in rows)
H=f"""# mathbot n<=10 class representatives for a(10) = {len(rows)} (data only; draft, pending review)
# Model: emlcore.py (unmodified), LOWER cut Arg in [-pi,pi), inf policy 'allowed' (internal infinities kept, only finite values counted).
# Classes = emlcore canonical forms (5065 finite) merged by the six proven K19 field identities (exp(S - Log w) = exp(S)/w family):
#   1111EEE11EE=111111EEE11EEE1EE1E ; 111E11E1EEE11EE=111E1EE11E11E1EEE1E ; 1111EEE111EE1E1EE=11111EEE1EE111EEE1E ;
#   1111EE11EEE11E1EE=111E1EE111EE11EEE1E ; 111E1EE111EEE11EE=11111E1EEEE111EEE1E ; 111E11E1E1E1EEE11EE=11E11E11E1E1E1EEE1E
# buggybot's 7th identity (11111E11EEE11EEE1EE = 11111E1EEEE11E11EEE) is already ONE emlcore class (same canonical form); no extra merge.
# Representative = shortest word in the class, then lexicographically first ('1' < 'E').
# Flags: b = shortest program has exactly 10 leaves (sum {sum(r['b'] for r in rows)}); c = reachable with exactly 10 leaves (sum {sum(r['c'] for r in rows)});
#        z = reachable by some ln0-free program with <=10 leaves (sum {sum(r['ln0free'] for r in rows)} = a0(10)).
# Values: lower cut (conjugate of principal). src=mpmath: canonical form evaluated in mpmath at 90 and 180 dps, agreeing to >=64 digits.
#        src=arb8192: mpmath skipped/unstable (tower or cancellation); value is the midpoint of emlcore's Arb ball; 'acc' = certified relative accuracy in bits.
#        Tower values that overflow / underflow Arb, or near-collisions, cannot be given to 60 digits; those rows show the ball as printed by Arb (may be [+/- inf]).
#        {NU} rows have no 60-digit value (tower overflow/underflow or Arb accuracy < 200 bits); their re/im show 'UNRESOLVED' and the raw Arb ball in brackets.
#        The exact canonical form (emlcore show(), lower cut) is the last column and is the authoritative identity of the class.
# Columns (TAB-separated): n_min  word  flags(b,c,z)  re  im  src  acc_bits  form
"""
with open('/workspace/eml-hub/oeis/mathbot-n10-classes.txt','w') as f:
    f.write(H)
    for r in rows:
        fl=f"{r['b']}{r['c']}{r['ln0free']}"
        f.write('\t'.join([str((len(r['word'])+1)//2),r['word'],fl,*( (clean(r['re']),clean(r['im'])) if not unres(r) else ('UNRESOLVED['+clean(r['re'])+']','UNRESOLVED['+clean(r['im'])+']') ),r['src'],str(r.get('acc','')),r.get('form','').replace('\n',' ').replace('\t',' ')])+'\n')
print('written',len(rows))
