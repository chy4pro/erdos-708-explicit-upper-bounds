from fractions import Fraction as F
from math import comb, prod
import random, decimal
decimal.getcontext().prec=60
D=decimal.Decimal

# ---------- (A) improved 0/1 pair certificate: all C(65,2) pairs instead of 32 disjoint ones
# scaled analogue: NP primes, threshold NP-1; c = 2/NP on all pairs
def scaled_pair_test(NP, primes, m, x):
    P=primes[:NP]
    S=[0]*(m+1)
    for q in P:
        n=((x//q)+1)*q
        while n<=x+m: S[n-x]+=1; n+=q
    R=sum(v-1 for v in S[1:] if v>1)
    Q=prod(P)
    # certificate value with c=2/NP on all pairs
    val=F(2,NP)*sum((x+m)//(P[i]*P[j])-x//(P[i]*P[j]) for i in range(NP) for j in range(i+1,NP))
    # engine Lemma5 analogue: t=(NP-1)//2 disjoint pairs
    t=(NP-1)//2
    Ds=[P[2*i]*P[2*i+1] for i in range(t)]
    val_eng=sum((x+m)//Dd-x//Dd for Dd in Ds)
    # asymptotic bounds
    k=Q
    b_new=(NP-1)*m/ k**(2.0/NP)
    b_eng=2*t/2*1.0*m/k**(2.0/NP)   # 2t/2? engine: t*(1-6^-(t-1)) ... use t (coefficient 1 per pair)
    return R,float(val),float(val_eng), b_new, t*m/k**(2.0/NP)

primes=[2,3,5,7,11,13,17,19,23,29,31,37]
print("=== 0/1 pair certificate: all pairs (c=2/NP) vs engine's 32 disjoint pairs (scaled) ===")
for NP,m in [(5,3000),(5,100000),(7,600000),(7,3000000)]:
    rng=random.Random(NP*m)
    worst=None
    for _ in range(30):
        x=rng.randint(0,10**8)
        R,v,ve,bn,be=scaled_pair_test(NP,primes,m,x)
        if worst is None or R<worst[0]: worst=(R,v,ve,bn,be)
    R,v,ve,bn,be=worst
    print(" NP=%d m=%d: min_x R=%d ; all-pairs cert value=%.1f (valid: %s) ; disjoint-pairs value=%.1f ; "
          "asym bounds  new=(NP-1)m/k^{2/NP}=%.1f  engine=t*m/k^{2/NP}=%.1f"%(NP,m,R,v,R>=v,ve,bn,be))

# ---------- (B) closure ranges
c0=F(624,100)/10**90
def rng_log10(const, expo_den, expo_num=1):
    # m <= (const/c0)^(expo_den/expo_num)
    r=F(const)/c0 if not isinstance(const,F) else const/c0
    return float(F(expo_den,expo_num)*(D(r.numerator).ln()-D(r.denominator).ln())/D(10).ln())
print("\n=== closure ranges log10(m_max) ===")
print(" engine Lemma 2 (fractional): C=32/3(1-6^-31), exponent 1/32   -> %.2f"%rng_log10(F(32,3)*(1-F(1,6**31)),32))
print(" engine Lemma 5 (0/1):        C=32(1-6^-31),   exponent 2/65   -> %.2f"%rng_log10(F(32)*(1-F(1,6**31)),65,2))
print(" improved  Lemma 5 (0/1):     C=64(1-eps),     exponent 2/65   -> %.2f"%rng_log10(F(64),65,2))
print(" conjectural fractional       C=64,            exponent 2/65   -> %.2f"%rng_log10(F(64),65,2))

# ---------- (C) where 81n beats the published unconditional O(n loglog n) bound
import math
def bnd(n): return 16+20*math.log(math.log(8*n**3))
lo,hi=2,10**6
while lo<hi:
    mid=(lo+hi)//2
    if bnd(mid)>81: hi=mid
    else: lo=mid+1
print("\n=== 81n vs published unconditional (16+20 ln ln(8n^3))n ===")
print(" smallest n where 81n is the better bound:", lo, " (value at n-1: %.3f, at n: %.3f)"%(bnd(lo-1),bnd(lo)))
