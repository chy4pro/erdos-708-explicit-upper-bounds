from fractions import Fraction as F
from math import factorial, log10, prod
import decimal
decimal.getcontext().prec=60
D=decimal.Decimal

# --- c_0 from S2: L <= m H^65/65!, H < 17/16
c0_exact = F(17,16)**65 / factorial(65)
print("(17/16)^65/65! =", D(c0_exact.numerator)/D(c0_exact.denominator))
print("  < 6.24e-90 ?", c0_exact < F(624,100)*F(1,10**90))
print("  > 6.23e-90 ?", c0_exact > F(623,100)*F(1,10**90))

# --- C_* exact
Cstar = F(32,3)*(1-F(1,6**31))
print("\nC_* = 32/3*(1-6^-31) =", D(Cstar.numerator)/D(Cstar.denominator))
print("  C_* > 52/5 = 10.4 ?", Cstar > F(52,5))
print("  1-6^-31 > 39/40 ?", 1-F(1,6**31) > F(39,40), " (6^31 =", 6**31, ")")
print("  (52/5)*(3/32) = 39/40 ?", F(52,5)*F(3,32)==F(39,40))

# --- (5/3)^32 > 10^7 ?
print("\n(5/3)^8 = 390625/6561 =", D(390625)/D(6561), " > 59 ?", F(390625,6561)>59)
print("59^4 =", 59**4, " > 10^7 ?", 59**4>10**7)
print("(5/3)^32 > 10^7 ?", F(5,3)**32 > 10**7, "  (5/3)^32 =", D((F(5,3)**32).numerator)/D((F(5,3)**32).denominator))
print("=> 10^(7/32) < 5/3 : ", True)

# --- Theorem 3 sufficient condition: c0*m^{1/32} <= C_*, exact
# m <= (C_*/c0)^32 ; check m=10^2887 works with c0=6.24e-90 and with exact c0
for name,c in [("6.24e-90",F(624,100)/10**90), ("(17/16)^65/65!", c0_exact)]:
    ratio = Cstar/c
    # threshold = ratio^32 ; compare with 10^2887 exactly
    lhs = ratio**32
    print("\nusing c0 = %s :  (C_*/c0)^32  vs 10^2887 :"%name)
    print("   log10 threshold =", float(32*(decimal.Decimal(ratio.numerator).ln()-decimal.Decimal(ratio.denominator).ln())/decimal.Decimal(10).ln()))
    print("   10^2887 <  threshold ?", 10**2887 < lhs)
    print("   10^2888 <  threshold ?", 10**2888 < lhs)
# exact max integer m: largest m with c0*m <= C_*m^{31/32}  <=> m <= (C_*/c0)^32
r = Cstar/F(624,100)*10**90
th = r**32
import math
print("\nexact sufficient range (c0=6.24e-90): m <= floor((C_*/c0)^32), log10 =", 
      float((decimal.Decimal(th.numerator).ln()-decimal.Decimal(th.denominator).ln())/decimal.Decimal(10).ln()))

# --- vacuity threshold: primorial(65)
def primes_upto(n):
    s=[True]*(n+1); s[0]=s[1]=False
    for i in range(2,int(n**.5)+1):
        if s[i]:
            for j in range(i*i,n+1,i): s[j]=False
    return [i for i,v in enumerate(s) if v]
P=primes_upto(400)[:65]
prim65=prod(P)
print("\n65th prime =",P[-1],"  primorial(65) =", D(prim65), " log10 =", log10(prim65))

# --- g(n) threshold: need (TH_65) for all m = a_n < 8n^3, i.e. m <= 8n^3-1 <= M0
for M0,label in [(10**2887,"10^2887"), (int(th),"(C_*/c0)^32"), (prim65,"primorial(65) [previous, trivial]")]:
    # largest n with 8n^3-1 <= M0
    lo,hi=1,10**1000
    while lo<hi:
        mid=(lo+hi+1)//2
        if 8*mid**3-1<=M0: lo=mid
        else: hi=mid-1
    print("\nM0 = %s : g(n)<=81n for all n <= N with N = %s"%(label, D(lo)))
    print("   log10 N =", float((decimal.Decimal(lo).ln())/decimal.Decimal(10).ln()))
    print("   is 10^961 <= N ?", 10**961<=lo, "  is 10^962 <= N ?", 10**962<=lo, "  is 10^963<=N ?",10**963<=lo)

# --- Lemma 5 (0/1): closure range  c0*m^{2/65} <= 32(1-6^-31)
C5=32*(1-F(1,6**31))
r5=C5/(F(624,100)/10**90)
print("\n0/1 branch (Lemma 5): m <= (32(1-6^-31)/c0)^{65/2}; log10 =",
      float(decimal.Decimal(65)/2*(decimal.Decimal(r5.numerator).ln()-decimal.Decimal(r5.denominator).ln())/decimal.Decimal(10).ln()))
