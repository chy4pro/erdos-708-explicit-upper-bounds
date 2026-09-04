from fractions import Fraction as F
import random

# --- Lemma 10 exact polynomial identity, done with exact rational polynomial arithmetic ---
# derived: 270400*(t-1-t/65) - 65*(64 - t/65)*t*(t-1)
# expand by evaluating at 4 points and comparing to claimed cubic (t-65)(t^2-4096t+4160)
def derived(t): return F(270400)*(t-1-F(t,65)) - F(65)*(F(64)-F(t,65))*t*(t-1)
def claimed(t): return (t-65)*(t*t-4096*t+4160)
print("identity check at t=0..8:", all(derived(t)==claimed(t) for t in range(0,9)))
print("identity check at t=100,-7,65,2:", [derived(t)==claimed(t) for t in (100,-7,65,2)])
disc=4096**2-4*4160
print("roots of t^2-4096t+4160 approx:", (4096-disc**0.5)/2, (4096+disc**0.5)/2)
print("nonneg on 0<=t<=65:", all(claimed(t)>=0 for t in range(0,66)), " zeros at t in", [x for x in range(66) if claimed(x)==0])

# --- brute force feasibility of c_* = (B-1)/2080 on all-pairs, unequal masses ---
def worst_slack(bs):
    B=sum(bs); c=(B-1)/F(2080); s=sorted(bs); n=len(bs); w=None
    for tt in range(2,n+1):
        S0=sum(s[:tt]); lhs=c*F(tt*(tt-1),2); rhs=max(S0-1,F(0)); sl=rhs-lhs
        if w is None or sl<w[0]: w=(sl,tt)
    return w
random.seed(1); mins=[]
for _ in range(20000):
    bs=[F(64,65)+F(random.randint(1,10**6),65*10**6) for _ in range(65)]
    if sum(bs)<=64: continue
    mins.append(worst_slack(bs)[0])
print("\nmin slack over %d random unequal-mass instances: %s (%.6g)"%(len(mins),min(mins),float(min(mins))))
for eps in [F(1,65*10**6), F(1,10**4), F(1,66), F(1,65)]:
    bs=[F(64,65)+eps]*65; w=worst_slack(bs)
    print("uniform eps=%-14s B=%.8f worst slack=%.8g at t=%d"%(eps,float(sum(bs)),float(w[0]),w[1]))

# --- Lemma 9 ---
eps=F(1,10000); bs=[F(64,65)+eps]*65; B=sum(bs)
print("\nLemma 9: all-pairs 2/65 value at n=k =", float(F(2,65)*2080), "  capacity (S0-1)^+ =", float(B-1),
      "  infeasible:", F(2,65)*2080 > B-1, " excess =", float(F(2,65)*2080-(B-1)))
print("  H = 65*(64/65+eps)/1000 =", float(65*(F(64,65)+eps)/1000), "< 17/16:", 65*(F(64,65)+eps)/1000 < F(17,16))
print("  packing counterexample: 107*(3/5) =", float(107*F(3,5)), "> 64 ; single item 0.6 < 64/65 =", float(F(64,65)), "; two items 1.2 > 1")
print("\nLemma 11: 64/C(65,2) =", F(64,2080), " equals 2/65:", F(64,2080)==F(2,65))
