from fractions import Fraction as F
import math, random, sys

# ---------- exact rational verification of the constants in Lemmas 5 / Thm 6 ----------
print("=== A. exact constant chain (Lemma 5) ===")
Hlo, Hhi = F(17,16), F(17,16)+F(1,2)
print("greedy window [17/16, 17/16+1/2] =", Hlo, Hhi, "  25/16 =", F(25,16), "match:", Hhi==F(25,16))
first = F(63,64)*Hlo
print("(4.6) first moment coeff  (63/64)*(17/16) =", first, " claimed 1071/1024 ->", first==F(1071,1024))
second = Hhi + Hhi**2
print("(4.9) second moment coeff  H+H^2 at H=25/16 =", second, " claimed 1025/256 ->", second==F(1025,256))
res = first - second/256
print("(4.11) net coeff =", res, "=", float(res), " claimed 67519/65536 ->", res==F(67519,65536))
print("      surplus per m:", res-1, "=", float(res-1), " claimed 1983/65536 ->", (res-1)==F(1983,65536))
print("      surplus*m>1 requires m >", float(1/(res-1)))
# quadratic cap
print("(4.10) min(t,64) >= t - t^2/256 ?")
bad=[]
for i in range(0,200001):
    t=i/500.0
    if min(t,64.0) < t - t*t/256.0 - 1e-12: bad.append(t)
print("   violations on grid [0,400]:", len(bad), " max of t-t^2/256 at t=128 ->", 128-128*128/256)
