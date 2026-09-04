from decimal import Decimal as D, getcontext
from math import factorial, log, log2
getcontext().prec = 200
M=2000; Q=D(2)**M; ln2=D(2).ln()
# Lemma 7 chain, exact-ish
# L/V > Q^(4/5) / (2^194 * 65! * (log 2Q)^64)
num = D(2)**(D(4)*M/5)
den = D(2)**194 * D(factorial(65)) * ((M+1)*ln2)**64
print("exact ratio bound L/V >", (num/den), " = 2^", (num/den).ln()/ln2)
print("claimed 2^247 =", D(2)**247)
print("margin holds:", num/den > D(2)**247)
# their crude replacements
print("65! =", D(factorial(65)), "< 2^455 =", D(2)**455, ":", D(factorial(65))<D(2)**455)
print("log(2Q) =", (M+1)*ln2, "< 2^11:", (M+1)*ln2 < D(2)**11)
print("exponent bookkeeping 1600-194-455-704 =", 1600-194-455-11*64)
# monotonicity in M
print("d/dM log(2^(4M/5)/(M+1)^64) at M=2000:", float(D(4)/5*ln2 - D(64)/(M+1)))

# ---- Independent order-of-magnitude audit of the real quantities in the family ----
# H (true, Mertens):  ln( ln(2Q)/ln(Q^0.9) ) ; L ~ m H^65/65! ; all-n LP optimum ~ m*H/p_min
import math
Htrue = math.log(math.log(2)*(M+1)/(math.log(2)*0.9*M))
log10m = 65*(M+1)*math.log10(2)
log10L_upper_via_S2_Hbound = log10m + 65*math.log10(0.9) - math.log10(float(factorial(65)))
log10L_true_est = log10m + 65*math.log10(Htrue) - math.log10(float(factorial(65)))
log10_Lem6cap = math.log10(1.0) + (M - math.log2(2*(M+1)*math.log(2)))*math.log10(2) + log10m - 1.8*M*math.log10(2)  # (N-1)m/Q^1.8, N~Q/(2 ln2Q)
log10_LPopt_est = log10m + math.log10(Htrue) - 0.9*M*math.log10(2)   # ~ m*H/p_min  (max spanning tree/star)
print("\n--- magnitudes for the T3 family at M=2000 (log10) ---")
print("log10 m                        =", log10m)
print("log10 L  (<= via S2 with H<0.9)=", log10L_upper_via_S2_Hbound)
print("log10 L  (true, H=%.5f)      ="%Htrue, log10L_true_est)
print("log10 Lemma-6 cap on V(c)      =", log10_Lem6cap)
print("log10 true all-n LP optimum ~  =", log10_LPopt_est)
print("=> Lemma 6 cap below L by 10^%.1f ; true LP opt below L by 10^%.1f"%(log10L_true_est-log10_Lem6cap, log10L_true_est-log10_LPopt_est))

# ---- The counter-certificate:  c_{2pq} = gamma on all pairs, feasible on the WINDOW ----
smax = math.floor(65*(M+1)/(0.9*M))
gamma = (smax-1)/ (smax*(smax-1)/2)
print("\n--- window-feasible certificate c_{2pq}=gamma ---")
print("max S0(t) for t<=m: floor(65(M+1)/(0.9M)) =", 65*(M+1)/(0.9*M), "->", smax)
print("gamma = (smax-1)/C(smax,2) = 2/smax =", gamma)
# crude rigorous value bound using ONLY Lemma 4's N >= Q/(2 log 2Q):
#  sum_{p<q} floor(m/(2pq)) >= (m/2)*C(N,2)/(2Q)^2 - C(N,2)
#  >= (m/2)* (N^2/2 - N/2)/(4Q^2) - N^2/2
logN = M*math.log10(2) - math.log10(2*(M+1)*math.log(2))
log10_val = math.log10(gamma) + log10m - math.log10(2) + (2*logN - math.log10(2)) - (2*M*math.log10(2)+math.log10(4))
print("log10 V_window(lower bd, crude) =", log10_val, "  i.e. ~10^%.1f * m"%(log10_val-log10m))
print("log10 L upper (S2, H<0.9)       =", log10L_upper_via_S2_Hbound)
print("V_window / L  >= 10^%.1f"%(log10_val-log10L_upper_via_S2_Hbound))
