import math
from fractions import Fraction

LIM = 3_000_000
sieve = bytearray([1])*(LIM+1); sieve[0]=sieve[1]=0
for i in range(2,int(LIM**.5)+1):
    if sieve[i]: sieve[i*i::i]=bytearray(len(sieve[i*i::i]))
primes=[i for i in range(LIM+1) if sieve[i]]
pi=[0]*(LIM+1); c=0
for i in range(LIM+1):
    if sieve[i]: c+=1
    pi[i]=c
# theta
theta=[0.0]*(LIM+1); s=0.0
for i in range(LIM+1):
    if sieve[i]: s+=math.log(i)
    theta[i]=s

# Lemma 1 core: theta(n) <= 4 n log 2 for all integers n  (claimed via induction)
bad=[n for n in range(1,LIM+1) if theta[n] > 4*n*math.log(2)+1e-9]
print("Lemma1 step theta(n)<=4n log2 violations up to",LIM,":",len(bad))
print("max theta(n)/(n log2) =", max(theta[n]/(n*math.log(2)) for n in range(2,LIM+1)))
# Lemma 1 conclusion pi(y)<=8y/log y for y>=16
bad1=[y for y in range(16,LIM+1) if pi[y] > 8*y/math.log(y)+1e-9]
print("Lemma1 pi(y)<=8y/log y violations 16..%d:"%LIM, len(bad1))
print("max pi(y) log y/(8y), y in [16,LIM] =", max(pi[y]*math.log(y)/(8*y) for y in range(16,LIM+1)))
# the intermediate bound sqrt y + 8 ln2 y/ln y <= 8y/ln y  <=> ln y/sqrt y <= 8(1-ln2)
print("8(1-ln2) =", 8*(1-math.log(2)), " ln16/4 =", math.log(16)/4, " decreasing beyond e^2 ok")

# Lemma 2: pi(2Q) >= (2Q ln2 - ln(2Q+1))/ln(2Q) for integer Q>=16
worst=None
for Q in range(16, LIM//2):
    lb=(2*Q*math.log(2)-math.log(2*Q+1))/math.log(2*Q)
    r=pi[2*Q]/lb
    if worst is None or r<worst[0]: worst=(r,Q)
    if pi[2*Q] < lb-1e-9: print("Lemma2 VIOLATION at Q=",Q); break
else:
    print("Lemma2 holds for all 16<=Q<%d ; tightest ratio pi(2Q)/bound = %.4f at Q=%d"%(LIM//2,worst[0],worst[1]))

# Lemma 4 sub-claims at M=2000 (symbolic/numeric)
M=2000
print("2^(M/10) >= 2(M+1)ln2 ?", 2**(M//10) >= 2*(M+1)*math.log(2))
print("2Q ln2 - ln(2Q+1) > Q ?  (ln2>2/3 arg) 4/3 Q vs ln(2Q+1):", 4/3, " Q=2^2000 huge -> True")
# H bound arithmetic
Hb = 8/((M+1)*math.log(2)) + 8*math.log((M+1)/(0.9*M))
print("H upper bound at M=2000 =", Hb, "  claimed < 0.9:", Hb<0.9)
print("  pieces: 8/((M+1)ln2)=",8/((M+1)*math.log(2)), " <1/150=",1/150)
print("  (M+1)/(0.9M)-1 =", (M+1)/(0.9*M)-1, " vs 67/600 =", 67/600)
print("  8*67/600+1/150 =", 8*67/600+1/150)
# true H (Mertens estimate) for primes in (Q^0.9, 2Q], Q=2^2000
Htrue = math.log(math.log(2**2001)/math.log(2**1800))
print("true H ~ log(ln(2Q)/ln(Q^0.9)) =", Htrue)
