#!/usr/bin/env python3
"""Explicit refutation of (NM)/(SB) [P20 round 4]: build m, x such that the window I = {x+1..x+m} contains
>= pi(m)+2 integers with no prime factor <= m/2 ("rough"). Hensley-Richards style: positions n in [-h, h+m-h),
h = m//2; stage 1 removes n = 0 mod p for p <= sqrt(m) (survivors: +-1 and +-primes in (sqrt m, m/2] and nothing else);
stage 2 for primes p in (sqrt m, m/2] removes the least populated residue class among survivors. CRT then gives x with
p | x+1+i exactly on the removed classes. Every claim is re-verified from x itself (residues of x mod p).
Usage: python3 hr_construct.py m1 m2 ...  -> writes nm_counterexample_m{m}.txt on success."""
import sys, math
import numpy as np
def primes_upto(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
for m in map(int, sys.argv[1:]):
    P=primes_upto(m//2); pi_m=len(primes_upto(m)); h=m//2
    n=np.arange(-h, m-h, dtype=np.int64)          # window positions as centred integers
    alive=np.ones(m, dtype=bool); choice={}
    r=int(math.isqrt(m))
    for p in P:
        if p<=r:
            cls=0
        else:
            res=np.mod(n[alive], p)
            cnt=np.bincount(res, minlength=p)
            cls=int(np.argmin(cnt))
        choice[p]=cls
        alive &= (np.mod(n, p)!=cls)
    surv=int(alive.sum())
    print(f"m={m}: survivors {surv} vs pi(m)+2={pi_m+2}  (stage-1 count would be {2+2*(len([p for p in P if p>r]))})", flush=True)
    if surv < pi_m+2: continue
    # CRT: x+1+i = x+1+(n+h) ≡ 0 (mod p) on the class n ≡ cls  ->  x ≡ -1-h-cls (mod p)
    x=0; M=1
    for p,cls in choice.items():
        a=(-1-h-cls)%p; t=((a-x)*pow(M,-1,p))%p; x+=M*t; M*=p
    # independent verification from x: rough positions
    rough=np.ones(m, dtype=bool); i=np.arange(m, dtype=np.int64)
    for p in P:
        xp=x%p
        rough &= (np.mod(xp+1+i, p)!=0)
    R=int(rough.sum())
    assert R==surv, (R,surv)
    # spot-check a few rough b directly with big-int trial division
    idx=np.nonzero(rough)[0][:5]
    for j in idx:
        b=x+1+int(j); assert all(b%p for p in P)
    print(f"  VERIFIED: |T| = {R} rough numbers in I (>= pi(m)+2 = {pi_m+2}); x has {len(str(x))} digits", flush=True)
    with open(f"nm_counterexample_m{m}.txt","w") as f:
        f.write(f"# (NM)/(SB) counterexample: m={m}, |T|={R} integers in I=[x+1,x+m] with no prime factor <= m/2, pi(m)={pi_m}.\n")
        f.write(f"# Hall: N(T) subset of {{1}} U primes<=m, so |N(T)| <= pi(m)+1 < |T|.\n")
        f.write(f"m={m}\npi_m={pi_m}\nT_size={R}\nx={x}\n")
    break
