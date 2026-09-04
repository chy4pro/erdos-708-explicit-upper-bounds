from math import gcd, comb, prod
from fractions import Fraction as F

def _isp(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def nextprime(n):
    n+=1
    while not _isp(n): n+=1
    return n


def lcm_upto(M):
    r=1
    for i in range(1,M+1): r=r*i//gcd(r,i)
    return r

def test(NP, THR, M, verbose=True):
    """NP support primes, threshold THR (=NP-1), engine construction scaled."""
    qs=[]; p=M
    for _ in range(NP):
        p=nextprime(p); qs.append(p)
    a=prod(qs); m=a*M
    B=a*lcm_upto(M); x=B-(-(-m//2))
    I0,I1=x+1,x+m
    assert I0<=B<=I1
    # sparse-core-style conditions (scaled): H < (NP)/M , support q<=m/THR... engine uses m/64 -> m/THR
    H=sum(F(1,q) for q in qs)
    supp_ok=all(q<=F(m,THR) for q in qs)
    # high points: multiples of a in [1,m]
    highs=[a*t for t in range(1,M+1)]
    L=sum(1 for _ in highs)   # each S0=NP, (NP-THR)^+ = 1
    assert NP-THR==1
    # forced ones
    forced=[t for t in range(M//2+1,M+1)]
    uniq_ok=True; multcount={}
    for t in forced:
        k=a*t
        mults=[b for b in range(((I0-1)//k+1)*k, I1+1, k)]
        multcount[t]=len(mults)
        if mults!=[B]: uniq_ok=False
        assert m//k==M//t==1
    S0B=sum(1 for q in qs if B%q==0)
    # exact R over the window
    S=[0]*(m+1)
    for q in qs:
        n=((x//q)+1)*q
        while n<=I1: S[n-x]+=1; n+=q
    R=sum(v-1 for v in S[1:] if v>1)
    lb=THR*M*(M+1)**(comb(NP,2)*2//NP*0+ (NP-2))   # careful below
    # engine's bound generalised: R >= (2/NP)*C(NP,2)*M*(M+1)^{NP-2} = (NP-1)*M*(M+1)^{NP-2}
    lb=(NP-1)*M*(M+1)**(NP-2)
    if verbose:
        print(" NP=%d THR=%d M=%d: a=%d m=%d B=%d x=%d"%(NP,THR,M,a,m,B,x))
        print("   H=%s (<%d/M=%s) support q<=m/THR: %s"%(H,NP,F(NP,M),supp_ok))
        print("   #high points L=%d ; forced k_t (t>M/2): %d = ceil(M/2)=%d ; unique multiple B: %s ; mult counts %s"%(
            L,len(forced),-(-M//2),uniq_ok,sorted(set(multcount.values()))))
        print("   S0(B)=%d, capacity (S0(B)-1)^+=%d  -> overload factor >= %d/%d = %.2f"%(
            S0B,S0B-1,len(forced),S0B-1,len(forced)/(S0B-1)))
        print("   TRUE R=%d ; engine lower bound (NP-1)M(M+1)^{NP-2}=%d ; R>=bound? %s ; R/L=%.1f (bound R/L=%d)"%(
            R,lb,R>=lb,R/L,lb//L))
    return R>=lb and uniq_ok and S0B==NP

ok=True
for M in [4,5,6,7,8,10]:
    ok &= test(5,4,M)
print("\nall scaled Prop6/Lemma7 checks pass:", ok)
