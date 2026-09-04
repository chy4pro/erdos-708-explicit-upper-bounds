# End-to-end on an enumerable window: threshold r=2 analogue.
import numpy as np, itertools
def sieve(n):
    s=bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2,int(n**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]
Q=2**7; z=2*Q; y=Q**0.9
ps=[p for p in sieve(z) if p>y]; N=len(ps); m=z**3
P=1
for p in ps: P*=p
print("Q=%d z=%d y=%.2f  primes=%s  N=%d  m=%d  P=%d"%(Q,z,y,ps,N,m,P))
assert ps[0]**4>m, (ps[0]**4,m)
# exact L on {1..m}
S0=np.zeros(m+1,dtype=np.int8)
for p in ps: S0[p::p]+=1
L=int(np.sum(np.maximum(S0[1:m+1].astype(np.int64)-2,0)))
# exact R on I={P,...,P+m-1}:  S0(P)=N, S0(P+t)=S0(t)
R=(N-1)+int(np.sum(np.maximum(S0[1:m].astype(np.int64)-1,0)))
print("L=%d  R=%d   R>=L: %s   (Lemma 8 analogue)"%(L,R,R>=L))
print("max S0(t), t<=m :", int(S0[1:m+1].max()))
print("P odd:", P%2==1, "  gcd(P,6)=1:", P%2 and P%3)
# class-A cap and MST
capA=(N-1)*(m//(ps[0]*ps[1]))
mstw=sorted([(m//(ps[i]*ps[j]),i,j) for i in range(N) for j in range(i+1,N)],reverse=True)
par=list(range(N))
def find(x):
    while par[x]!=x: par[x]=par[par[x]]; x=par[x]
    return x
mst=0
for w,i,j in mstw:
    a,b=find(i),find(j)
    if a!=b: par[a]=b; mst+=w
# window certificate value, and a DIRECT verification of feasibility on every b in I
smax=int(S0[1:m+1].max()); gamma=2.0/smax
val=gamma*sum(m//(2*ps[i]*ps[j]) for i in range(N) for j in range(i+1,N))
# direct check: for every b in I, sum_{D|b} c_D <= (S0(b)-1)^+
pairs=[(ps[i],ps[j]) for i in range(N) for j in range(i+1,N)]
viol=0; maxlhs=0
t=np.arange(0,m,dtype=np.int64)
lhs=np.zeros(m,dtype=np.float64)
for (a,b) in pairs:
    d=2*a*b
    off=(-P)%d            # positions t with d | P+t
    lhs[off::d]+=gamma
cap=np.maximum(S0[0:m].astype(np.float64)-1,0)   # (S0(P+t)-1)^+ for t>=1 ; fix t=0 separately
cap[0]=N-1
bad=np.where(lhs>cap+1e-9)[0]
print("window-cert direct feasibility over all %d elements of I: violations = %d"%(m,len(bad)))
print("certificate value  = %.1f   sum over b in I of assigned mass = %.1f  (<= R = %d : %s)"%(val,lhs.sum(),R,lhs.sum()<=R))
print("class-A cap = %d ; class-A exact (pairs, MST) = %d ; L = %d ; window cert = %.1f"%(capA,mst,L,val))
