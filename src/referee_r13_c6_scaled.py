# Scaled-down analogue of the Theorem A family: threshold r=2 in place of 64.
#   Q, P_r = {p prime : Q^{9/10} < p <= 2Q},  alpha_{p,1}=1,  m = (2Q)^{r+1} = (2Q)^3
#   window I = {P, ..., P+m-1},  P = prod of the selected primes
import numpy as np, math
from math import comb

def sieve(n):
    s=bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2,int(n**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]

for MM in (12,13,14):
    Q=2**MM; z=2*Q; y=Q**0.9; m=z**3
    ps=[p for p in sieve(z) if p>y]
    N=len(ps); P=np.array(ps,dtype=np.int64)
    p1,p2=ps[0],ps[1]
    assert p1**4>m, "S0(k)<=3 fails"
    # exact L = sum_{p<q<s} floor(m/(pqs))     (threshold 2: (S0-1)^+ = 1 for the S0=3 points)
    L=0
    for i in range(N-2):
        for j in range(i+1,N-1):
            d=P[i]*P[j]
            L+=int(np.sum(m//(d*P[j+1:])))
    # rigorous cap on the class-A ("(F) for all n") LP:  sum c_D <= N-1 and floor(m/D) <= m/(p1 p2)
    capA=(N-1)*(m//(p1*p2))
    # exact class-A optimum restricted to pair moduli = maximum weight spanning forest (matroid)
    W=[]
    for i in range(N-1):
        W.append(np.stack([m//(P[i]*P[i+1:]), np.full(N-1-i,i,dtype=np.int64), np.arange(i+1,N,dtype=np.int64)]))
    W=np.concatenate(W,axis=1).T
    order=np.argsort(-W[:,0],kind='stable')
    par=list(range(N))
    def find(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    mst=0; cnt=0
    for idx in order:
        w,i,j=W[idx]; a,b=find(int(i)),find(int(j))
        if a!=b: par[a]=b; mst+=int(w); cnt+=1
        if cnt==N-1: break
    # window certificate: c_{2pq} = gamma = 2/smax with smax = max S0(t), t<=m  (=3 here)
    smax=3; gamma=2.0/smax
    # support check: 2pq must divide a high point k<=m
    worst=2*ps[-1]*ps[-2]*p1
    val_win=0
    for i in range(N-1):
        val_win+=int(np.sum(m//(2*P[i]*P[i+1:])))
    val_win*=gamma
    print("Q=2^%d  z=%d  y=%.1f  N=%d  m=%.4g" % (MM,z,y,N,m))
    print("   exact L                                  = %d"%L)
    print("   class-A LP  UPPER bound (Lemma 6 style)  = %d      (< L : %s)"%(capA, capA<L))
    print("   class-A LP  exact opt on pair moduli(MST)= %d      (ratio to cap %.2f)"%(mst,mst/capA))
    print("   window-feasible cert value (c_{2pq}=2/3) = %.0f    (> L : %s, factor %.2f)"%(val_win,val_win>L,val_win/L))
    print("   support ok (max 2pq*p_min <= m): %s   L/capA = %.2f"%(worst<=m, L/capA))
