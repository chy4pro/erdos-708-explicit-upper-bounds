from math import comb, factorial
from sympy import primerange, isprime
# Theorem 10 numbers
P=list(primerange(3299,6900)); n=len(P); print("primes in [3299,6899]:",n, "min two", P[:2], "max three", P[-3:])
m=P[-1]*P[-2]*P[-3]; print("m =",m)
Y=m//(P[0]*P[1]); print("Y =",Y, " W bound =",Y*(n-1), " C(n,3) =",comb(n,3), " W<L2:",Y*(n-1)<comb(n,3))
# Lemma 3 on a small instance, exact LP
import numpy as np
from scipy.optimize import linprog
Ps=[2,3,5,7]; ms=35; B=factorial(ms); I=list(range(B-ms+1,B+1))
def S0(b): return sum(1 for p in Ps if b%p==0)
Ds=list(range(1,ms+1))
# objective: maximize sum c_D floor(m/D)
c=-np.array([ms//D for D in Ds],dtype=float)
A=[];bvec=[]
for b in I:
    row=[1.0 if b%D==0 else 0.0 for D in Ds]; A.append(row); bvec.append(max(S0(b)-1,0))
res=linprog(c,A_ub=np.array(A),b_ub=np.array(bvec),bounds=[(0,None)]*len(Ds),method="highs")
print("small instance P=",Ps,"m=",ms," LP value W =",-res.fun," Lemma-3 bound Y(n-1) =",(ms//(Ps[0]*Ps[1]))*(len(Ps)-1))
# reflection check: S0(B-t)==S0(t) for 1<=t<m, S0(B)==n
print("reflection holds:", all(S0(B-t)==S0(t) for t in range(1,ms)), S0(B)==len(Ps))
# L_C and R for C=2 on this window
L2=sum(max(S0(k)-2,0) for k in range(1,ms+1)); R=sum(max(S0(b)-1,0) for b in I); print("L_2 =",L2," R =",R)
# Lemma 7 numeric sanity for a small s (not in the lemma's range) using the actual bound shape: p_{2n} <= 10 n s ?
from sympy import prime
for s in [4,6,8,10]:
    nn=2**s; print("s=%d n=%d p_{2n}=%d 10ns=%d ok=%s"%(s,nn,prime(2*nn),10*nn*s,prime(2*nn)<=10*nn*s))
