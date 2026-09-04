from decimal import Decimal as D
from math import factorial, log, ceil, sqrt, exp, lgamma
# log of RHS of (8.1)
def lrhs(N):
    return log(N/3.0)+log1m6(N)+lgamma(2*N+2)-(2*N+1)*log(17/16)
def log1m6(N):
    return log(1-6.0**(1-N))
print("N=32: log10 m_max = 32*log10(rhs) =", 32*lrhs(32)/log(10), " (published 2887.455)")
print("\nLemma 16: (8.1) => log m <= 3N^2 log(3N)")
for N in [2,3,5,10,32,100,1000,10**4,10**6]:
    lm=N*lrhs(N); bnd=3*N*N*log(3*N)
    print("  N=%-8d log m_max=%.5g  3N^2log(3N)=%.5g  ok=%s"%(N,lm,bnd,lm<=bnd))
print("\nCorollary 15 / (8.3):")
bad=0; bad2=0; X=exp(8)
for e in range(0,500):
    X=exp(8)*(1.05**e); N=ceil(3*sqrt(X/log(X)))
    if not (X <= N*lrhs(N)): bad+=1
    if not (X/N+(2*N+1)/16+log(4) <= (N+2)*log(N)): bad2+=1
print("  (8.1) failures: %d ; (8.3) failures: %d  (X from e^8=%.4g to %.4g)"%(bad,bad2,exp(8),X))
for l10 in [1294,2942,10**6]:
    Xv=l10*log(10); N=ceil(3*sqrt(Xv/log(Xv))); print("  log10 m=%-8s -> N=%d threshold 2N=%d"%(l10,N,2*N))
print("\nLemma 14 packing order:")
for order,lab in [([0.66,0.66,0.7],'arbitrary order'),([0.7,0.66,0.66],'heavy leftover first')]:
    s=0
    for a in order:
        s+=a
        if s>4/3: break
    print("  %-22s closed-group mass = %.4f  (<=2 : %s)"%(lab,s,s<=2))
