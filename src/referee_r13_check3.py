import numpy as np, random, math
exec(open('/private/tmp/claude-501/-Users-roychen-workspace-claudecode-automath/457116fb-0921-45cf-974f-013eece5c1dc/scratchpad/ref708/check2.py').read().split("random.seed")[0])

random.seed(7); np.random.seed(7)
PR=primes_upto(300000)

def build(m, zmap):
    S=S_on_1m(m,zmap)
    A_all=atoms(zmap,m); A0=[a for a in A_all if a[2]<=m/64]
    S0=np.zeros(m+1)
    for (p,j,pk,al) in A0: S0[pk::pk]+=al
    return S,S0,A0

def greedy_Q(A0):
    hp={}
    for (p,j,pk,al) in A0: hp[p]=hp.get(p,0.0)+al/pk
    ps=sorted(hp)
    Q=[]; tot=0.0
    for p in ps:
        if tot>=17/16: break
        Q.append(p); tot+=hp[p]
    return Q,tot,hp

def moments(m,A0,Q):
    Qs=set(Q)
    T=np.zeros(m+1)
    Up={p:np.zeros(m+1) for p in Q}
    for (p,j,pk,al) in A0:
        if p in Qs:
            T[pk::pk]+=al; Up[p][pk::pk]+=al
    return T,Up

print("=== B. Lemma 5 moment bounds on the greedy Q + counting transfer (Prop cert) ===")
print(f"{'m':>7} {'mode':<7} {'H_Q':>7} {'B_Q/m':>8} {'>=63/64 HQ':>11} {'M2/m':>8} {'<=H+H^2':>9} {'capmin/m':>9} {'>=67519/65536':>13} {'Umax':>6} {'V':>11} {'RHS_I min':>12} {'transfer':>8}")
cases=[]
for m in [5000, 9000, 20000, 64000]:
    for mode in ['ones','unif','theta','mixed']:
        cand=[int(p) for p in PR if p<=m]
        if mode=='ones': zmap={p:1.0 for p in cand}
        elif mode=='unif': zmap={p:random.random() for p in cand}
        elif mode=='theta':
            th=random.uniform(0.05,0.4); zmap={p:min(1.0,p**(-th)) for p in cand}
        else: zmap={p:random.choice([1.0,0.7,0.4,random.random(),0.05]) for p in cand}
        S,S0,A0=build(m,zmap)
        Q,HQ,hp=greedy_Q(A0)
        if HQ<17/16:  # dense hypothesis fails
            print(f"{m:>7} {mode:<7} {HQ:7.4f}   (H64<17/16: sparse branch)"); continue
        T,Up=moments(m,A0,Q)
        BQ=float(T[1:].sum()); M2=float((T[1:]**2).sum())
        cap=float(np.minimum(T[1:],64.0).sum())
        Umax=max(float(Up[p][1:].max()) for p in Q)
        # certificate value for S_0 baseline
        V=sum(al*(m//pk) for (p,j,pk,al) in A0)-(m+1)
        # actual RHS over random windows
        rhs=[]
        for _ in range(6):
            x=random.choice([0, random.randint(0,10**6), random.randint(0,10**9),
                             m*random.randint(1,50)])
            Sb=S_on_interval(x,m,zmap)
            rhs.append(float(np.maximum(Sb-1.0,0.0).sum()))
        ok1=BQ>=63/64*HQ*m-1e-6
        ok2=M2<=m*(HQ+HQ*HQ)+1e-6
        ok3=cap>=67519/65536*m-1e-6
        ok4=min(rhs)>=V-1e-6
        print(f"{m:>7} {mode:<7} {HQ:7.4f} {BQ/m:8.4f} {str(ok1):>11} {M2/m:8.4f} {str(ok2):>9} {cap/m:9.4f} {str(ok3):>13} {Umax:6.3f} {V:11.1f} {min(rhs):12.1f} {str(ok4):>8}")
