import numpy as np, random, math
exec(open('/private/tmp/claude-501/-Users-roychen-workspace-claudecode-automath/457116fb-0921-45cf-974f-013eece5c1dc/scratchpad/ref708/check2.py').read().split("random.seed")[0])
PR=primes_upto(200000)
random.seed(99); np.random.seed(99)
print("=== I. counting transfer  sum_I (S-1)^+ >= V(c)  for the S_0-baseline certificate, adversarial x ===")
worst=1e18; cnt=0; fails=0
for m in [5000, 12000, 40000]:
    cand=[int(p) for p in PR if p<=m]
    for mode in ['ones','unif','theta','mixed']:
        if mode=='ones': zmap={p:1.0 for p in cand}
        elif mode=='unif': zmap={p:random.random() for p in cand}
        elif mode=='theta': zmap={p:min(1.0,p**(-random.uniform(0.05,0.35))) for p in cand}
        else: zmap={p:random.choice([1.0,0.7,0.4,random.random(),0.05]) for p in cand}
        A0=atoms(zmap,m/64)
        H64=sum(al/pk for (p,j,pk,al) in A0)
        if H64<17/16: continue
        V=sum(al*(m//pk) for (p,j,pk,al) in A0)-(m+1)
        Vsharp=sum(al*(m//pk) for (p,j,pk,al) in A0)-m   # paper's sharper N_I(1)=m
        # adversarial windows
        big=[int(p) for p in PR if p<=60]
        prod=1
        for p in big[:6]: prod*=p
        xs=[0, m, 10*m, 10**6, 10**9, 10**12,
            (prod - 1) + prod*random.randint(1,50),
            prod*random.randint(1,100)]
        for x in xs:
            Sb=S_on_interval(x,m,zmap)
            rhs=float(np.maximum(Sb-1.0,0.0).sum())
            cnt+=1
            worst=min(worst, rhs-Vsharp)
            if rhs < V-1e-6: fails+=1; print("  FAIL", m, mode, x, rhs, V)
print(f" windows tested: {cnt}   failures of  sum_I(S-1)^+ >= V : {fails}")
print(f" min slack over the SHARPER V (= B - m, paper's Cor.\\ref{{cor:affine}}): {worst:.2f}")
