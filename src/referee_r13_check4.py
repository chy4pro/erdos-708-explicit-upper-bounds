import numpy as np, random, math
exec(open('/private/tmp/claude-501/-Users-roychen-workspace-claudecode-automath/457116fb-0921-45cf-974f-013eece5c1dc/scratchpad/ref708/check2.py').read().split("random.seed")[0])
PR=primes_upto(400000)
print("=== C. adversarial extremes for Lemma 5: mass pushed onto p^j just below m/64 ===")
print(f"{'m':>8} {'strategy':<26} {'H64':>7} {'cap/m':>8} {'slack/m':>9} {'>=1+1983/65536':>15} {'maxS0':>7}")
for m in [8192, 30000, 100000, 300000]:
    B=m/64
    for strat in ['top primes only','top pp only','2-adic+top','uniform 1/p tail']:
        cand=[int(p) for p in PR if p<=B]
        if strat=='top primes only':
            zmap={}; H=0.0
            for p in sorted(cand,reverse=True):
                if H>=17/16+1e-12: break
                zmap[p]=1.0; H+=1.0/p
        elif strat=='top pp only':
            # use prime powers p^j<=B with j>=1, prefer largest p^j
            pp=[]
            for p in cand:
                pk=p; j=1
                while pk<=B: pp.append((pk,p,j)); pk*=p; j+=1
            pp.sort(reverse=True)
            zmap={}; H=0.0; used=set()
            for pk,p,j in pp:
                if H>=17/16+1e-12: break
                if p in used: continue
                used.add(p); zmap[p]=1.0/j if j>1 else 1.0
                # h_p ~ alpha/p^j approx; recompute exactly below
                H=0.0
                for (pp2,jj,pkk,al) in atoms(zmap,B): H+=al/pkk
        elif strat=='2-adic+top':
            zmap={2:1.0}; H=0.5
            for p in sorted(cand,reverse=True):
                if H>=17/16+1e-12: break
                if p==2: continue
                zmap[p]=1.0; H+=1.0/p
        else:
            zmap={}; H=0.0
            for p in cand:
                if H>=17/16+1e-12: break
                zmap[p]=1.0; H+=1.0/p
        A0=atoms(zmap,B)
        H64=sum(al/pk for (p,j,pk,al) in A0)
        if H64<17/16-1e-12: print(f"{m:>8} {strat:<26} {H64:7.4f}   (cannot reach 17/16)"); continue
        S0=np.zeros(m+1)
        for (p,j,pk,al) in A0: S0[pk::pk]+=al
        cap=float(np.minimum(S0[1:],64.0).sum())
        print(f"{m:>8} {strat:<26} {H64:7.4f} {cap/m:8.5f} {(cap-m)/m:9.5f} {str(cap>=(1+1983/65536)*m-1e-6):>15} {S0[1:].max():7.3f}")
