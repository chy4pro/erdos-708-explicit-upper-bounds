"""Exact, standard-library-only verifier. No network, floating point, or LP.
Run with --all-scan-witnesses to print every witness in the finite scans.
"""

from itertools import combinations

from math import gcd, prod

from fractions import Fraction

import sys

def factor(n):
    out = {}
    d = 2
    while d*d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out

def valuation(n, p):
    e = 0
    while n % p == 0:
        e += 1
        n //= p
    return e

def graph_data(A):
    fs = [factor(a) for a in A]
    Q = sorted(p for p in set().union(*(set(f) for f in fs))
               if sum(p in f for f in fs) >= 2)
    adj = [[i for i,f in enumerate(fs) if p in f] for p in Q]
    match = {}
    def augment(j, seen):
        for i in adj[j]:
            if i not in seen:
                seen.add(i)
                if i not in match or augment(match[i], seen):
                    match[i] = j
                    return True
        return False
    nu = sum(augment(j, set()) for j in range(len(Q)))
    parent = list(range(len(A)+len(Q)))
    def root(u):
        while parent[u] != u:
            parent[u] = parent[parent[u]]
            u = parent[u]
        return u
    for j, nb in enumerate(adj):
        for i in nb:
            parent[root(i)] = root(len(A)+j)
    c = len({root(i) for i in range(len(parent))})
    W = sum(map(len, adj))
    return Q, W, nu, c, W-len(A)-len(Q)+c

def exact_dp(A, x):
    """0/1 DP; equal capped valuation vectors are grouped without reuse."""
    m = max(A)
    fs = [factor(a) for a in A]
    ps = sorted(set().union(*(set(f) for f in fs)))
    D = tuple(sum(f.get(p,0) for f in fs) for p in ps)
    groups = {}
    for b in range(x+1, x+m+1):
        v = tuple(min(t,valuation(b,p)) for p,t in zip(ps,D))
        if any(v):
            groups.setdefault(v,[]).append(b)
    # A vector never needs more than max ceil(D_p/v_p) identical items.
    dp = {tuple(0 for _ in D): ()}
    for v, bs in sorted(groups.items(), key=lambda kv: (-sum(kv[0]),kv[0])):
        cap = min(len(bs), max((t+e-1)//e for t,e in zip(D,v) if e))
        new = dict(dp)
        for state, witness in dp.items():
            for k in range(1, cap+1):
                ns = tuple(min(t,s+k*e) for t,s,e in zip(D,state,v))
                w = witness + tuple(bs[:k])
                if ns not in new or len(w)<len(new[ns]):
                    new[ns] = w
        dp = new
    B = tuple(sorted(dp[D]))
    assert len(B)==len(set(B)) and all(x<b<=x+m for b in B)
    assert all(sum(valuation(b,p) for b in B)>=t for p,t in zip(ps,D))
    return len(B),B,tuple(ps),D,len(dp)

def anchor_data(A, x):
    fs = [factor(a) for a in A]
    ps = sorted(set().union(*(set(f) for f in fs)))
    groups = {}
    for a in A:
        b = ((x//a)+1)*a
        groups.setdefault(b, []).append(a)
    S = tuple(sorted(groups))
    delta = {}
    for p in ps:
        E = max(f.get(p,0) for f in fs)
        delta[p] = max([0]+[sum(f.get(p,0)>=j for f in fs)
                    - sum(valuation(b,p)>=j for b in S)
                    for j in range(1,E+1)])
    cert = len(S)+sum(delta.values())
    beta = graph_data(A)[-1]
    local_betas = sum(graph_data(tuple(C))[-1] for C in groups.values())
    assert cert <= len(A)+local_betas <= len(A)+beta
    return S,delta,cert,local_betas

def repair_data(A,x,S):
    fs=[factor(a) for a in A]
    ps=sorted(set().union(*(set(f) for f in fs)))
    rho={}
    for p in ps:
        demand=sum(f.get(p,0) for f in fs)
        need=max(0,demand-sum(valuation(b,p) for b in S))
        vals=sorted((valuation(b,p) for b in range(x+1,x+max(A)+1) if b not in S),reverse=True)
        k=0
        while need>0:
            need-=vals[k]; k+=1
        rho[p]=k
    return rho,len(S)+sum(rho.values())

def adaptive_cover(A,x):
    remain=list(A); S=set(); seen=set(); done=[]
    while remain:
        a=next((a for a in remain if set(factor(a))&seen),remain[0])
        remain.remove(a); done.append(a)
        fresh=next((b for b in range((x//a+1)*a,x+max(A)+1,a) if b not in S),None)
        if fresh is not None:
            S.add(fresh)
        else:
            fs=[factor(t) for t in done]
            for p in factor(a):
                E=max(f.get(p,0) for f in fs)
                delta=max([0]+[sum(f.get(p,0)>=j for f in fs)-sum(valuation(b,p)>=j for b in S) for j in range(1,E+1)])
                assert delta<=1
                if delta:
                    b=max((b for b in range(x+1,x+max(A)+1) if b not in S),key=lambda b:(valuation(b,p),-b))
                    S.add(b)
        seen.update(factor(a))
        for p in seen:
            E=max(valuation(t,p) for t in done)
            assert all(sum(valuation(b,p)>=j for b in S)>=sum(valuation(t,p)>=j for t in done) for j in range(1,E+1))
    assert len(S)<=len(A)+graph_data(A)[-1]
    return tuple(sorted(S))

def packed_cover(A,x,k):
    n=len(A); m=max(A); h=k*n
    assert k in (2,3)
    assert m >= (8*n**3 if k==2 else 9*n*n)
    big={}; small=[]
    def pack(atoms):
        bins=[1]*k
        def go(i):
            if i==len(atoms):return True
            tried=set()
            for j in range(k):
                if bins[j] not in tried and bins[j]*atoms[i]*h<=m:
                    tried.add(bins[j]); bins[j]*=atoms[i]
                    if go(i+1):return True
                    bins[j]//=atoms[i]
            return False
        assert go(0)
        return [b for b in bins if b>1]
    for a in A:
        fs=factor(a); large=[(p,e) for p,e in fs.items() if p**e*h>m]
        assert len(large)<=1
        if large:
            p,e=large[0];big.setdefault(p,[]).append(e)
            f=a//p**e
            if f>1:small.append(f)
            assert f*h<=m
        else:
            small.extend(pack(sorted((p**e for p,e in fs.items()),reverse=True)))
    S=set()
    for p,es in big.items():
        bs=sorted(range(x+1,x+m+1),key=lambda b:(-valuation(b,p),b))[:len(es)]
        assert all(valuation(b,p)>=e for b,e in zip(bs,sorted(es,reverse=True)))
        S.update(bs)
    for f in small:
        b=next(b for b in range((x//f+1)*f,x+m+1,f) if b not in S)
        S.add(b)
    assert len(S)<=h
    assert prod(S)%prod(A)==0
    return tuple(sorted(S))


A0 = (30,42,70,105)
A1 = (30,42,66,70,105,165)
A2 = (30,42,66,70,78,105,110,165)
A3 = (30,42,66,70,105,110,154,165,231,385)
A4 = (105,120,126,140,150,168,180)
A5 = (330,420,462,630,770,1155)
A6 = (30,42,70,165,273)
CASES = [
    ("D0", A0, 0, 4, (56,75,84,105)),
    ("D1", A0, 113, 4, (168,189,200,210)),
    ("D2", A1, 151, 5, (176,250,294,297,315)),
    ("D3", A2, 997, 5, (1050,1100,1134,1144,1155)),
    ("D4", A3, 1009, 7, (1029,1100,1155,1188,1232,1375,1386)),
    ("H0", A0, 8, 4, (56,75,84,105)),
    ("H1", A1, 16, 5, (135,147,165,175,176)),
    ("D5", A4, 12510, 5, (12544,12600,12625,12663,12690)),
    ("D6", A5, 13282, 4, (13365,13552,13750,14406)),
    ("D7", A6, 29900, 3, (29988,30000,30030)),
    ("D8", A0, 1207, 3, (1225,1260,1296)),
    ("T", (77,91,143), 5934, 4, (5941,5954,5978,6050)),
    ("F", (6,10,21), 53, 2, (60,63)),
    ("U0", (6,10,15), 53, 3, (54,55,60)),
    ("U1", (154,273,715), 29672, 3, (29744,30030,30135)),
    ("U2", (154,273,715), 0, 3, (462,546,715)),
    ("R0", (6,10,15), 0, 3, (10,12,15)),
    ("R1", (6,14,21), 0, 3, (14,18,21)),
    ("R2", (15,21,35), 0, 3, (15,21,35)),
    ("R3", (35,55,77), 0, 3, (35,55,77)),
    ("R4", (30,70,105), 0, 3, (84,100,105)),
]
SCANS = [
    (A0, range(0,211,7), (4,0,(56,75,84,105))),
    ((6,10,15), range(900), (3,0,(10,12,15))),
    ((6,14,21), range(2000), (3,0,(14,18,21))),
    ((15,21,35), range(2000), (3,0,(15,21,35))),
    ((35,55,77), range(2000), (3,0,(35,55,77))),
    ((30,70,105), range(2000), (3,0,(84,100,105))),
]
PACK_CASES = [
    ((154,273,715),29672,2,(29673,29674,29678,29705,29722,29757)),
    ((30,42,105,200),1009,3,(1010,1011,1015,1016,1020,1022,1035,1125)),
    ((30,105),8,2,(10,15,20,21)),
    ((30,165),16,2,(20,30,33)),
    ((30,42,105),8,3,(9,10,12,14,15,18,21)),
    ((30,42,165),16,3,(18,21,22,28,30,45)),
]

def valid(A,x,B):
    assert len(B)==len(set(B))
    assert all(x<b<=x+max(A) for b in B)
    assert prod(B)%prod(A)==0


def sift(A):
    P=tuple(sorted(set().union(*(set(factor(a)) for a in A))))
    L=prod(P); m=max(A)
    good=[int(gcd(i,L)==1) for i in range(L+m)]
    count=sum(good[1:m+1]); prefix=count; best=(count,0)
    for x in range(1,L):
        count+=good[x+m]-good[x]
        if count>best[0]:best=(count,x)
    survivors=tuple(b for b in range(best[1]+1,best[1]+m+1) if gcd(b,L)==1)
    return P,prefix,best,survivors


def main():
    maximum=Fraction(0)
    for name,A,x,want,B in CASES:
        got=exact_dp(A,x)
        assert got[0]==want and got[1]==B
        valid(A,x,B)
        maximum=max(maximum,Fraction(want,len(A)))
        print("EXACT",name,"A",A,"x",x,"graph",graph_data(A),"DP",got)
    assert maximum==Fraction(4,3)
    print("MAXIMUM_RETAINED_RATIO",maximum)
    for A,beta in [(A0,5),(A1,8),(A2,11),(A3,16),(A4,11),(A5,14),(A6,5)]:
        assert gcd(*A)==1 and all(b%a for a,b in combinations(A,2))
        assert all(len(factor(a))>=3 for a in A)
        assert 2*len(A)<max(A)<8*len(A)**3
        assert graph_data(A)[3:]==(1,beta)
    for A,want in [(A0,(24,(26,8))),(A1,(34,(37,16)))]:
        result=sift(A)
        assert result[1:3]==want
        print("SIFT",result)
    for name,A,x,want,B in CASES:
        data=anchor_data(A,x)
        rho,cost=repair_data(A,x,data[0])
        assert all(rho[p]<=data[1][p] for p in rho)
        adaptive=adaptive_cover(A,x)
        valid(A,x,adaptive)
        print("CERT",name,data,"RHO",rho,cost,"ADAPTIVE",adaptive)
    assert anchor_data(A4,12510)[2]==18
    assert repair_data(A4,12510,(12600,))==({2:2,3:2,5:2,7:2},9)
    for a in A4:
        assert tuple(range((12510//a+1)*a,12691,a))==(12600,)
    best=10**9; minimizer=None
    for mask in range(1<<len(A5)):
        C=tuple(a for i,a in enumerate(A5) if mask>>i&1)
        bound=len(C)+graph_data(C)[-1]+sum(len(factor(a)) for i,a in enumerate(A5) if not(mask>>i&1))
        if bound<best:best,minimizer=bound,C
    assert (best,minimizer)==(20,(330,420))
    print("SUBSET_BOUND_MINIMUM",best,minimizer)
    for A,x,k,B in PACK_CASES:
        assert packed_cover(A,x,k)==B
        valid(A,x,B)
        print("PACK",A,x,k,B)
    all_witnesses="--all-scan-witnesses" in sys.argv
    for A,xs,want in SCANS:
        best=(0,None,None)
        for x in xs:
            ans=exact_dp(A,x)
            if all_witnesses:print("SCAN_WITNESS",A,x,ans[:2])
            if ans[0]>best[0]:best=(ans[0],x,ans[1])
        assert best==want
        print("EXHAUSTIVE_FINITE_SCAN",A,(xs.start,xs.stop,xs.step),len(xs),best)
    assert sum(len(xs) for A,xs,want in SCANS)==8931
    print("ALL_CHECKS_PASSED")


if __name__=="__main__":
    main()