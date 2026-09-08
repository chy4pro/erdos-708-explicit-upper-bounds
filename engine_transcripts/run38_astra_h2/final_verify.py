#!/usr/bin/env python3
"""Reproduce the final mathematical constants without floating-point discovery.
Run from the repository root with python3 -B engine/out/astra_708_h2/final_verify.py.
The --full flag also reruns the complete fixed-support K4 sweep and actual families.
"""
from fractions import Fraction as F
from pathlib import Path
from itertools import product
from math import factorial,prod,comb
from collections import defaultdict
import json,sys
import fallback as f
import baseline_verifier as b
OUT=Path(__file__).resolve().parent
T=F(5337547,1000000)
C=F(280923567,32000000)

def retention():
    data=json.loads((OUT/'retention_verified.json').read_text())
    eta={int(v):e for v,e in data['ETA'].items()};vs=sorted(eta)
    maxima=[]
    for v in vs:
        dp=[None]*65;dp[0]=0
        for w in range(1,65):
            a=[dp[w-u]+eta[u] for u in vs if u>=v and u<=w and dp[w-u] is not None]
            if a:dp[w]=max(a)
        z=max(dp[w]+eta[v] for w in range(65-v,65) if dp[w] is not None)
        assert z<=480;maxima.append([v,z])
    assert maxima==data['prefix_maxima']
    for v,e in eta.items():assert F(e,720)<=min(F(1,3),F(16,27)*F(v,64))
    dp=[-10**6]*720;dp[0]=0;rewards=dict(zip(vs,vs[1:]+[64]))
    for w in range(1,720):
        dp[w]=max((dp[w-e]+rewards[v] for v,e in eta.items() if e<=w),default=-10**6)
    z,w=max((1440*a+243*(720-w),w) for w,a in enumerate(dp) if a>=0)
    assert (z,w,dp[w])==(255663,699,174)
    assert F(z,92160)==f.D0==F(28407,10240)
    assert f.D0+f.RHO*T==C<F(56501,6400) and C>8 and T>=f.TMIN
    print('final retention and threshold arithmetic PASS')

def independent_crosschecks(records):
    # Direct ordered assignment enumeration checks the polynomial convention.
    cases=0
    for L in (8,16,32):
        for j in ([8] if L==8 else range(8,16)):
            levels,rows=b.coefficient_rows(L,j)
            for k in range(1,min(4,len(rows))+1):
                hist=defaultdict(int)
                for es in product(levels,repeat=k):
                    if min(es)==j:hist[sum(es)]+=1
                assert [hist[L+d] for d in range(1,j+1)]==rows[k-1]
                cases+=1
    # Selected moment orders checked from their defining Fraction formula.
    count=0
    for rec in records:
        L,j=rec['L'],rec['j'];th=F(j,L)
        bits,hats,orders=f.envelopes(T,L,j)
        assert orders==rec['orders']
        for d,(r,hat) in enumerate(zip(orders,hats),1):
            a=(T-1-F(d,L))/th;v=int(r*a/(r-1))
            z=th*(v-a)*(f.H/th)**r*F(factorial(v-r),factorial(v))
            assert F(hat-1,1<<bits)<z<=F(hat,1<<bits)
            count+=1
    print('independent coefficient cases',cases,'selected moment bounds',count)

def main():
    retention();f.structural();f.tail()
    tab=json.loads((OUT/'fallback_discovery_5337547_1000000.json').read_text())['K']
    result=f.exact(T,tab,2048)
    assert result['C']==str(C)
    independent_crosschecks(result['records'])
    subtotals=defaultdict(F)
    for r in result['records']:subtotals[r['L']]+=F(r['value'])
    upper={L:F(b.ceildiv(z.numerator*10**12,z.denominator),10**12) for L,z in subtotals.items()}
    tail=F(json.loads((OUT/'fallback_tail.json').read_text())['total_upper'])
    total=sum(upper.values(),F(0))+tail
    assert total==F(499998420228283,500000000000000)<1
    assert 1-total==F(1579771717,500000000000000)
    # A neighboring smaller T is not established by the same bound.
    neighbor=json.loads((OUT/'fallback_exact_2668773_500000.json').read_text())
    assert F(neighbor['total'])>1 and neighbor['Lmax']==512
    full='--full' in sys.argv
    if full:
        from route_tests import analytic_tail,frontier_sweep
        analytic_tail()
        cutoff=json.loads((OUT/'antichain_tail.json').read_text())['Q_cutoff']
        row=frontier_sweep((2,3,5,7),cutoff-1)
        expected=json.loads((OUT/'frontier_complete_2357.json').read_text())
        assert row['passed'] and row['maximum']=='101/105'
        for k in ('states','intervals','limit','max_Q'):assert row[k]==expected[k]
        # Independent unswept frontiers on small Q check the interval argument.
        for Q in range(2,101):
            ps=(2,3,5,7);ladders=[]
            for p in ps:
                a=[1]
                while a[-1]<Q:a.append(a[-1]*p)
                ladders.append(a)
            value=F(0)
            for qs in product(*ladders):
                D=prod(qs)
                if D//max(qs)<Q:continue
                good=True
                for i,p in enumerate(ps):
                    if qs[i]>1:
                        pred=list(qs);pred[i]//=p
                        if prod(pred)//max(pred)>=Q:good=False;break
                if good:value+=F(Q,D)
            assert value<=1
        from certificate_audit import audit
        audit(2);audit(3)
        from adversarial import main as adversarial
        adversarial()
    summary=dict(status='PASS',threshold=str(C),total_upper=str(total),margin=str(1-total),
                 finite_scales=len(result['records']),full=full,kernel_checked=False)
    (OUT/'verification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print('FINAL PASS',summary)

if __name__=='__main__':main()
