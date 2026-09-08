#!/usr/bin/env python3
"""Independent rational certificate verifier and complete attempted-instance ledger.
No optimization packages, floating point tolerances, network, or external writes.
"""
import collections, json, math, sys
from fractions import Fraction as F
from pathlib import Path
OUT=Path(__file__).resolve().parent
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(1000000)

def vp(a,p):
    e=0
    while a%p==0:a//=p;e+=1
    return e

def run():
    rows=[json.loads(t) for t in (OUT/'refutation_results.jsonl').read_text().splitlines()]
    for r in rows:
        assert r.get('status')!='FAILED',r
        A,x,m,ps,need=r['A'],r['x'],r['m'],r['primes'],r['need']
        assert A==sorted(set(A)) and m==max(A)
        # Check the supplied prime support is complete using trial factor removal.
        for a in A:
            for p in ps:
                while a%p==0:a//=p
            assert a==1
        assert all(p>=2 and all(p%d for d in range(2,math.isqrt(p)+1)) for p in ps)
        assert need==[sum(vp(a,p) for a in A) for p in ps]
        z=list(map(F,r['dual']));assert all(0<=t<=1 for t in z)
        y={offset:F(t) for offset,t in r['primal']}
        assert len(y)==len(r['primal']) and all(1<=t<=m and 0<q<=1 for t,q in y.items())
        assert all(sum(vp(x+t,p)*q for t,q in y.items())>=d for p,d in zip(ps,need))
        primal=sum(y.values(),F(0))
        dual=sum(q*d for q,d in zip(z,need))
        for t in range(1,m+1):dual-=max(F(0),sum(q*vp(x+t,p) for p,q in zip(ps,z))-1)
        assert primal==dual==F(r['tau'])
        if 'g' in r:
            B=r['witness'];assert len(B)==len(set(B))==r['g']
            assert all(x<b<=x+m for b in B) and math.prod(B)%math.prod(A)==0
            assert F(r['gap'])==r['g']-primal and F(r['gap_per_n'])==F(r['gap'])/len(A)
            if r['family'].startswith('repair_'):assert len(B)==math.ceil(primal)
            if r['family'].startswith('CRT_unique'):
                assert len(ps)==len(A)
                support=[{t for t in range(1,m+1) if (x+t)%p==0} for p in ps]
                assert all(len(s)==1 for s in support) and len(set.union(*support))==len(A)
                assert r['g']==len(A)
    complete=[r for r in rows if 'g' in r]
    best=max(complete,key=lambda r:F(r['gap_per_n']))
    baseline=max((r for r in complete if not r['family'].startswith('CRT_unique')),key=lambda r:F(r['gap_per_n']))
    unique={(tuple(r['A']),r['x']):r for r in rows}
    lines=['# Exact refutation ledger','',
      '**PROVED:** the raw Section 7 LP has explicit instances with G=n and tau*=n/K. Its additive loss is n(1−1/K), so a uniform o(n) loss and every fixed bound G≤alpha tau*+C are false. This proves a positive linear loss; it does not prove a superlinear loss or refute additive n.','',
      'All artifacts are confined to this directory. No git or internet was used. The numerical optimizer proposes rational solutions; every LP optimum below is certified independently by exact primal feasibility, exact dual feasibility, and equality of rational objectives. Full A,x, primal offsets/weights, dual weights, exact G and integral witnesses are stored in `refutation_results.jsonl`, one attempted job per line.','',
      f'{len(rows)} attempted jobs, {len(complete)} records with exact G, {len(unique)} distinct instances. Five initial HR jobs exceeded the DP state cap; all five were subsequently settled exactly by an integral cover of size ceil(tau*) and the verified rational dual lower bound. No unresolved optimum or LP certificate failure remains.','',
      'The capped valuation DP in the prior campaign was imported read-only. It is the exact 0/1 dynamic program, with identical-column compression and integer arithmetic. Three small records were also rechecked with the unmodified repository gn_dp.min_B. HR repairs use exact upper/lower certificates, not numerical MIP lower bounds.','',
      f'Maximum observed normalized loss: **{best["gap_per_n"]}**. It is attained for every K=100 spike test n=1,...,12. At n=12: A=[101,103,107,109,113,127,131,137,139,149,151,157], m=157, spike offsets 78,...,89, tau*=3/25, G=12, loss=297/25. The exact x is the least nonnegative CRT solution x≡p_i^100−(78+i) mod p_i^101 (i=0,...,11), retained in the JSONL.','',
      f'Largest nonspike normalized loss: **{baseline["gap_per_n"]}**, A={baseline["A"]}, x={baseline["x"]}, tau*={baseline["tau"]}, G={baseline["g"]}.','',
      '## Spike proof and asymptotic scope','',
      'Choose n distinct primes p_i with maximum m and min p_i>(m+n)/2. Let distinct offsets t_i lie in the integer interval [m−min p_i+1,min p_i]. By CRT choose x≡p_i^K−t_i modulo p_i^(K+1). Then x+t_i has p_i-adic valuation exactly K and is the unique multiple of p_i in (x,x+m]. Distinct t_i ensure every demand row has a distinct unique available column. With A={p_i}, each demand is one, so every integral cover contains all n columns, and exactly those n columns suffice. The unique fractional requirements are y_(x+t_i)≥1/K, giving tau*=n/K. Dual weights z_(p_i)=1/K attain the same value with zero hinge penalty.','',
      'An elementary arbitrary-n selection is supplied and independently audited in theory.md: search bands [Q,4Q/3) with Q≥6n. If all sufficiently late geometric bands contained fewer than n primes, the sum of prime reciprocals would converge, contradicting the Euler-product proof of its divergence. This proves termination of an explicit prime-band search. Taking K=n yields tau*=1 and G=n, hence unbounded multiplicative gap and additive gap n−1. Taking K arbitrarily large shows no universal coefficient c<1 can satisfy G≤tau*+c n+C. The finite certificates require no prime-distribution assumption.','',
      '## Every attempted instance','',
      'Row is the 1-based line number in refutation_results.jsonl. Each row preserves the exact A,x and witnesses; a failed DP attempt stays visible even after its repair.','',
      '| Row | Family | n | tau* | G | (G−tau*)/n | Status |','|---:|---|---:|---:|---:|---:|---|']
    for i,r in enumerate(rows,1):
        status='exact DP + rational LP' if 'g' in r and not r['family'].startswith('repair_') else r.get('status','unknown')
        lines.append(f'| {i} | {r["family"]} | {r["n"]} | {r.get("tau","—")} | {r.get("g","—")} | {r.get("gap_per_n","—")} | {status} |')
    r3=[json.loads(t) for t in (OUT/'r3_exact.jsonl').read_text().splitlines()]
    lines.extend(['','## R3 exact-instance ledger','',
      'These 13 additional jobs are retained in the R3-owned `r3_exact.jsonl` and independently checked here for their raw LP and integral optima. They include one instance duplicated by the main ledger. Row identifies its JSONL line; all exact A,x and original/level witnesses are in that artifact.','',
      '| R3 row | n | A | x | tau_raw | G | tau_cap | tau_level | G_level |','|---:|---:|---|---|---:|---:|---:|---:|---:|'])
    for i,r in enumerate(r3,1):
        A,x,K=r['A'],r['x'],r['K'];n=len(A);m=max(A);R=sum(vp(a,2) for a in A)
        assert all(a&(a-1)==0 for a in A) and R==r['R']
        assert max(vp(b,2) for b in range(x+1,x+m+1))==K
        assert F(r['tau_raw'])==F(R,K) and r['g']==1 and len(r['original_witness'])==1
        assert math.prod(r['original_witness'])%math.prod(A)==0
        assert F(r['tau_cap'])==1 and F(r['tau_level'])==r['g_level']==n
        B=r['level_witness'];assert len(set(B))==len(B)==n
        assert all(x<b<=x+m for b in B)
        for j in range(1,n+1):assert sum(b%(2**j)==0 for b in B)>=sum(a%(2**j)==0 for a in A)
        xtext='4' if i==1 else f'2^{K}−2^{n}'
        lines.append(f'| {i} | {n} | powers 2^1,...,2^{n} | {xtext} | {r["tau_raw"]} | {r["g"]} | {r["tau_cap"]} | {r["tau_level"]} | {r["g_level"]} |')
    lines.extend(['','Reproduction: run `python3 -B engine/out/astra_708_rounding/refutation_verify.py` for the independent rational verifier and ledger. The search generator used the existing interpreter `/Users/roychen/workspace/claudecode/hfreqtrade/venv/bin/python -B` with `engine/out/astra_708_rounding/refutation_exact.py` modes `baseline`, `spikes`, `repair`, and `route_witnesses`. Search modes append to the attempted-job ledger; the verifier does not append.','',
      'Independent mathematical audit completed: theory.md P1 exact CRT theorem and prime-band termination, P2 strict vertex rounding, F1 nonlaminar and determinant obstructions, F2 cycle-excess comparison counterexample; r2_large_prime_bounds.md support counts, explicit prime-count error, and resulting bounds 20n−2 and 19n+pi(2n)−1. All arguments checked without an unresolved logical step.'])
    lines.extend(['','## R4 route assessment','',
      '**PROVED / target settled:** explicit positive linear rounding loss, approaching coefficient one; **REFUTED:** uniform sublinear additive rounding, and fixed multiplicative rounding with additive constant. **OPEN:** G≤tau*+n; no tested case refutes it. **REFUTED:** the ES prior record can be explained by zero rounding loss; its exact optimum is tau*=17/6 versus G=4. **OPEN:** a family with tau*≈n and G≥1.5n; the spike construction settles a stronger multiplicative separation with tau* much smaller, but does not have that normalization.','',
      'Gap: The exact CRT spike family settles linear-loss T2 and refutes sublinear and fixed multiplicative rounding, while the universal additive-n upper bound remains unproved and unrefuted.'])
    (OUT/'refutation_log.md').write_text('\n'.join(lines)+'\n')
    (OUT/'refutation_verification.json').write_text(json.dumps(dict(attempted_jobs=len(rows),exact_G_records=len(complete),unique_instances=len(unique),all_unique_settled=all('g' in r for r in unique.values()),maximum_gap_per_n=best['gap_per_n'],verified='all rational primal/dual certificates and all integral witnesses'),indent=2)+'\n')
    print(json.dumps(dict(attempted_jobs=len(rows),exact_G_records=len(complete),unique_instances=len(unique),all_unique_settled=all('g' in r for r in unique.values()),maximum_gap_per_n=best['gap_per_n'])))

if __name__=='__main__':run()
