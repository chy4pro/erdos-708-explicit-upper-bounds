#!/usr/bin/env python3
"""Root's independent exact audit of retained finite certificates.

Only writes final_verification.json beside this file. Run with python3 -B.
Optimality for non-spike DP jobs also uses the exhaustive DP recurrence described
in report.md; this verifier checks their retained covers, not a new DP run.
"""
from fractions import Fraction as Q
from pathlib import Path
import collections
import hashlib
import json
import math
import sys

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(1000000)
OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]


def val(a, p):
    assert a > 0
    j = 0
    while a % p == 0:
        j += 1
        a //= p
    return j


def factor(a):
    result = {}
    p = 2
    while p*p <= a:
        while a % p == 0:
            result[p] = result.get(p, 0) + 1
            a //= p
        p += 1
    if a > 1:
        result[a] = result.get(a, 0) + 1
    return result


def read(name):
    return [json.loads(s) for s in (OUT/name).read_text().splitlines()]


rows = read('refutation_results.jsonl')
unique = {}
dp_claims = 0
structurally_certified = 0
for r in rows:
    assert r.get('status') != 'FAILED'
    A, x, m = r['A'], r['x'], r['m']
    assert x >= 0 and A == sorted(set(A)) and min(A) > 1 and m == max(A)
    demand = collections.Counter()
    for a in A:
        demand.update(factor(a))
    ps = sorted(demand)
    assert ps == r['primes'] and [demand[p] for p in ps] == r['need']
    y = {t: Q(q) for t, q in r['primal']}
    assert len(y) == len(r['primal'])
    assert all(1 <= t <= m and 0 < q <= 1 for t, q in y.items())
    for p in ps:
        assert sum(val(x+t, p)*q for t, q in y.items()) >= demand[p]
    z = dict(zip(ps, map(Q, r['dual'])))
    assert len(r['dual']) == len(ps) and all(0 <= q <= 1 for q in z.values())
    active = [(p, q) for p, q in z.items() if q]
    penalty = sum(max(Q(0), sum(q*val(x+t, p) for p, q in active)-1)
                  for t in range(1, m+1))
    tau = Q(r['tau'])
    assert sum(y.values()) == tau == sum(z[p]*demand[p] for p in ps)-penalty
    key = (tuple(A), x)
    if 'g' in r:
        B = r['witness']
        assert len(B) == len(set(B)) == r['g']
        assert all(x < b <= x+m for b in B)
        assert all(sum(val(b, p) for b in B) >= demand[p] for p in ps)
        assert Q(r['gap']) == r['g']-tau
        assert Q(r['gap_per_n']) == (r['g']-tau)/len(A)
        if r['family'].startswith('CRT_unique_spike'):
            positions = [[t for t in range(1, m+1) if (x+t) % p == 0] for p in ps]
            assert all(len(v) == 1 for v in positions)
            assert len({v[0] for v in positions}) == len(A) == r['g']
            K = int(r['family'].split('K')[-1])
            assert all(val(x+v[0], p) == K for p, v in zip(ps, positions))
            assert tau == Q(len(A), K)
            structurally_certified += 1
        elif r['family'].startswith('repair_'):
            assert r['g'] == math.ceil(tau)
            structurally_certified += 1
        else:
            dp_claims += 1
    if key not in unique or 'g' in r:
        unique[key] = r

assert all('g' in r for r in unique.values())
r3 = read('r3_exact.jsonl')
for r in r3:
    A, x, K = r['A'], r['x'], r['K']
    n, m = len(A), max(A)
    assert A == [2**j for j in range(1, n+1)]
    R = n*(n+1)//2
    assert K >= R and max(val(x+t, 2) for t in range(1, m+1)) == K
    assert Q(r['tau_raw']) == Q(R, K)
    B = r['original_witness']
    assert len(B) == r['g'] == 1 and x < B[0] <= x+m and val(B[0], 2) >= R
    assert Q(r['tau_cap']) == 1
    L = r['level_witness']
    assert len(L) == len(set(L)) == r['g_level'] == n
    assert all(x < b <= x+m for b in L)
    for j in range(1, n+1):
        assert sum(val(b, 2) >= j for b in L) >= n-j+1
    assert Q(r['tau_level']) == n
    key = (tuple(A), x)
    if key in unique:
        assert unique[key]['g'] == 1 and Q(unique[key]['tau']) == Q(r['tau_raw'])
    unique[key] = dict(r, tau=r['tau_raw'], gap_per_n=str((1-Q(r['tau_raw']))/n))

maxgap = max(Q(r['gap_per_n']) for r in unique.values())
assert maxgap == Q(99, 100)
assert len(rows)+len(r3) == 93 and len(unique) == 85
sources = ['engine/briefs/erdos708_rounding_astra.md', 'papers/erdos708/main.tex',
           'papers/erdos708/sec_h17.tex', 'problems/erdos708/repo/src/gn_dp.py',
           'engine/harvest/astra_708_2n.md', 'engine/out/astra_708_2n/refutation_search.py']
result = dict(status='PASS', attempted_jobs=len(rows)+len(r3), distinct_instances=len(unique),
              maximum_normalized_raw_gap=str(maxgap), all_distinct_optima_settled=True,
              rational_LP_certificates_checked=len(rows), R3_exact_checks=len(r3),
              spike_or_repair_optimality_rechecked=structurally_certified,
              other_DP_records_with_verified_covers=dp_claims,
              source_sha256={p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources})
(OUT/'final_verification.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
