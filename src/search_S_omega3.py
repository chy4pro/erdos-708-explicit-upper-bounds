#!/usr/bin/env python3
"""Targeted search for counterexamples to Conjecture S: A drawn from integers with >= 3 distinct primes (<= 210),
x from ES-style placements (a common multiple in the middle) and random. Internal cap SECONDS. Prints any infeasible."""
import sys, math, random, time
from split_assign import feasible, factor
cap = float(sys.argv[1]) if len(sys.argv) > 1 else 600
pool = [k for k in range(2, 211) if len(factor(k)) >= 3]
mixed = [k for k in range(2, 211) if len(factor(k)) >= 2]
random.seed(11); t0 = time.time(); tried = 0; bad = 0
while time.time() - t0 < cap:
    n = random.choice([3, 4, 5, 6])
    src = pool if random.random() < 0.6 else mixed
    A = sorted(random.sample(src, n)); m = max(A)
    L = math.lcm(*A)
    xs = [t * L - m // 2 for t in (1, 2)] + [t * math.lcm(*random.sample(A, min(2, n))) - m // 2 for t in (1, 3)] + [random.randrange(0, 4000)]
    for x in xs:
        if x < 0: continue
        try: r = feasible(A, x, time.time() + 15)
        except TimeoutError: continue
        tried += 1
        if not r: bad += 1; print("S INFEASIBLE:", A, x, flush=True)
print(f"omega>=3 search: tried {tried}, infeasible {bad}, {time.time()-t0:.0f}s")
