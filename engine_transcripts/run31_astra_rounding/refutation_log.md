# Exact refutation ledger

**PROVED:** the raw Section 7 LP has explicit instances with G=n and tau*=n/K. Its additive loss is n(1−1/K), so a uniform o(n) loss and every fixed bound G≤alpha tau*+C are false. This proves a positive linear loss; it does not prove a superlinear loss or refute additive n.

All artifacts are confined to this directory. No git or internet was used. The numerical optimizer proposes rational solutions; every LP optimum below is certified independently by exact primal feasibility, exact dual feasibility, and equality of rational objectives. Full A,x, primal offsets/weights, dual weights, exact G and integral witnesses are stored in `refutation_results.jsonl`, one attempted job per line.

80 attempted jobs, 75 records with exact G, 73 distinct instances. Five initial HR jobs exceeded the DP state cap; all five were subsequently settled exactly by an integral cover of size ceil(tau*) and the verified rational dual lower bound. No unresolved optimum or LP certificate failure remains.

The capped valuation DP in the prior campaign was imported read-only. It is the exact 0/1 dynamic program, with identical-column compression and integer arithmetic. Three small records were also rechecked with the unmodified repository gn_dp.min_B. HR repairs use exact upper/lower certificates, not numerical MIP lower bounds.

Maximum observed normalized loss: **99/100**. It is attained for every K=100 spike test n=1,...,12. At n=12: A=[101,103,107,109,113,127,131,137,139,149,151,157], m=157, spike offsets 78,...,89, tau*=3/25, G=12, loss=297/25. The exact x is the least nonnegative CRT solution x≡p_i^100−(78+i) mod p_i^101 (i=0,...,11), retained in the JSONL.

Largest nonspike normalized loss: **7/18**, A=[323, 391, 437], x=88930, tau*=17/6, G=4.

## Spike proof and asymptotic scope

Choose n distinct primes p_i with maximum m and min p_i>(m+n)/2. Let distinct offsets t_i lie in the integer interval [m−min p_i+1,min p_i]. By CRT choose x≡p_i^K−t_i modulo p_i^(K+1). Then x+t_i has p_i-adic valuation exactly K and is the unique multiple of p_i in (x,x+m]. Distinct t_i ensure every demand row has a distinct unique available column. With A={p_i}, each demand is one, so every integral cover contains all n columns, and exactly those n columns suffice. The unique fractional requirements are y_(x+t_i)≥1/K, giving tau*=n/K. Dual weights z_(p_i)=1/K attain the same value with zero hinge penalty.

An elementary arbitrary-n selection is supplied and independently audited in theory.md: search bands [Q,4Q/3) with Q≥6n. If all sufficiently late geometric bands contained fewer than n primes, the sum of prime reciprocals would converge, contradicting the Euler-product proof of its divergence. This proves termination of an explicit prime-band search. Taking K=n yields tau*=1 and G=n, hence unbounded multiplicative gap and additive gap n−1. Taking K arbitrarily large shows no universal coefficient c<1 can satisfy G≤tau*+c n+C. The finite certificates require no prime-distribution assumption.

## Every attempted instance

Row is the 1-based line number in refutation_results.jsonl. Each row preserves the exact A,x and witnesses; a failed DP attempt stays visible even after its repair.

| Row | Family | n | tau* | G | (G−tau*)/n | Status |
|---:|---|---:|---:|---:|---:|---|
| 1 | known_record | 3 | 3 | 4 | 1/3 | exact DP + rational LP |
| 2 | known_record | 4 | 65/18 | 5 | 25/72 | exact DP + rational LP |
| 3 | known_record | 5 | 83/18 | 6 | 5/18 | exact DP + rational LP |
| 4 | ES_prior_ES_n3_extend | 3 | 3 | 4 | 1/3 | exact DP + rational LP |
| 5 | ES_prior_ES_n3_extend | 3 | 3 | 4 | 1/3 | exact DP + rational LP |
| 6 | ES_prior_ES_n3_extend | 3 | 17/6 | 4 | 7/18 | exact DP + rational LP |
| 7 | ES_prior_ES_n3_extend | 3 | 3 | 4 | 1/3 | exact DP + rational LP |
| 8 | ES_prior_ES_center | 6 | 6 | 6 | 0 | exact DP + rational LP |
| 9 | ES_prior_ES_hybrid | 6 | 11/2 | 6 | 1/12 | exact DP + rational LP |
| 10 | ES_prior_ES_random_crt | 6 | 6 | 6 | 0 | exact DP + rational LP |
| 11 | ES_prior_ES_large_extend | 6 | 6 | 6 | 0 | exact DP + rational LP |
| 12 | ES_prior_ES_center | 10 | 23/2 | 12 | 1/20 | exact DP + rational LP |
| 13 | ES_prior_ES_large_extend | 10 | 23/2 | 12 | 1/20 | exact DP + rational LP |
| 14 | ES_prior_ES_large_extend | 10 | 11 | 12 | 1/10 | exact DP + rational LP |
| 15 | ES_prior_ES_large_record_recheck | 10 | 23/2 | 12 | 1/20 | exact DP + rational LP |
| 16 | reflected_factorial | 3 | 1/2 | 1 | 1/6 | exact DP + rational LP |
| 17 | random_CRT | 3 | 13/6 | 3 | 5/18 | exact DP + rational LP |
| 18 | reflected_factorial | 4 | 1/4 | 1 | 3/16 | exact DP + rational LP |
| 19 | random_CRT | 4 | 229/104 | 3 | 83/416 | exact DP + rational LP |
| 20 | reflected_factorial | 5 | 2/5 | 1 | 3/25 | exact DP + rational LP |
| 21 | random_CRT | 5 | 135/52 | 3 | 21/260 | exact DP + rational LP |
| 22 | reflected_factorial | 6 | 1/2 | 1 | 1/12 | exact DP + rational LP |
| 23 | random_CRT | 6 | 109/30 | 4 | 11/180 | exact DP + rational LP |
| 24 | reflected_factorial | 7 | 1/2 | 1 | 1/14 | exact DP + rational LP |
| 25 | random_CRT | 7 | 4 | 4 | 0 | exact DP + rational LP |
| 26 | reflected_factorial | 8 | 1 | 1 | 0 | exact DP + rational LP |
| 27 | random_CRT | 8 | 81/20 | 5 | 19/160 | exact DP + rational LP |
| 28 | reflected_factorial | 9 | 1 | 1 | 0 | exact DP + rational LP |
| 29 | random_CRT | 9 | 152/27 | 6 | 10/243 | exact DP + rational LP |
| 30 | reflected_factorial | 10 | 1 | 1 | 0 | exact DP + rational LP |
| 31 | random_CRT | 10 | 25/4 | 7 | 3/40 | exact DP + rational LP |
| 32 | reflected_factorial | 11 | 1 | 1 | 0 | exact DP + rational LP |
| 33 | random_CRT | 11 | 57/8 | 8 | 7/88 | exact DP + rational LP |
| 34 | reflected_factorial | 12 | 1 | 1 | 0 | exact DP + rational LP |
| 35 | random_CRT | 12 | 101/15 | 7 | 1/45 | exact DP + rational LP |
| 36 | HR_unicyclic | 4 | 1512/695 | 3 | 573/2780 | exact DP + rational LP |
| 37 | HR_private_star | 12 | 77/32 | — | — | LP exact; integer DP excluded |
| 38 | HR_random_n3_0 | 3 | 77/32 | 3 | 19/96 | exact DP + rational LP |
| 39 | HR_random_n3_1 | 3 | 17/8 | 3 | 7/24 | exact DP + rational LP |
| 40 | HR_random_n3_2 | 3 | 213/112 | 3 | 41/112 | exact DP + rational LP |
| 41 | HR_random_n3_3 | 3 | 559/256 | 3 | 209/768 | exact DP + rational LP |
| 42 | HR_random_n8_0 | 8 | 573/128 | 5 | 67/1024 | exact DP + rational LP |
| 43 | HR_random_n8_1 | 8 | 9/2 | 5 | 1/16 | exact DP + rational LP |
| 44 | HR_random_n8_2 | 8 | 41/7 | 6 | 1/56 | exact DP + rational LP |
| 45 | CRT_unique_spike_K10 | 1 | 1/10 | 1 | 9/10 | exact DP + rational LP |
| 46 | CRT_unique_spike_K100 | 1 | 1/100 | 1 | 99/100 | exact DP + rational LP |
| 47 | CRT_unique_spike_K10 | 2 | 1/5 | 2 | 9/10 | exact DP + rational LP |
| 48 | CRT_unique_spike_K100 | 2 | 1/50 | 2 | 99/100 | exact DP + rational LP |
| 49 | CRT_unique_spike_K10 | 3 | 3/10 | 3 | 9/10 | exact DP + rational LP |
| 50 | CRT_unique_spike_K100 | 3 | 3/100 | 3 | 99/100 | exact DP + rational LP |
| 51 | CRT_unique_spike_K10 | 4 | 2/5 | 4 | 9/10 | exact DP + rational LP |
| 52 | CRT_unique_spike_K100 | 4 | 1/25 | 4 | 99/100 | exact DP + rational LP |
| 53 | CRT_unique_spike_K10 | 5 | 1/2 | 5 | 9/10 | exact DP + rational LP |
| 54 | CRT_unique_spike_K100 | 5 | 1/20 | 5 | 99/100 | exact DP + rational LP |
| 55 | CRT_unique_spike_K10 | 6 | 3/5 | 6 | 9/10 | exact DP + rational LP |
| 56 | CRT_unique_spike_K100 | 6 | 3/50 | 6 | 99/100 | exact DP + rational LP |
| 57 | CRT_unique_spike_K10 | 7 | 7/10 | 7 | 9/10 | exact DP + rational LP |
| 58 | CRT_unique_spike_K100 | 7 | 7/100 | 7 | 99/100 | exact DP + rational LP |
| 59 | CRT_unique_spike_K10 | 8 | 4/5 | 8 | 9/10 | exact DP + rational LP |
| 60 | CRT_unique_spike_K100 | 8 | 2/25 | 8 | 99/100 | exact DP + rational LP |
| 61 | CRT_unique_spike_K10 | 9 | 9/10 | 9 | 9/10 | exact DP + rational LP |
| 62 | CRT_unique_spike_K100 | 9 | 9/100 | 9 | 99/100 | exact DP + rational LP |
| 63 | CRT_unique_spike_K10 | 10 | 1 | 10 | 9/10 | exact DP + rational LP |
| 64 | CRT_unique_spike_K100 | 10 | 1/10 | 10 | 99/100 | exact DP + rational LP |
| 65 | CRT_unique_spike_K10 | 11 | 11/10 | 11 | 9/10 | exact DP + rational LP |
| 66 | CRT_unique_spike_K100 | 11 | 11/100 | 11 | 99/100 | exact DP + rational LP |
| 67 | CRT_unique_spike_K10 | 12 | 6/5 | 12 | 9/10 | exact DP + rational LP |
| 68 | CRT_unique_spike_K100 | 12 | 3/25 | 12 | 99/100 | exact DP + rational LP |
| 69 | HR_random_n8_3 | 8 | 89/24 | 4 | 7/192 | exact DP + rational LP |
| 70 | HR_random_n12_0 | 12 | 19/4 | — | — | LP exact; integer DP excluded |
| 71 | HR_random_n12_1 | 12 | 638/105 | — | — | LP exact; integer DP excluded |
| 72 | HR_random_n12_2 | 12 | 7 | — | — | LP exact; integer DP excluded |
| 73 | HR_random_n12_3 | 12 | 425/56 | — | — | LP exact; integer DP excluded |
| 74 | repair_HR_private_star | 12 | 77/32 | 3 | 19/384 | EXACT: rational LP lower bound rounds to verified integral cover |
| 75 | repair_HR_random_n12_0 | 12 | 19/4 | 5 | 1/48 | EXACT: rational LP lower bound rounds to verified integral cover |
| 76 | repair_HR_random_n12_1 | 12 | 638/105 | 7 | 97/1260 | EXACT: rational LP lower bound rounds to verified integral cover |
| 77 | repair_HR_random_n12_2 | 12 | 7 | 7 | 0 | EXACT: rational LP lower bound rounds to verified integral cover |
| 78 | repair_HR_random_n12_3 | 12 | 425/56 | 8 | 23/672 | EXACT: rational LP lower bound rounds to verified integral cover |
| 79 | R5_cycle_loss_refutation | 4 | 3/10 | 1 | 7/40 | exact DP + rational LP |
| 80 | R3_level_value_obstruction | 2 | 1 | 1 | 0 | exact DP + rational LP |

## R3 exact-instance ledger

These 13 additional jobs are retained in the R3-owned `r3_exact.jsonl` and independently checked here for their raw LP and integral optima. They include one instance duplicated by the main ledger. Row identifies its JSONL line; all exact A,x and original/level witnesses are in that artifact.

| R3 row | n | A | x | tau_raw | G | tau_cap | tau_level | G_level |
|---:|---:|---|---|---:|---:|---:|---:|---:|
| 1 | 2 | powers 2^1,...,2^2 | 4 | 1 | 1 | 1 | 2 | 2 |
| 2 | 1 | powers 2^1,...,2^1 | 2^10−2^1 | 1/10 | 1 | 1 | 1 | 1 |
| 3 | 2 | powers 2^1,...,2^2 | 2^30−2^2 | 1/10 | 1 | 1 | 2 | 2 |
| 4 | 3 | powers 2^1,...,2^3 | 2^60−2^3 | 1/10 | 1 | 1 | 3 | 3 |
| 5 | 4 | powers 2^1,...,2^4 | 2^100−2^4 | 1/10 | 1 | 1 | 4 | 4 |
| 6 | 5 | powers 2^1,...,2^5 | 2^150−2^5 | 1/10 | 1 | 1 | 5 | 5 |
| 7 | 6 | powers 2^1,...,2^6 | 2^210−2^6 | 1/10 | 1 | 1 | 6 | 6 |
| 8 | 7 | powers 2^1,...,2^7 | 2^280−2^7 | 1/10 | 1 | 1 | 7 | 7 |
| 9 | 8 | powers 2^1,...,2^8 | 2^360−2^8 | 1/10 | 1 | 1 | 8 | 8 |
| 10 | 9 | powers 2^1,...,2^9 | 2^450−2^9 | 1/10 | 1 | 1 | 9 | 9 |
| 11 | 10 | powers 2^1,...,2^10 | 2^550−2^10 | 1/10 | 1 | 1 | 10 | 10 |
| 12 | 11 | powers 2^1,...,2^11 | 2^660−2^11 | 1/10 | 1 | 1 | 11 | 11 |
| 13 | 12 | powers 2^1,...,2^12 | 2^780−2^12 | 1/10 | 1 | 1 | 12 | 12 |

Reproduction: run `python3 -B engine/out/astra_708_rounding/refutation_verify.py` for the independent rational verifier and ledger. The search generator used the existing interpreter `/Users/roychen/workspace/claudecode/hfreqtrade/venv/bin/python -B` with `engine/out/astra_708_rounding/refutation_exact.py` modes `baseline`, `spikes`, `repair`, and `route_witnesses`. Search modes append to the attempted-job ledger; the verifier does not append.

Independent mathematical audit completed: theory.md P1 exact CRT theorem and prime-band termination, P2 strict vertex rounding, F1 nonlaminar and determinant obstructions, F2 cycle-excess comparison counterexample; r2_large_prime_bounds.md support counts, explicit prime-count error, and resulting bounds 20n−2 and 19n+pi(2n)−1. All arguments checked without an unresolved logical step.

## R4 route assessment

**PROVED / target settled:** explicit positive linear rounding loss, approaching coefficient one; **REFUTED:** uniform sublinear additive rounding, and fixed multiplicative rounding with additive constant. **OPEN:** G≤tau*+n; no tested case refutes it. **REFUTED:** the ES prior record can be explained by zero rounding loss; its exact optimum is tau*=17/6 versus G=4. **OPEN:** a family with tau*≈n and G≥1.5n; the spike construction settles a stronger multiplicative separation with tau* much smaller, but does not have that normalization.

Gap: The exact CRT spike family settles linear-loss T2 and refutes sublinear and fixed multiplicative rounding, while the universal additive-n upper bound remains unproved and unrefuted.
