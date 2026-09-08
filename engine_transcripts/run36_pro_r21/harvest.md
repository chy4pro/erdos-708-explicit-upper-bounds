# Harvest P35 — Erdős 708, (H_2) by induction on the number of primes (web GPT-6 Pro, 49m41s, 2026-09-08)

Chat: https://chatgpt.com/c/6aa01e8e-9a84-83ea-87d5-20a3de3f3485 (model "6 Pro" verified; brief engine/briefs/erdos708_r21_pro.md).

## OUTCOME: T1 NOT REACHED. The largest N for which (H_2) is proved for UNRESTRICTED atom systems is still N = 4. No counterexample. The global bound is unchanged: g(n) ≤ 12n kernel-verified, 11n refereed, threshold interval [2, 8.83]. What the run produced is a set of restricted theorems and one genuine impossibility result.

## NEW RESULTS (status CLAIMED; my exact rechecks below all pass)
T4 (five primes, one multilevel): (H_2) holds for every system with at most five active primes in which at most ONE prime carries more than one nonzero atom; weights arbitrary real, and the exceptional prime may carry arbitrarily many levels. In particular it covers five arbitrary primes with one arbitrary prime power each. Method: "elimination" — write S = T + f with T on four coprime moduli and f on the fifth prime; the layer identity (T+f−a)^+ − (T−a)^+ = ∫_0^1 [f > t][T > a−t] dt turns the fifth prime into a divisor condition [d | n] for each layer, and a Boolean antichain bound (Lemma 2 below) charges the layer's left-hand count to ⌊m/(dQ(t))⌋, which the window dominates.
L2 (Boolean antichain / Kraft bound): for pairwise coprime a<b<c<d ≥ 2 and Q ≥ 2, the minimal subsets A whose product-divided-by-largest-element is ≥ Q satisfy Q·Σ_A 1/∏A ≤ 1. Proved by an exhaustive nine-row case table; the extremal row is 2·e_2(1/2,1/3,1/5,1/7) = 101/105 < 1.
T5 (per-prime cap, ALL N): for every N ≥ 2, (H_2) holds whenever there are at most N active primes each of total weight at most 2/(N−1). The certificate is cyclic: G(f) = Σ_{r<N} max(0, min(λ/N, min_i (f_i − λ·((r+i) mod N)/N))) with λ = 2/(N−1), which equals λ·P(Z_i ≤ f_i ∀i) for shifted uniforms — the union bound gives the lower hinge and a branch-length computation the upper one. At five equal half-weights it has value 1/2 exactly where the pair certificate collapses to 0.
L6 (grids): (H_2) for five primes whenever all cumulative weights lie in {0,1/q,…,1} with q = 6 or q = 8; proved by exact finite certificates over 462 and 1287 sorted cases.
L7 (IMPOSSIBILITY — the structurally important one): there is NO pointwise nonnegative "threshold rectangle" certificate on {0,1/2,1}^6 sandwiched between (S−2)^+ and (S−1)^+. Counting: the upper bound kills constants, singletons and the (1/2,1/2) pairs; then P+T+H ≤ 5 at the all-ones state and 4P+T ≥ 20 by summing the twenty states with three ones; these force T = H = 0, and at the all-half state G = 0 < 1/2. So beyond five primes any certificate must be signed, or must dominate only after summation.
L8 (the exact bridge, OPEN): a four-prime analogue K_4 of the Kraft bound for prime-power "projection frontiers" would give unrestricted five primes; it is verified finitely (primes 2,3,5,7 for Q ≤ 300; all 4-subsets of the first six primes for Q ≤ 60) but OPEN. The run also REFUTES the five-prime analogue: 2·e_2(1/2,1/3,1/5,1/7,1/11) = 194/165 > 1, so even K_4 would not continue the induction.
METHODOLOGICAL POINT: T4's certificate dominates the left hinge only AFTER summation over [1,m], not pointwise — the run exhibits its own explicit five-prime certificate failing pointwise at n = 12705 (1948 < 2625). Its right-hand domination is pointwise and all divisor coefficients are nonnegative.

## MY EXACT RECHECKS (all pass)
2e_2(1/2,1/3,1/5,1/7) = 101/105 < 1 ✓; 3e_2(1/3,1/4,1/5,1/7) = 131/140 ✓; the b = 5 row 179/210 ✓; the five-prime refutation 2e_2(…,1/11) = 194/165 > 1 ✓; the cyclic certificate sandwich on 4,629 grid points for N = 2,3,4,5,6 with no violation, and its value 1/2 at five half-weights ✓; the third-difference facts from my own brief ✓; L7's counting identity 4P+T = 4(P+T+H) − 3T − 4H ✓.

## SEARCH SCOPE (the run's own, not verified by me yet)
190,246,980 window instances over five to eight primes (all starts, selected lengths; all lengths for N = 5), of which 127,514,310 satisfy the G_2 region conditions — no counterexample. Selection of weight systems is heuristic; enumeration of starts is exhaustive.

## DECISION
Worth refereeing (T4, T5, L7 are publishable; L8's refutation of the five-prime Kraft analogue is a useful negative). Not published today — v14 went out this morning and Section 19 is already staged for v15 on 09-09; if the referee confirms, T4/T5/L7 join that section. Astra frozen until 13 Sep, so nothing here can be formalised this week.
