# Harvest P36 — Erdős 708, the 2n conjecture via the shared-prime incidence graph (web GPT-6 Pro, 46m02s, 2026-09-08)

Chat: https://chatgpt.com/c/6aa042f5-489c-83e9-9cbb-8d1a38b173c8 (model "6 Pro" verified; brief engine/briefs/erdos708_r22_pro.md).

## OUTCOME: NO uniform improvement. T1 (2n), T2 (a counterexample), a uniform 3n and a uniform 2n+o(n) were all NOT obtained; the uniform baseline stays at our published 12n kernel-verified / 11n refereed, and the run says so explicitly. What it did produce is a substantial strengthening of the restricted incidence-graph theorem.

## CLAIMS (status CLAIMED; my exact rechecks below all pass)
C1: g(A,x) ≤ n + β(Γ) uniformly in A and x, where β is the cycle rank of the shared-prime incidence graph. No hypothesis on a_n, no primitivity, no LP, no prefix-to-window injection. SHARP in the coefficient of β: an explicit primitive connected instance has n = 3, β = 1, g = 4 = n + β.
C2: with A_core = {a ∈ A : ω(a) ≥ 3} and k = |A_core|, g(A,x) ≤ 2n − k + β_core, where β_core is the cycle rank of the incidence graph of A_core alone.
C3: hence β_core ≤ k ⟹ g(A,x) ≤ 2n. THIS IS THE ADVANCE: the previous criterion was the pseudoforest condition β ≤ c (at most one cycle per component); β_core ≤ k is materially weaker, since k counts the retained inputs and is at least the number of components.
C4: a_n ≥ 8n³ ⟹ g ≤ 2n, reproved independently of the long-interval black box.
C5: a_n ≥ 9n² ⟹ g ≤ 3n. NOTE (mine): this is NOT new — it is exactly Theorem ksplit with k = 3 in the published paper. The run appears not to have been told, or not to have used, that it was already available.
Also: an identity n + β = Ω_0(A) − |P(A)| + c with Ω_0 = Σ_a ω(a); an exact nested-shortage formula δ_p and a separate exact total-valuation shortage ρ_p ≤ δ_p with g ≤ |S| + Σ_p ρ_p(S).
Frozen gap, stated by the run: an arithmetic saving for all primitive connected critical-range instances with β_core > k.

## MY EXACT RECHECKS (independent DP + independent cycle-rank computation; ALL NINE MATCH)
| id | A | x | n | claimed g | my g | my β | n+β | 2n |
|----|---|---|---|-----------|------|------|-----|----|
| D0 | 30,42,70,105 | 0 | 4 | 4 | 4 | 5 | 9 | 8 |
| D1 | 30,42,70,105 | 113 | 4 | 4 | 4 | 5 | 9 | 8 |
| D2 | 30,42,66,70,105,165 | 151 | 6 | 5 | 5 | 8 | 14 | 12 |
| D3 | 30,42,66,70,78,105,110,165 | 997 | 8 | 5 | 5 | 11 | 19 | 16 |
| D4 | 30,42,66,70,105,110,154,165,231,385 | 1009 | 10 | 7 | 7 | 16 | 26 | 20 |
| D5 | 105,120,126,140,150,168,180 | 12510 | 7 | 5 | 5 | 11 | 18 | 14 |
| D6 | 330,420,462,630,770,1155 | 13282 | 6 | 4 | 4 | 14 | 20 | 12 |
| D7 | 30,42,70,165,273 | 29900 | 5 | 3 | 3 | 5 | 10 | 10 |
| MAX | 77,91,143 | 5934 | 3 | 4 | 4 | 1 | 4 | 6 |
Every claimed optimum reproduces under my own exhaustive DP (problems/erdos708/repo/src/gn_dp.py), every β matches my own computation from the bipartite incidence graph, g ≤ n + β holds in all nine, and the sharpness instance is exactly tight: 77 = 7·11, 91 = 7·13, 143 = 11·13 gives β = 1 and g = 4 = n + β. Maximum ratio over the run's retained instances is 4/3, consistent with the earlier campaign's 973-instance search.

## DECISION
Refereeing this: it claims a materially wider sufficient condition than the pseudoforest one, which was my stated trigger. If confirmed, C1–C3 replace the pseudoforest remark in a future paper version. Still no bound change, so per the corrected cadence: GitHub only, no Zenodo, no X.
