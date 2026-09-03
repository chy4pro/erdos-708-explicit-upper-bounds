# P18 HARVEST — Erdős #708 Conjecture-S campaign, GPT-5.6 Sol Pro, chat 6a98e745, "Worked for 25m 49s", harvested 2026-09-03 22:5x CDT
# Chat: https://chatgpt.com/c/6a98e745-5404-83ea-ae48-0e3825c340f2
# VERDICT (dialogue audit, every step re-derived): T3 ACHIEVED (S itself not proved). Second explicit bound, better constants.

## Theorem. For n ≥ 2, with Λ(t) = ⌈log₂ t⌉ (least r with t ≤ 2^r):  g(n) ≤ F(n) := n(Λ(2n) + Λ(Λ(2n)) + 2) = n log₂ n + n log₂ log₂ n + O(n).

## Clean transcription (dialogue)
Notation: m = a_n, I = {x+1..x+m}. Budget H (integer), threshold T = m/H. Atoms of a: q_p(a) = p^{v_p(a)} (pairwise coprime).
Large atom: q > T (Hq > m); small atom: q ≤ T. Large atoms are individual demands. Small atoms of each a are packed by
multiplicative next-fit (increasing prime order): keep multiplying into the current bin while the product stays ≤ T; else close
the bin and start a new one with the current atom. Bins d_1..d_u per a, pairwise coprime, product of all demands of a = a.
L1 (supply/demand count). #{b ∈ I : d | b} ≥ ⌊m/d⌋ ≥ #{a ∈ A : d | a} for every d ≤ m.
L2 (next-fit). Consecutive bins of one a satisfy d_j d_{j+1} > T (bin j was closed because the next atom q did not fit: d_j q > T,
and q | d_{j+1}).
L3 (budget). Let L = #large demands, S = #small bins, D = L + S. If (B1) H ≥ n(2κ+1) and (B2) H^{(κ+1)n} ≤ 2^{κH} for integers
H, κ ≥ 1, then D ≤ H.  Case m^κ ≤ H^{κ+1}: D ≤ W = Σ ω(a); 2^{ω(a)} ≤ a ⇒ 2^W ≤ ∏a ≤ m^n ⇒ 2^{κW} ≤ m^{κn} ≤ H^{(κ+1)n} ≤ 2^{κH} ⇒ W ≤ H.
   Case m^κ > H^{κ+1}: T^{κ+1} > m. For one a with ℓ large atoms and u bins: the large atoms and the pair-products d_1d_2, d_3d_4, …
   are pairwise coprime factors of a, each > T; if ℓ + ⌊u/2⌋ ≥ κ+1 their product > T^{κ+1} > m ≥ a, contradiction; so
   ℓ + ⌊u/2⌋ ≤ κ, hence ℓ + u ≤ 2κ + 1, and D ≤ n(2κ+1) ≤ H.
L4 (parameters). r = Λ(2n), s = Λ(r), C = r + s + 2, H = nC, κ = ⌊(C−1)/2⌋. (B1): 2κ+1 ≤ C. (B2), n ≥ 3: r ≥ 3, s ≥ 2, n ≤ 2^{r−1},
   s + 2 ≤ 2^s, r ≤ 2^s ⇒ C ≤ 2^{s+1} ⇒ H ≤ 2^{r+s} = 2^{C−2}; C ≤ 2(κ+1) ⇒ (C−2)(κ+1) ≤ κC ⇒ H^{(κ+1)n} ≤ 2^{(C−2)(κ+1)n} ≤ 2^{κCn} = 2^{κH}.
   n = 2: r=2, s=1, C=5, H=10, κ=2: 10^6 ≤ 2^20.
L5 (large demands, per prime). Sort the p-demands by exponent descending; assign the j-th to the least b ∈ I with p^{e_j} | b not
   used by an earlier p-demand. Exists: the first j sources are divisible by p^{e_j}, so ⌊m/p^{e_j}⌋ ≥ j candidates, j−1 used.
   Different primes may share b. U = positions used; |U| ≤ L; at each b ∈ U at most one demand per prime, so their product | b.
L6 (small demands, globally distinct). Each bin d ≤ T = m/H has ≥ ⌊m/d⌋ ≥ H multiples in I; forbidden positions ≤ |U| + (j−1)
   ≤ L + j − 1 < H (since H ≥ D = L + S ≥ L + j); pick an unused multiple outside U.
Conclusion. c_b := product of demands at b divides b for every b ∈ B; ∏_b c_b = ∏A; so ∏A | ∏B; |B| = |U| + S ≤ L + S = D ≤ H = F(n).
§10 the Erdős–Surányi l=3 instance (H = 21, T ≈ 20.8): algorithm outputs 6 positions; the tight 4-element certificate
   B = {74290, 74081, 74086, 74083} is exhibited with per-prime capacities at u = 74290 used once each (G6 passed).
§11 Lean plan: ceilLog2 via Nat.find; Nat.factorization atoms; next-fit fold with invariant Hd ≤ m; budget cases; explicit
   multiples b_0, b_0+d, …, b_0+(H−1)d; two greedy inductions; local products c_b | b; finite product divisibility.

## Dialogue notes
- Same architecture as P17 (large atoms one-each; small atoms binned; counting) but with a purely combinatorial budget (no ω-moment
  estimate), yielding O(n log n) with small constants: F(2)=10, F(3)=21, F(4)=28, F(10)=100, F(100)=1300, F(1000)=15000.
- Combined statement: g(n) ≤ min{ n(Λ(2n)+Λ(Λ(2n))+2), ⌈48n√((81+ln n)/ln(81+ln n))⌉ } and g(n) ≤ (2+o(1)) n √(ln n/ln ln n).
- S not proved; the sharing of representatives among "medium" atoms of distinct a's remains the gap to O(n).
