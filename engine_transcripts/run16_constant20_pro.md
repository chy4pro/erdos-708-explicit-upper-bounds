# Harvest index — Erdős #708, round 9, ChatGPT Pro (GPT-5.6 Sol), chat P25

Raw: `erdos708_pro_r9_raw.md` (21,028 bytes, Chinese, 61 min). Brief: `engine/briefs/erdos708_r9_pro.md` (TEMPLATE v2.3).
Register: `PRO_CHATS_OPEN.md` P25. Status: DONE; independent referee (Opus subagent) launched 09-03 16:1x — see ledger.

## Claim
(TH_c) for ALL weights z_p ∈ [0,1], all m ≥ 3, all x ≥ 0, with c = 20 ln ln m (threshold 2 for m ≤ 2).
Consequence: g(n) ≤ (16 + 20 ln ln(8n³)) n. Improves round-8 constant 1 + 149e ln(1+ln m) (≈ 405 ln ln m) to 20 ln ln m.
Target hit: T2 of the brief (C ≤ 20). T1 (absolute constant) NOT reached — residual eH baseline in the factorial inversion.

## Structure (11 lemmas, all tagged PROVED by the engine)
1. Σ_{d ∈ D, d ≤ L} 1/d ≤ e ln(1+ln L) =: H (pairwise coprime moduli; from prime reciprocals).
2. Thinning lower bound #{n ∈ J : ν_D ≥ k} ≥ L e_k/(4(8H)^k) (θ = 1/(8H), 2-term Bonferroni, interval counts L/d−1 < N_J(d) < L/d+1).
3. Upper tail #{n ≤ L : ν_D ≥ 2k+ρ} ≤ L e_k H^ρ/ρ!.
4. Any-G factorial inversion: ρ(H,G,k) = ⌈eH + s(A)⌉, A = ln(4G) + k ln(8H), s(A) = min{A, 2A/√ln(2+A/(eH))} ⇒ ρ! ≥ 4G(8H)^k H^ρ.
5. Geometric encoding q = 51/50: k_j = ⌈q^j⌉ ≤ R−1 (Q layers), α_j = q^{−j}/50, X ≤ Σ_{j<Q} α_j N_j + R q^{1−Q}; N_j ≥ k_j ⇒ X ≥ 1.
6. Comparison: h ≥ 4 ⇒ #{n ≤ L : X ≥ B_L + 2} ≤ #{n ∈ J : X ≥ 1}, B_L = Σ α_j (2k_j + ρ_j), gain G = Q.
7. Budget: B_L + 3 < 19.24 h for h = ln(1+ln L) ≥ 4; pieces 7.538 + 2.240 + 1.734 + 6.212 + 1.515; needs the one-variable
   inequality ℓ J(h)/h < 5 (analytic for h ≥ 8; finite interval certificate on [4,8], 80 bins, max 4.966).
8. Weighted ordering identity. 9. Quotient transfer with T = 20 ln ln m − 1 (uses ln ln m ≥ 0.995 h_m; h_{L_d} < 4 ⇒ ω < 77.4 < T).
10. Peel w = E + S. 11. Small m: ln(1+ln m) < 4 ⇒ max w ≤ log₂ m ≤ 20 ln ln m (m ≥ 4); m = 3, 2, 1 by hand.

## Our independent checks (before referee)
`problems/erdos708/r9_budget_check.py`: sup (B_L+3)/h = 18.0226 (< 19.24) over L = 2^b, b ≤ 2·10⁵ sampled; factorial condition
ρ! ≥ 4G(8H)^k H^ρ holds at every layer; max ℓJ(h)/h on [4,8] = 4.9099 (< 5); tail value at h = 8: 4.6747 (< 4.677).
`problems/erdos708/constant_check.py`: with θ = 1/(4H) (Q29's idea) the exact dyadic budget gives sup (A*+1)/H = 8.97, i.e.
c ≈ 8.97e ln(1+ln m) ≈ 24 ln ln m numerically — P25's geometric layers beat it with a PROOF, not just a computation.

## Verdict pending
Referee items: Lemma 4 case analysis; Lemma 5 telescoping; Lemma 6 R ≥ 77 and R q^{1−Q} < 2; every constant in Lemma 7;
Lemma 9 (9.5)/(9.6); Lemma 11. If PASS → paper v6 §10, Zenodo v6, X, site comment, dashboard.
