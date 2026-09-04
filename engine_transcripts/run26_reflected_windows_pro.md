# Harvest index — Erdős #708 round 14 (P31, Pro GPT-5.6 Sol, 2026-09-05 09:38–10:18 CDT, 40m15s)
Raw: erdos708_pro_r14_raw.md (Chinese). Brief: engine/briefs/erdos708_r14_pro.md (window-adapted certificates for (SC_64)). Human guidance: coordinator brief (window LP + fractional-cover dual; hot-point moment heuristics A1–A3).

## Claims (engine labels; referee verdicts pending in scratchpad/referee_708_r14.md)
- Lemma 1–2 [PROVED]: window first moment Σ_I S₀ < (1105/1024)m, |{b ∈ I : S₀(b) > 72}| < 0.015m; truncated higher moments ≤ 2mH^ℓ/ℓ!.
- Lemma 3 [PROVED] (reflected window): P = n primes ≤ m, atoms α_{p,1} = 1, B = m!, I = (B − m, B]. For D < m: D | B − D and S₀(B − D) = ω_P(D); if ω_P(D) ≤ 1 the point B − D has capacity 0, forcing c_D = 0; point B (S₀ = n, all D ≤ m divide it) forces Σ c_D ≤ n − 1; hence W(I) ≤ (n − 1)⌊m/(p₁p₂)⌋. Coordinator check: exact LP on P = {2,3,5,7}, m = 35 gives W = 10 ≤ 15 (bound), reflection identity verified.
- Lemma 4 [PROVED]: explicit dual cover of cost (n − 1)Y (y_B = Y, y_{B−t} = m if ω_P(t) ≤ 1, else 0).
- Lemma 5 [PROVED]: L_C ≥ C(n, C+1) when the product of the C+1 largest primes ≤ m.
- Theorem 6 [PROVED]: W < L_C whenever C(n, C+1) > (n − 1)⌊m/(p₁p₂)⌋, yet R ≥ L_C + C − 1 on the same window (reflection S₀(B − t) = S₀(t)): the failure is of the certificate cone, not of (SC_C).
- Lemma 7 [PROVED]: p_{2n} ≤ 10ns for n = 2^s, s ≥ 2048 (central binomial). Coordinator check: shape holds numerically for s = 4..10.
- Theorem 8 [PROVED — T3]: infinite family (n_t = 2^{2^t}, P_t = p_{n_t+1..2n_t}, m_t = p_{2n_t}^65, t ≥ 11) satisfying all (SC_64) hypotheses with W(x_t)/L_64 ≤ 20^65·65!·s_t^65/n_t → 0. Corollary 9: exactly one point with S₀ > 72 in the window.
- Theorem 10 [PROVED, exact]: C = 2 finite witness: primes in [3299, 6899] (425 of them), m = 6871·6883·6899 = 326,275,048,607, Y = 29,960, W ≤ 12,703,040 < C(425,3) = 12,704,100 ≤ L_2. Coordinator check: all numbers reproduced (sympy).
- Verdicts on the brief's heuristics: A1 correct but insufficient; A2 (cold pair + hot shadow) refuted as a universal strategy; A3 (LCM-rich hot windows are the adversary) confirmed with an exact realisation.
- Unproved: (SC_64) itself. Suggested next cone: certificates that distinguish multiples of D by position/residue class (transport structure).

## Coordinator assessment
Second barrier for the linear-for-all-n programme: P29 killed all-n certificates; P31 kills window-adapted nonnegative divisor certificates (single coefficient per modulus). On the barrier windows the inequality holds by reflection (R ≥ L + 63), so (SC_64) is untouched. The natural remaining cone is the position-dependent (transport) certificate: coefficients c_{D,b} per (modulus, multiple in I) with a K-side covering c'_D — brief r15.

## Referee (Opus, 09-05 10:4x; full report erdos708_pro_r14_referee.md)
ALL TEN CLAIMS PASS (Lemmas 1–5, 7; Theorems 6, 8, 10; Corollary 9). Cosmetic gap: "S₀(B) = n" needs p_n ≤ m (true in both applications; only S₀(B) ≤ n is used). Independent exact rational LPs on six reflected windows all satisfy Lemma 3 (one tight); Lemma 4's dual cover verified in exact integers; Theorem 10 survives exact window counts (12,703,464 < 12,704,100; exact L₂ = 30,287,189). Significance: genuine counterexample to "W(I) ≥ L for all sparse windows" — brief targets T1, T2 refuted, T4 refuted for C = 2 above m = 3.26·10^11; nothing against (SC_64). GAP (moderate, over-claim): §9 "must leave the certificate cone" is false on the family itself — the HOT-SET-EXCLUDED window LP (feasibility on I ∖ T, T = hot points, counts ⌊m/D⌋ − |T ∩ multiples|) gives value 64·L_64 on Theorem 8's family (c_D = 64 on 65-prime products) and 13.8·L₂ on Theorem 10's instance (c_{pq} = 1/3). Next question: is there a family with |T| large and W_{I∖T} < L? (Note: sympy's simplex lpmax gave wrong answers on these instances; not used.)
