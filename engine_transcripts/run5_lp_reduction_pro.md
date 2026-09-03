# P19 HARVEST — Erdős #708 round 3 (bounded regime a_n < 8n³), GPT-5.6 Sol Pro, chat 6a98f93b, "Worked for 239m 59s", harvested 2026-09-04 03:5x CDT (page text; answer in Chinese)
# VERDICT (dialogue audit): NO new theorem. Its "staircase theorem" m^κ ≥ ((2κ+1)n)^{κ+1} ⇒ g ≤ (2κ+1)n IS Theorem D with k = 2κ+1 (identical threshold); corollaries 9n² ⇒ 3n, (5n)^{3/2} ⇒ 5n, (7n)^{4/3} ⇒ 7n coincide with Theorem D's k = 3, 5, 7.
# NEW and useful: a clean reduction of an absolute-constant linear bound (T2) to one inequality.

## The LP reduction (dialogue-checked)
Let P = primes dividing ∏A, r = |P|, R_p = Σ_a v_p(a). Bounded fractional cover LP: τ* = min Σ_b y_b s.t. Σ_b v_p(b) y_b ≥ R_p (p ∈ P), 0 ≤ y_b ≤ 1. Feasible (y ≡ 1 since ∏A | ∏I).
L2.1 (duality, checked): τ* = max_{z ≥ 0} [ Σ_{a∈A} w_z(a) − Σ_{b∈I} (w_z(b) − 1)⁺ ], w_z(k) = Σ_p z_p v_p(k).
L2.2 (checked): the max is attained with 0 ≤ z_p ≤ 1 (for t = z_p ≥ 1 every b with p | b has w ≥ 1, so the objective is linear in t with slope R_p − S_p ≤ 0, S_p = Σ_{b∈I} v_p(b) ≥ R_p by G1 summed over prime powers).
L2.3 (checked): if m < 8n³ then r < 16n (∏_{j≤r} p_j ≤ ∏A ≤ m^n < (8n³)^n and (16n+1)! > (8n)^{8n} > (8n³)^n).
L2.4 (checked, standard): an optimal extreme point has ≤ r fractional coordinates; rounding them up gives an integral B with ∏A | ∏B and |B| ≤ τ* + r.
Bounded Hinge inequality (BH), UNPROVED: for all A ⊆ [1,m], all intervals I of length m, all 0 ≤ z_p ≤ 1:
   Σ_{a∈A} (w(a) − 2)⁺ ≤ Σ_{b∈I} (w(b) − 1)⁺.
   Since Σ_a w(a) ≤ 2n + Σ_a (w(a)−2)⁺, (BH) gives τ* ≤ 2n and hence |B| ≤ 2n + r < 18n for m < 8n³; with Theorem C for m ≥ 8n³: g(n) ≤ 18n.
Stronger A-independent form (TH), UNPROVED: Σ_{k=1}^{m} (w(k) − 2)⁺ ≤ Σ_{b=x+1}^{x+m} (w(b) − 1)⁺ for all x ≥ 0, m ≥ 1, 0 ≤ z_p ≤ 1.
   (TH) ⇒ (BH) because A ⊆ [1,m]. Sanity: z supported on one prime: LHS = Σ_{j≥3}⌊m/p^j⌋ ≤ Σ_{j≥2} #{b∈I: p^j | b} = RHS ✓.
Also: unique-multiple core lemmas (4.1 unique multiple ⇒ a > m/2; 4.2 residual after the common multiple u splits into ≤ 2k factors ≤ m/2, two per row, coprime within a row; 4.3 offset criterion q | u+t ⟺ q | t for q | Λ) — a precise but unclosed list-colouring/offset assignment gap. Registry of rejected reasoning (multiset vs set, SDR from per-divisor counts, etc.) consistent with G9.

## Dialogue decision
Not publishable as a theorem. (TH) is a crisp, self-contained inequality about additive functions on intervals — a good round-4 target: proving (TH) gives g(n) ≤ 18n, the first linear bound with an absolute constant. Test (TH)/(BH) numerically first (random z, m, x); if no counterexample, dispatch P20/Q24 on (TH).
