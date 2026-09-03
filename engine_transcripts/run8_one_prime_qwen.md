# Q25 HARVEST — #708 round 5, (PQ′) building blocks (Qwen3.8-Max, ~30 min, harvested 07:54 CDT 09-04 via Copy)
# Chat: https://chat.qwen.ai/c/556970ee-742f-438f-8fa6-75fecdcd15dc   Raw: erdos708_qwen_r5_raw.md
# Verdict: T2 PROVED (one prime, every 0 ≤ z ≤ 1, every a ≥ 0, every interval): dialogue audit PASS.
## Content
- L1 interval multiples: ⌊L/d⌋ ≤ #{i∈J : d|i} ≤ ⌊L/d⌋+1 (floor identity, r+s < 2d). VALID.
- L2 telescoping: for nonincreasing φ on ℕ, Σ_{n∈I} φ(v_p(n)) = |I|φ(0) − Σ_t Δ_t #{n∈I : p^t | n}. VALID.
- L3 t ↦ f_a(zt) nonincreasing (a = 0 convention f_0(0) = 1). VALID.
- L4 (the key, STRONGER than asked): Σ_J f_a(z v_p(i)) ≤ Σ_{i≤L} f_a(z v_p(i)) — same-threshold domination holds for ONE prime for
  any nonincreasing function of the valuation, because the interval has ≥ ⌊L/p^t⌋ multiples of every p^t. VALID (sanity test
  19514 random instances, 0 failures).
- L5 f_a ≤ g_a pointwise. VALID.  Thm 6 = L4 + L5 ⇒ (PQ′) for one prime. VALID.
- a > 1 budget form: margin = Σ_{i≤L} (g_a − f_a)(z v_p(i)) ≥ L(g_a(0) − f_a(0)) with explicit values (1 − 1/a for 1 < a ≤ 2; 1/a for a ≥ 2). VALID.
## Dialogue notes
- Simpler than the brief's G1 (which compared Δg with Δf); the brief's route was correct but roundabout.
- L4 does NOT extend to several primes: with two primes the count of "touched" elements #{i∈J : p|i or q|i} can be one less
  than on [1,L] (an extra pq-multiple), so same-threshold domination fails (cf. D4); the factor 2 in g must absorb such
  boundary effects. The general (PQ′) remains with P21.
