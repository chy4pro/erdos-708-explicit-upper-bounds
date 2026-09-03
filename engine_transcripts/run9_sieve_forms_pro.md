# P21 HARVEST — #708 round 5, (PQ′) ⇒ (TH) ⇒ 18n (ChatGPT Pro GPT-5.6 Sol, "Worked for 224m 23s", harvested 11:19 CDT 09-04)
# Chat: https://chatgpt.com/c/6a9964d0-0130-83e9-a518-8505cb1f84e9   Raw (Copy): erdos708_pro_r5_raw.md
# Verdict: NO proof of T1–T5, NO counterexample. Valid partial results + reformulations; one endorsed target is FALSE (see audit).

## Index (dialogue audit in brackets)
- L1 finitisation: primes > L can be dropped (z_p := 0 only raises LHS, RHS unchanged); valuations on J may be capped at e_p = ⌊log_p L⌋
  (raises LHS via monotonicity) — a harder finite model. [VALID]
- L2 one prime, all a ≥ 0: Σ_J f_a(z v_p) ≤ Σ_{[1,L]} f_a(z v_p) by telescoping + ⌊L/p^j⌋ counts, then f ≤ g. [VALID; identical to Q25]
- L3 large-a region: if a ≥ 2 and aL ≥ W_L := w(L!) = Σ_{k≤L} w(k), then (PQ′) holds: LHS ≤ L/a, RHS = 2Σ 1/(a+w(k)) ≥ 2L²/(aL+W_L) ≥ L/a.
  Explicit sufficient forms: a ≥ max(2, Σ_{p≤L} z_p/(p−1)) or a ≥ max(2, log₂(L!)/L). [VALID, hand-checked; weak — needs a ≳ ln ln L]
- L4 (EC): s Σ_J s^{w} ≤ Σ_{[1,L]} s^{w} for s ∈ (0,1] ⇒ (PQ′) for a ≥ 2 (Laplace, then 1/(x−1) ≤ 2/x for x ≥ 2). [VALID implication —
  but (EC) is FALSE: dialogue certificate lap_counterexample_L1000000.txt (L=10^6, s ∈ [0.005,0.015]); P21 still calls (EC) a
  "genuinely valuable target" — WRONG, D7]
- L5 abstract random-set example showing intersection-count domination alone cannot give (EC). [VALID, fine]
- L6 0/1 weights: (TH) ⟺ (SI): B₀ − A₀ ≤ Δ + B_{≥2}, with B₀/A₀ the P-rough counts on [1,L]/J, Δ the prime-power surplus,
  B_{≥2} = #{k ≤ L : Ω_P(k) ≥ 2}; and B₀ − A₀ = Σ_{∅≠S⊆P} (−1)^{|S|+1} δ_{∏S} (inclusion–exclusion). [VALID, identities hand-checked;
  same as Q24's alternating-surplus form]
- L7 0/1: repeated prime powers peel off (per-prime-power domination), so 0/1 (TH) ⇐ distinct-prime (DTH): Σ_{k≤L}(ω_P(k)−2)⁺ ≤ Σ_J (ω_P(b)−1)⁺. [VALID; also in P20]
- L8–L9 (DTH) ⇐ AF "arithmetic forest transfer": for each k with ω_P(k) = d ≥ 3 choose a forest F_k with d−2 edges on S(k) = {p ∈ P : p | k};
  send each edge {p,q} to some b ∈ J with pq | b so that the edges landing on b form a forest on S(b) (≤ ω_P(b)−1 of them).
  Exact criterion: Rado's theorem for the direct sum of graphic matroids: r(∪_{u∈U} A_u) ≥ |U| for all unit subfamilies U.
  Single-label capacities automatic (#{k ≤ L : pq | k} ≤ #{b ∈ J : pq | b}); the obstacle is acyclicity across labels. [VALID as a sufficient
  condition; truth of AF UNKNOWN — a transport statement, so it must be stress-tested on H–R windows before use]
- L10 a single global forest cannot work (averaging over r-subsets). [VALID]
- L11 composites-only injection fails on the L = 10^5 window by 142. [VALID; = D1]
- Gaps stated by P21: (A) prove (EC) [dead — false]; (B) prove AF (0/1 only; fractional needs a polymatroid version).

## Dialogue verdict
No advance on T1–T5. New usable pieces: L3 (large-a region), (SI)/(DTH)/AF reformulation with the Rado criterion. The engine did not
detect that (EC) is false (needs L ~ 10^6 CRT windows). Five Pro rounds on the linear bound (P19–P21 ≈ 10.5 h) have produced exact
reductions but no proof; the remaining honest program is analytic (explicit large-sieve bounds inside the layer-cake form).
