# Q24 HARVEST — Erdős #708 round 4 (hinge inequality TH), Qwen3.8-Max, chat 9a7e533a, harvested 2026-09-04 05:1x CDT via Copy+pbpaste (raw: erdos708_qwen_r4_raw.md, 16.1KB)
# VERDICT (dialogue audit): honest partial. No proof of (TH)/(BH). Useful: exact special cases, an exact reduction of the 0/1 case, a refuted stronger statement, a brief correction.

## Verified content
- Correction to my brief: the displayed "equivalent form" had the capped sums reversed. Correct: (TH) ⟺ Σ_{b∈I} min(w(b),1) − Σ_{k≤m} min(w(k),2) ≤ Σ_{b∈I} w(b) − Σ_{k≤m} w(k). (TH) itself was stated correctly. Brief fixed.
- Lemma 1 (one prime, any 0 ≤ z ≤ 1): (TH) holds — layer-cake: Σ_R (z v_p − a)⁺ = ∫_0^∞ N_R(⌊(a+t)/z⌋+1) dt with N_R(j) = #{n ∈ R : p^j | n}, and N_I(j) ≥ N_K(j), j_I(t) ≤ j_K(t). Sound.
- Lemma 2 (two primes, 0/1 weights): (u+v−1)⁺ = (u−1)⁺ + (v−1)⁺ + [u,v ≥ 1] and (u+v−2)⁺ ≤ same; then per-prime-power domination and domination of multiples of pq. Sound.
- Lemma 5 (0/1 weights): with M_q(R) = Σ_{n∈R} C(Ω(n), q) and Δ_q = M_q(I) − M_q(K) ≥ 0 (each M_q is a nonnegative combination of multiple-counts of weight-q divisors): (TH)_{0/1} ⟺ Σ_{q≥2} (−1)^q Δ_q ≥ −#{k ≤ m : Ω(k) ≥ 2}. Identity machine-checked on 200 random instances (0 mismatches). The obstruction: the odd-q terms enter with a minus sign.
- Refuted stronger statement: "#{b∈I: Ω(b) ≥ r} ≥ #{k≤m: Ω(k) ≥ r} for all r ≥ 2" is FALSE: m = 1000, S = {23,29,31}, x = 23²29²31² − 500: K has six numbers with Ω = 2, I has only M (Ω = 6). Machine-checked. (TH) still holds there with slack 5.
- Fractional weights: lifting a 0/1 proof needs an explicit layer inequality (their (14)); convexity blocks naive rounding.

## Status of round 4
P20 (Pro) still running (route: injection k ↦ b ∈ I with (k/p) | b for some prime p | k, giving w(b) ≥ w(k) − z_p ≥ w(k) − 1 — if such an injection exists for the subset {k : w(k) ≥ 2}, (TH) follows; a Hall-type matching lemma is under audit there).
