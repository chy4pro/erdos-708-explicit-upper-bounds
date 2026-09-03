# P22 HARVEST — #708 round 6, hinge inequality by explicit sieve bounds (ChatGPT Pro GPT-5.6 Sol, "Worked for 93m 23s", harvested 13:30 CDT 09-04)
# Chat: https://chatgpt.com/c/6a999f80-2144-83ea-9654-c7791cb48673   Raw (Copy): erdos708_pro_r6_raw.md
# Verdict: THEOREM A PROVED (dialogue audit PASS, every lemma re-derived; 52,850 numerical tests of the theorem and 51,775 of Lemma 3, no failure):
#   for every finite prime set P, m ≥ 3, x ≥ 0:  Σ_{n≤m} (Ω_P(n) − c*(m))⁺ ≤ Σ_{b∈I} (Ω_P(b) − 1)⁺,  c*(m) = 5 + max(2, ⌈2e² ln(1 + ln m/6)⌉) ≤ 20 ln ln m (m ≥ 30).
#   i.e. the 0/1 hinge inequality with threshold c = 20 ln ln m instead of 2 (target T4, 0/1 part). Fractional weights NOT covered (honestly stated).

## Index (all VALID unless noted)
- L1 N_J(d) ∈ (L/d − 1, L/d + 1) (floor identity).
- L2 Σ_{p≤y} 1/p ≤ e·ln(1 + ln y): 1/p ≤ e p^{−σ} with σ = 1 + 1/ln y, Σ p^{−σ} ≤ ln ζ(σ) ≤ ln(1 + 1/(σ−1)). Explicit, elementary.
- L3 (core sieve) L ≥ 64, y = L^{1/6}, R = {q ∈ Q : q ≤ y}, H = Σ_R 1/q, s(L) = max(2, ⌈2e² ln(1 + ln L/6)⌉): for every interval J of length L,
  #{n ≤ L : ω_Q(n) ≥ s(L)+5} ≤ #{n ∈ J : ω_Q(n) ≥ 1}. Proof: ≤ 5 large primes per n ≤ L; N_s ≤ L H^s/s! ≤ L 2^{−s} ≤ L/4 (s ≥ 2eH, s! ≥ (s/e)^s);
  two-term Bonferroni with L1 gives U_J(R′) ≥ L(H′ − H′²/2) − (3/4)y² ≥ L/4 for a subfamily with 1/2 ≤ H′ ≤ 1, or U_J(R) ≥ LH/4 when H < 1/2
  (N_s ≤ LH²/2 ≤ LH/4). Uses BOTH bounds of L1 (lower on singles, upper on pairs) — the counting-certificate principle in disguise.
- L4 ordering identity (ω_P(n) − c)⁺ = Σ_{p|n} 1_{ω_{<p}(n) ≥ c}.
- Thm 5 distinct-prime version: per p, n = pi, i ≤ L = ⌊m/p⌋, quotient interval J_p of length L or L+1 (correctly NOT identified with [1,L]); L3 applies
  for L ≥ 64 since s(L) ≤ s(m); for L < 64, ω ≤ 3 < 7 ≤ c*.
- L6–L7, Thm 8: prime powers peel off exactly ((Ω−1)⁺ = E + (ω−1)⁺, (Ω−c)⁺ ≤ E + (ω−c)⁺, Σ_I E ≥ Σ_K E).
- L9 c*(m) ≤ 20 ln ln m for m ≥ 30 (monotone G(t), numeric certificate at m = 30); m < 30 trivial.
- §8–9 fractional weights: lossless peel w = E + S with S = Σ_p min(z_p v_p, 1); (w−1)⁺ = E + (S−1)⁺, (w−C)⁺ ≤ E + (S−C)⁺, Σ_I E ≥ Σ_K E; so the
  fractional T4 reduces to (50): Σ_K (S−C)⁺ ≤ Σ_I (S−1)⁺, integer form (NC) with R(n) = Σ_p min(a_p v_p(n), N): Σ_K (R − CN)⁺ ≤ Σ_I (R − N)⁺. [VALID reduction; unproved]
- §10 why layer-cake fails (∫(r_t−1)⁺ = S − max z_p ≠ (S−1)⁺) [VALID, = P20 §8]; §11 audits [fine]; §12 Lean modules.

## Dialogue notes
- No consequence for g(n) yet (the LP dual needs fractional z). Value: first explicit-constant hinge inequality for 0/1 weights at every m;
  complements the counting certificates (0/1 with c = 2 for m ≤ 1000 by LP, and for m ≤ ~10^48 by C_2 pending Q27's rigorous range).
- Candidate for the paper (v4): Theorem A + the certificate principle + C_2 range + (NC) as the exact remaining statement.
