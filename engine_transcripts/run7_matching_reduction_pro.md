# P20 HARVEST — #708 round 4, hinge inequality (TH) (ChatGPT Pro GPT-5.6 Sol, "Worked for 143m 36s")
# Chat: https://chatgpt.com/c/6a993888-0590-83ea-adb6-1bb42db4e4bf   (started ~04:06 CDT 09-04, harvested 06:4x CDT)
# Verdict shape: NO proof of T1–T5, NO counterexample. Strongest result: a valid REDUCTION of (TH) to a weight-free
# perfect-matching statement (NM) ⟺ (SB), plus a valid reduction of the 0/1 case T3 to a two-layer sieve statement (Tail21).
# DIALOGUE VERDICT (see below): the reduction is correct but its target (NM)/(SB) is FALSE for large m
# (Hensley–Richards dense admissible tuples) — this route cannot prove (TH). Details in problems/erdos708/NOTES.md.

## Index of P20's content (all lemmas checked by dialogue unless marked)
- L1 (layer-cake): (u−c)⁺ = ∫_c^∞ 1_{u>t} dt; hence if for all t ≥ 1: #{k ≤ m : w(k) > t+1} ≤ #{b ∈ I : w(b) > t}  (1)
  then (TH). VALID.
- L2: C_t = {n : w(n) ≤ t} is divisor-closed and C_t^{[1]} := C_t ∪ {dp : d ∈ C_t, p prime} ⊆ C_{t+1} (uses z_p ≤ 1). VALID.
- (SB) [unproved]: for every divisor-closed C, m ≥ 1, x ≥ 0: |C ∩ I| ≤ |C^{[1]} ∩ [1,m]|.
- L3: (SB) ⇒ (1) for all w, all t ≥ 0 (apply (SB) to C_t, complement). VALID.  Cor 4: (SB) ⇒ (TH) ⇒ g(n) ≤ 18n. VALID.
- (NM) [unproved]: the bipartite graph G_{m,x}, L = [1,m], R = I, k ~ b iff k/gcd(k,b) ∈ {1} ∪ primes (⟺ ∃ prime p | k with
  (k/p) | b; k = 1 adjacent to all), has a perfect matching.
- L5: (SB) ⟺ (NM) via Hall with C_T = divisor closure of T ⊆ I and N(T) = C_T^{[1]} ∩ [1,m]. VALID.
- L6/L7: a perfect matching φ gives w(φ(k)) ≥ w(k) − 1 and (w(k)−2)⁺ ≤ (w(φ(k))−1)⁺ termwise. VALID.
- L8/L9/Cor10 (0/1 weights, prime set P): (Ω_P−1)⁺ = R_P + (ω_P−1)⁺, (Ω_P−2)⁺ ≤ R_P + (ω_P−2)⁺ with
  R_P(n) = Σ_p (v_p(n)−1)⁺; Σ_{k≤m} R_P(k) ≤ Σ_{b∈I} R_P(b) (per-prime-power counts); so T3 follows from the square-free form
  (SF): Σ_{k≤m}(ω_P(k)−2)⁺ ≤ Σ_{b∈I}(ω_P(b)−1)⁺. VALID.
- (Tail21) [unproved]: for finite Q, L ≥ 1, y ≥ 0: #{n ≤ L : ω_Q(n) ≥ 2} ≤ #{y < n ≤ y+L : ω_Q(n) ≥ 1}.
  L11: (Tail21) ⇒ (SF) (order the primes, count the 3rd/2nd prime factor by Q_j = {p_1..p_{j−1}}, multiples of p_j in I form a
  run of q's of length ≥ ⌊m/p_j⌋). Dialogue: plausible; NOT re-derived line by line.
- §8 (why T3 does not give fractional weights): w = ∫_0^1 Ω_{P_t} dt; ∫(Ω_{P_t}(n)−1)⁺ dt = w(n) − max_{p|n} z_p ≥ (w(n)−1)⁺,
  wrong direction (example z_p = z_q = 0.6). VALID and useful.
- §9: prefix total-weight domination Σ_{i≤r} w(x+i) − Σ_{i≤r} w(i) = w(C(x+r, r)) ≥ 0 is not enough (abstract 3-term
  counterexample). VALID.
- §10: matching code (augmenting paths); five instances m ≤ 100 matched perfectly.
- §11: Lean skeleton notes.

## Dialogue findings after harvest
- (NM)/(SB) is FALSE for large m: for T = {b ∈ I : lpf(b) > m/2} one has N(T) ⊆ {1} ∪ {primes ≤ m}, so Hall needs
  #{rough b in I} ≤ π(m)+1; by CRT the rough positions realise any pattern missing one residue class mod each prime ≤ m/2,
  so the maximum is the Hensley–Richards quantity ρ*(m) (> π(m) from m = 3159, unbounded excess). Explicit certificate:
  problems/erdos708/nm_refute.py (greedy admissible pattern + CRT + direct check).
- (TH) itself is untouched by this: for the weights that make K₂ = all composites, (TH) is trivial.
- Surviving target from P20's own layer-cake step: (LAYER) #{k ≤ m : w(k) > t+1} ≤ #{b ∈ I : w(b) > t} for t ≥ 1 — tested
  separately (problems/erdos708/layer_test.py).
