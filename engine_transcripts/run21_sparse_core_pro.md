# Harvest index — Erdős #708, round 11, ChatGPT Pro (GPT-5.6 Sol), chat P27 'Prove Or Refute Sparse Core'

Raw: `erdos708_pro_r11_raw.md` (20,517 bytes, Chinese, 141 min). Brief: `engine/briefs/erdos708_r11_pro.md`.
Chat: https://chatgpt.com/c/6a9a230b-28d4-83e9-b697-72b8e3248b25. Status: DONE 23:11 CDT; Opus referee launched 23:12 on all lemmas.

## Verdict on the targets
- T1 (SC_r) for all m: NOT proved. T2 (RP_64): REFUTED (Lemma 2, explicit small in-core example, deficit exactly 1/4096).
- T3 abstract adversary: PROVED in the 'counting-only' sense (Lemmas 5–6); NOT realisable by prime-power floor tables (Lemma 7).
- T4: a capacitated-transport (Hall-type) reduction (Lemma 13): if for every t ∈ [0,1]^K there is λ ∈ [0,1]^I with coverage
  Σ_{b∈I, q_a|b} λ_b ≥ Σ_{k≤m, q_a|k} t_k for every atom a and cost Σ λ_b ≤ C Σ t_k, then (TH_C) holds. Remaining: prove the transport
  with an absolute C in real floor systems.

## Structural results (engine PROVED)
- L1 random-partition Möbius coefficients μ_j = (−1)^j (j ≥ 2). L2 (RP_64) counterexample. L3–4 diagnostics ((TH_1) fails in very sparse cases).
- L5 Fano plane: μ = 8 empties + 7 lines, ν = each point ×2 + full set; every nonempty conjunction count differs by 0 or 1, yet
  Σ_μ(|B|−2)⁺ = 7 > 6 = Σ_ν(|B|−1)⁺. L6 projective plane of order q: m = qv+1, μ = lines + (q−1)v+1 empties, ν = singletons ×q + full set;
  Σ_μ(|B|−C)⁺ − Σ_ν(|B|−1)⁺ = v(q−C)+1 > 0 for C ≤ q; mean mass < 1 + 1/q (q = 67: m = 305,320, threshold 64 beaten).
  ⇒ the certificate principle with two-sided interval counts ALONE cannot give an absolute threshold; L7: not floor-realisable
  (singleton counts q+1 with pair counts exactly 1 force every product of two atom moduli to exceed m) ⇒ lcm/multiplicative structure necessary.
- L8 primorial barrier: (SC_64) vacuous for m < P_65 = ∏_{i≤65} p_i ≈ 6.1077·10^127.
- L9 Σ_{k≤m} e_ℓ((a_p(k))_p) ≤ m e_ℓ((h_p)_p) ≤ mH^ℓ/ℓ!. L10 (t−C)⁺ ≤ e_{C+1} of summands in [0,1]. Cor 11 Σ_K(S_0−64)⁺ ≤ mH^65/65! < 6.239·10^−90 m.
- L12 one k with S_0(k) > 64 forces Σ_I(S_0−1)⁺ > 63 (the window contains a multiple of k). Any counterexample needs m ≥ P_65 and a
  window deficient simultaneously for astronomically many moduli.

## Use
v9 §12: Proposition 'abstract two-sided counting is insufficient' (L5–L7) + remarks (L8, L9–11, L12) after referee PASS; T2 refutation and
transport reduction recorded in the transcript. Method-limit assessment: counting certificates are exhausted as a route to the linear
bound unless multiplicativity is used; next method must be genuinely arithmetic (CRT/lcm structure of windows).
