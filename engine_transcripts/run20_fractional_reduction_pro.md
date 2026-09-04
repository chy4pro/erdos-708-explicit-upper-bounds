# Harvest index — Erdős #708, round 10 follow-up 2, ChatGPT Pro (GPT-5.6 Sol), chat P26 (fractional case)

Raw: `erdos708_pro_r10b_raw.md` (24,877 bytes, Chinese, 168 min). Brief: `engine/briefs/erdos708_r10_pro_followup2.md`.
Chat: https://chatgpt.com/c/6a99e714-0b38-83ea-8434-7a5399bc839b. Status: DONE 20:43 CDT. Verdict: NO fractional theorem, no counterexample.

## Rigorous partials (engine-tagged PROVED; Opus referee launched 20:5x on Lemmas 1–7, 9, 12, 13)
- L1 prime-power atomisation of S(n) = Σ_p min(z_p v_p(n), 1) into atoms α_{p,j} = min(z_p j,1) − min(z_p(j−1),1) ≥ 0 with S = Σ α_{p,j} 1[p^j | n].
- L2–C3 affine baseline certificate (c_1 = −1, c_{p^j} = α_{p,j}) and capped-mass criterion: (TH_C) holds if Σ_K min(S, C) ≥ m + 1.
- L4 atoms with p^j > m/64 contribute ≤ 1 in total to every k ≤ m (peel; costs 1 in the threshold).
- L5–Thm 6 DENSE fractional branch: if the natural mean H_64(m,z) := Σ_{p^j ≤ m/64} α_{p,j}/p^j ≥ 17/16 then Σ_K(S − 65)⁺ ≤ Σ_I(S − 1)⁺
  (first/second moments + quadratic cap min(r,C) ≥ r − r²/(…)).
- Reduction 7: full fractional (TH_65) ⇐ (SC_64): for m > 4096 and natural mean < 17/16 over p^j ≤ m/64, Σ_K(S_0 − 64)⁺ ≤ Σ_I(S_0 − 1)⁺.
  (SC_64) would give g(n) ≤ 81n.
## Obstructions (engine-tagged PROVED)
- L8 any positive-coefficient level-set/dyadic combination creates 'fake hinges' on the RHS (cannot control Σ_I with any constant).
- L9 '0/1 vertices ⇒ whole cube' is FALSE: 9 coordinates, LHS 7 copies of [9], RHS all 36 pairs; 7(t−4)⁺ ≤ C(t,2) at every vertex but
  z ≡ 1/2 gives 7/2 > 0. (Checked by hand: correct as an abstract set-system statement.)
- L10–11 independent/dependent Bernoulli rounding of weights leaves an unremovable fake cost.
- L12 positive pair coefficients are infeasible when total weight can be < 1 with two primes dividing n; L13 no fixed-degree pointwise
  polynomial certificate handles arbitrarily small weights.
- L15–16 the +1 per negative coefficient is sharp (Boolean-cube adversary move); random-partition certificate has signed error.
- L17–18 sliding-window certificate: nonnegative coefficients c_A = Leb{t : A_t = A}; capture limited by the number of active runs;
  a single ordering cannot give an absolute constant pointwise.
## Proposed next target
(RP_r): E_r ≤ Σ_K min((S−r)⁺, r) for the random-partition certificate F_r ⇒ (TH_{2r}); r = 64 ⇒ (TH_129) ⇒ g(n) ≤ 145n.
Finite-check plan: exact LP / abstract adversary restricted to the sparse core.
