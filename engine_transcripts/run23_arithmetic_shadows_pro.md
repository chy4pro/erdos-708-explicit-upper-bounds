# Harvest index — Erdős #708, round 12, ChatGPT Pro (GPT-5.6 Sol), chat P28 'Prove Sparse Core Arithmetic'

Raw: `erdos708_pro_r12_raw.md` (18,954 bytes, Chinese, ~105 min). Brief: `engine/briefs/erdos708_r12_pro.md` (arithmetic route after the
counting limit). Chat: https://chatgpt.com/c/6a9a4baa-bd18-83ea-b5b0-0c5a4a0c1c74. Status: DONE 01:26 CDT; Opus referee launched 01:28.

## Main claims (engine PROVED)
- Lemma 1 (32-group packing): masses in (0,1] with sum > 64 can be split into 32 disjoint groups each of mass in (4/3, 2].
- Lemma 2 (arithmetic shadows): if S_0(k) > 64 for some k ≤ m, then with D_r := ∏_{p∈G_r} q_p (q_p = largest active prime power of p at k)
  the certificate c_{D_r} = 1/3 is (F)-feasible for S_0 (t divisors ⇒ S_0(n) > 4t/3 ⇒ (S_0−1)⁺ > t/3), hence
  R ≥ (1/3)Σ_r ⌊m/D_r⌋ ≥ (32/3)(1−6^−31) m/k^{1/32} ≥ C_* m^{31/32} (AM–GM on ∏ D_r ≤ k ≤ m; m/D_r ≥ 6^31).
- Theorem 3: with L ≤ 6.24·10^−90 m, (SC_64) holds for 4096 < m ≤ 10^2887 (m^{1/32} ≤ C_*/c_0 ≈ 1.71·10^90). Coordinator's check of the
  exponent arithmetic: log10 m_max = 2887.45; consequence g(n) ≤ 81n for n ≤ 10^962 (8n³ ≤ 10^2887).
- Proposition 6 (T3): the multiples-only charging of the brief's A2 fails by an unbounded factor on an explicit residue-defined window;
  Lemma 7: that window is not an (SC_64) counterexample (R/L ≥ 64(M+1)^63). Lemma 4: an independent periodic branch. Lemma 5: 0/1 single-point
  shadow with threshold 5. §8 self-audit; §10 exact remaining gap: charging ALL high points (shadow overlap) for m > 10^2887.

## Use
If the referee passes: paper v10 — Lemma pack32 / Theorem shadow / Corollary 2887 (g(n) ≤ 81n for n ≤ 10^962) + remark (raising the threshold
gives √(ln m/ln ln m) for all m, weaker than 20 ln ln m). Draft at scratchpad/sec_shadow.tex (coordinator's own proof of the packing lemma).
