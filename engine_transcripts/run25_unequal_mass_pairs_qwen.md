# Harvest index — Erdős #708, round 13, Qwen3.8-Max, chat Q33 (unequal-mass all-pairs certificate)

Raw: `erdos708_qwen_r13_raw.md` (21.7 KB, via the answer's Copy button). Brief: `engine/briefs/erdos708_r13_qwen.md`.
Chat: https://chat.qwen.ai/c/0f86d761-7e58-4cc9-84af-e3bc5522da06. Status: DONE (harvested 07:4x CDT).

## Claims (engine PROVED)
- T1: for N groups with masses in (β,1], the largest uniform all-pairs weight is λ_β(N) piecewise (0 when β ≤ 1/2; otherwise determined by the
  binding s); Lemma 2 exact fixed-mass pair weight; Lemma 3 AM–GM/floor bound; Lemma 4 the true bin guarantee from total mass > 64.
- T2: NO positive universal pair constant valid for every atom system with S_0(k) > 64 (Corollary 5; constants collapse near mass 1/2, Lemma 6) —
  agrees with P29's refutation of the uniform 2/65; the universal bound remains the 32-shadow one, log10 M = 32(log10 c_sh + 90 − log10 6.24) ≈ 2887.
- T3: ℓ-fold AM–GM value (Lemma 7); optimum discussion.

## Use
Consistent with P29 (round 13). Confirms that the pair-certificate 'improvement to 10^2957' is NOT universal for fractional weights. Archived as run25; not used in the paper.
