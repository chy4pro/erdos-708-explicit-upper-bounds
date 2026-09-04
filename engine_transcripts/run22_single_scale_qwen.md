# Harvest index — Erdős #708, round 12, Qwen3.8-Max, chat Q32 (single-scale sparse core)

Raw: `erdos708_qwen_r12_raw.md` (21 KB, captured by select-all; the Copy button wrote nothing). Brief: `engine/briefs/erdos708_r12_qwen.md`.
Chat: https://chat.qwen.ai/c/9a8957f7-76ed-4f6f-a1e0-0a523550a1af. Status: DONE 21:5x CDT (about 60 min).

## What it delivered (engine tags PROVED unless noted)
- T1 arbitrary weights: only the trivial regime — for y³ ≤ m < y⁴ at most three primes of (y,2y] divide any k ≤ m, so S ≤ 3 and (TH_3) holds
  with the zero certificate. The sliding-window certificate was NOT used for arbitrary weights; the interesting range m ≥ y⁴ is untouched.
- T1 0/1 weights: pair–triple alternating certificate proves (TH_2) for y ≥ 10⁷, y³ ≤ m < y⁴ (a special case of our published Section 11).
- T2 two scales: 'addition principle' — thresholds and certificates add (C₁ + C₂), consistent with the observation that per-scale certificate
  sums are feasible and the loss is on the left side.
- T3: the c ≥ 2 lower bound for the sliding-window family is tagged CONJECTURED, not proved.

## Assessment
Low value: no progress on the genuinely single-scale fractional core (m ≥ y⁴ with arbitrary weights); nothing to feed forward. Recorded for the
transcript archive only. Qwen micro-lemma seat: next dispatch should be a sharper, purely combinatorial target.
