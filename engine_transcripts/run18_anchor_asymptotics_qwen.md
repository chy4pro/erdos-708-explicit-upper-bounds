# Harvest index — Erdős #708, round 10, Qwen3.8-Max, chat Q30 (r-anchor certificate asymptotics)

Raw: `erdos708_qwen_r10_raw.md` (21,325 bytes, 36 min). Brief: `engine/briefs/erdos708_r10_qwen.md`.
Chat: https://chat.qwen.ai/c/c768e917-0beb-4d9a-a9ea-c4293f9a36dd. Status: DONE (harvested 09-04 17:2x CDT).

## Claims (all tagged PROVED by the engine; T1 spot-checked numerically, the rest read but not audited line by line)
- T1: V_R(m) = α_R m ln ln m + κ_R m + O_R(m/ln m), α_R = 1 − ∏_{p∈R}(1−1/p), κ_R = (M−1) − Π_R(M − S_R − 1), explicit error (11+5·2^r) m/ln m.
  Check: R={2,3} reproduces our −(1/3) m lnln m + (29/18 − M/3) m. Numerics at m = 10⁶: V_2 = 1,403,760 vs formula 1,535,971; V_3 = 1,366,676 vs
  1,659,568 — deviations 1.8 and 4.1 times m/ln m, within the stated error constants (16 and 28 times m/ln m). Not contradicted.
- T2: for fixed r and fixed c the r-anchor certificate fails for all large m (deficit Π_R m ln ln m); §6: no r(m) can save a fixed c for this
  family (2^r subset penalties force 2^r = O(ln m), then the lost factor Π_R ≈ e^{−γ}/ln p_r still gives deficit ≫ m).
- T3: general P: V = α_R m H^{elig}_{P∖R}(m) + m B_R + O(2^r m/ln m), B_R = Π_R − 1 + S_R.

## Assessment
Confirms the coordinator's heuristic A2 (fixed anchors lose the factor ∏(1−1/a)). Now largely moot for the full prime set: the affine
certificate (paper v7 Corollary 'trivial regime') gives Σ_K ω − m ≈ 1.89·10⁶ at m = 10⁶, above every V_r. Relevant only for prime sets without
small primes (T3). Not used in the paper; kept as a transcript (run18) for the record.
