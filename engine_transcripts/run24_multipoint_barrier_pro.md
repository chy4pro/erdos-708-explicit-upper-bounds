# Harvest index — Erdős #708, round 13, ChatGPT Pro (GPT-5.6 Sol), chat P29 'Analyze Erdős Problem 708'

Raw: `erdos708_pro_r13_raw.md` (25,806 bytes, Chinese, 44 min). Brief: `engine/briefs/erdos708_r13_pro.md` (multi-point charging).
Chat: https://chatgpt.com/c/6a9a6ad3-8f34-83e9-abc5-25ee8655cdc7. Status: DONE ~02:45 CDT; harvested 07:4x (five-hour scheduling gap).

## Claims (engine PROVED unless noted)
- T3 (Theorem A): an explicit infinite family of atom systems + congruence windows with m > 10^2958 for which EVERY nonnegative certificate
  supported on divisors of high points has value ≤ L − 1 (Lemmas 4–7); the windows themselves satisfy (SC_64) (Lemma 8) — so the
  'all-high-point shadow LP' cannot prove the sparse core for all m. METHOD REFUTED, statement intact.
- Unconditional improvement: (SC_64) for 4096 < m ≤ 10^2942 ⇒ g(n) ≤ 81n for n ≤ 10^980 (increment over v10's 10^2887 / 10^962).
- T2 as stated REFUTED (Lemma 9): the uniform coefficient 2/65 is infeasible for unequal masses even with all 65 groups in (64/65, 1];
  optimal uniform coefficient c* = (B−1)/C(65,2), B = Σ b_i (Lemma 10); corrected bound R > (B−1)(mQ^{−2/65} − 1) > 63(mk^{−2/65} − 1),
  pushing such instances to m ≤ 10^3013 (Lemma 11).
- T4 (threshold o(ln ln m)): CONJECTURED only; proved barrier: the single-high-point numerical comparison needs C(m) ≫ √(ln m/ln ln m).
- Lemma 3: a minimal adversarial example against naive 'sum or dedupe' charging (A2 variants).

## Use / decision
Not published (owner rule 09-05: no paper versions while iterating; write once at completion). Recorded in the repo as run24. The shadow route
is at its method limit: single-point ceiling ≈ 10^2958, multi-point LP refuted by Theorem A. #708 linear-bound campaign paused at v10;
slot 1 rotates. A light Opus referee was launched on Theorem A and the 10^2942 claim to make the method-limit decision trustworthy.
