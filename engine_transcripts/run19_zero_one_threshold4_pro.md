# Harvest index — Erdős #708, round 10, ChatGPT Pro (GPT-5.6 Sol), chat P26 'Counting constant proof'

Raw: `erdos708_pro_r10_raw.md` (21,244 bytes, Chinese, 65 min). Brief: `engine/briefs/erdos708_r10_pro.md` (+ follow-up 2 sent 17:47 for the
fractional case). Chat: https://chatgpt.com/c/6a99e714-0b38-83ea-8434-7a5399bc839b. Status: DONE; independent Opus referee PASS (12.7 min, every
step re-derived, 68,251 exhaustive instances m ≤ 43 + structured/random/deep-window scans: min(RHS−LHS) = 0, only degenerate).

## Main result (Theorem 6 → paper Theorem 'four', v8)
For every finite prime set P, m ≥ 1, x ≥ 0: Σ_{k≤m}(Ω_P(k)−4)⁺ ≤ Σ_{b∈I}(Ω_P(b)−1)⁺. Proof by counting certificates only:
y = ⌊m^{1/3}⌋, S = P ∩ [2,y], η = (1+1/y)Σ_{p∈S}1/p. Peel: ω_{P∖S} ≤ 2 on [1,m]; (Ω_P−4)⁺ ≤ e_P + (ω_S−2)⁺.
Sparse η ≤ 2: c_{p^j}=1 (j≥2), c_{pq}=11/21, c_{pqr}=−1/7 on S; (F) via r(r−1)(13−r)/42 ≤ (r−1)⁺; value ≥ A + E₂/3 using C(|S|,3) ≤ E₃ and
3E₃ ≤ ηE₂ (needs ⌊m/pq⌋ ≥ y); (r−2)⁺ ≤ C(r,2)/3. Dense η > 2: affine certificate; Σ min(Ω_P,4) ≥ m+1 via a greedy Q ⊆ S with 3/2 ≤ H_Q < 2,
min(r,4) ≥ r − C(r,2)/7, f(h)=h−h²/14 increasing, (19/56)m ≥ y+1 (y ≥ 5).
## Side results
Lemma 7: full prime set — no abstract adversary beats c=2 (= our affine corollary). Theorem 10: flat anchor certificates fail at c=3 for
Y=2^41, m=(8Y)^4, P=(Y,8Y] (Case 1 margin 0.44%). Lemma 11: same P solved at c=2 by pair–triple. Lemma 12: threshold layer-cake averaging
gives ∫(Ω_{P_t}−1)⁺dt = w − max z_p, not (w−1)⁺ — naive transfer to fractional weights fails.
## Referee notes
Threshold 4 = 2 (ω_L ≤ 2 from y=m^{1/3}) + 2 ((r−2)⁺ ≤ C(r,2)/3); (4.3) is an identity at η=2 (no slack); presentational gaps only
(⌊m/pq⌋ ≥ y, |Q| ≤ π(y) ≤ y, M₃ ≤ E₃ in Lemma 11). Empirically c=2 holds everywhere tested, c=1 fails from m=15.
Referee scripts: repo src/referee_c4_cert.py, src/referee_c4_scan.py. P26's own verify script (sandbox file) was not downloaded.
## Gap
Fractional weights (needed for the linear bound) — follow-up 2 running.
