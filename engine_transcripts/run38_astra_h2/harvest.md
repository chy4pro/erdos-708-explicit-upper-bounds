# Harvest — Astra (H_2) campaign, 2026-09-08 14:08–14:50 CDT (41m29s, single agent, ~6 pool points)

Brief: engine/briefs/erdos708_h2_astra.md. Output: engine/out/astra_708_h2/.

## OUTCOME
T1 (prove (H_2)) and T2 (refute it) were FROZEN by the two-unchanged-gap rule. No (H_2), no counterexample. The fallback T3 succeeded.

## CLAIMS
C1 (threshold): (H_c) holds for every atom system, every m and every window at c = 280923567/32000000 = 8.77886146875, improving the refereed 56501/6400 = 8.8283 by 1581433/32000000. Constants ρ = 9/8, H* = 1000003/1000000, D_0 = 28407/10240, T = 5337547/1000000; 65 finite scales plus an analytic tail total 499998420228283/500000000000000 < 1.
**MY JUDGEMENT: THIS CHANGES NO PUBLISHED BOUND.** Through g(n) ≤ ⌈cn⌉ + 2n the integer bound stays 11n (⌈8.7789n⌉ + 2n ≤ 11n exactly as ⌈8.8283n⌉ + 2n did). The real-valued bound improves for n ≥ 5, which is not a publishable change under the corrected cadence. Not going into the paper as a headline; recorded here only.
C2 (K_4 for a fixed support): K_4 holds for {2,3,5,7} for every integer Q ≥ 2 — I had this recorded as OPEN. Also proved: a uniform K_4 for all four-prime supports once Q ≥ 4900014488437221682.
C3: consequently (H_2) holds for arbitrary MULTILEVEL atom systems supported on {2,3,5,7,p} for any fifth prime p, and on any subset. This is a genuine addition to the Section 19 sequence (four primes; five primes with one multilevel; per-prime cap; six-prime impossibility): it fully settles the smallest primes.
REFUTED intermediates: an unrestricted minimum-divisor layer majorant as an induction step (exact witness); reusing the published eight-mantissa retention/carrier construction at threshold 2 (exact sparse witness).
Finite: no violation of (H_2) in 116,424,000 full-period window instances plus 215,838 sampled ones.

## MY EXACT RECHECKS (all pass)
D_0 + ρT = 280923567/32000000 exactly ✓; the improvement 56501/6400 − c = 1581433/32000000 ✓; the nine listed scale-group bounds plus the tail sum to exactly the claimed 499998420228283/500000000000000 < 1, with pointwise margin 1579771717/500000000000000 ✓; and I ran the campaign's own `final_verify.py --full` myself: FINAL PASS, 65 finite scales, kernel_checked false (correctly disclosed).

## IT CAUGHT THREE ERRORS IN MY BRIEF
(i) R8 stated the general remaining case as also requiring two multilevel primes and a prime of weight above 1/2; those hold only for at most five active primes. (ii) R7 reversed a domination direction. (iii) — the one I had missed — the non-empty witness I quoted for that region has only ONE multilevel prime (2, carrying atoms 2 and 4), so it does not lie in the strengthened region at all. I checked the PAPER: Proposition (the remaining case) there states the region WITHOUT the two-multilevel clause and the witness does satisfy it, and the two-multilevel clause lives in a separate corollary about at most five primes, so the paper is correct and only the brief was wrong. Corrected in the brief with dated notes.

## DECISION
No Zenodo, no X (no bound changed). Scoped Opus referee on C2 and C3 only, since those are the parts intended for the paper; C1 is recorded but not published. Pool after the campaign: 31%, resets 21:38 on 14 Sep — enough to keep for the Section 18 formalisation after the reset.
