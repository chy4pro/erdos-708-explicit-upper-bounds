# P23 HARVEST — #708 round 7, counting certificates (ChatGPT Pro GPT-5.6 Sol, "Worked for 42m 59s", harvested 14:12 CDT 09-04)
# Chat: https://chatgpt.com/c/6a99b47f-4414-83e9-836e-c34969adf494   Raw (Copy): erdos708_pro_r7_raw.md
# Verdict: only T3 REFUTED (as literally posed for all subsets P): for P = primes in [53,653], m = 10^8, the two-anchor certificate
# gives V_2 = 1,595,615 < W_ω = 1,602,217 (dialogue re-verified both numbers independently: sieve over 10^8 and direct formula).
# Nothing on T1/T2/T4/T5. Valid but low value: the target was mis-posed by the dialogue (V_2 with the two smallest primes of P as anchors);
# with r = 3 anchors the same family already covers this instance: [(2, 1595615), (3, 2266053), (4, 2845025), (5, 3364142), (6, 3843681)]. Lesson: choose the number of anchors adaptively.
## Content: L1 feasibility of the two-anchor certificate (cases s = 0,1,2) [VALID]; L2 exact V_2 [VALID, verified]; L3 ω_P ≤ 4 for n ≤ 10^8
## [VALID: 53·59·61·67·71 > 10^8]; L4 (r−2)⁺ = C(r,3) − 2C(r,4) for r ≤ 4 and double counting [VALID]; L5 W = S_3 − 2S_4 [VALID, verified];
## C++ checker provided. No status-tag violations; dependency list given. The run stopped at 43 min without touching T1 (the real target).
