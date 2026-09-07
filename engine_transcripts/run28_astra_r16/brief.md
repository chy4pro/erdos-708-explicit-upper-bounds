# PROOF CAMPAIGN — Erdős Problem #708, round 16 (GPT-6 Astra via codex): close the sparse core (SC_64) for all m via the (NC) reduction

## Setting (all refereed; read the files, do not re-derive)
Paper: /Users/roychen/workspace/claudecode/automath/papers/erdos708/main.tex (sections: atoms, hinge inequality, sparse core, moment bound, shadow theorem, Theorem four = 0/1 hinge with threshold 4).
Round-15 report and referee: /Users/roychen/workspace/claudecode/automath/engine/out/claude_blitz_0905/F1_708/report.md and referee.md. Key refereed facts:
- (SC_64) := L ≤ R with L = Σ_{k≤m}(S₀(k) − 64)⁺, R = Σ_{b∈I}(S₀(b) − 1)⁺, atoms p^j ≤ m/64, weights α_{p,j} ∈ [0,1], Σ_j α_{p,j} ≤ 1, H = Σ α_{p,j}/p^j < 17/16, m > 4096.
- PROVED: (SC_64) for all m when all weights are 0/1 (so any counterexample is fractional). PROVED: for 4096 < m ≤ 10^2942 (shadow theorem + moments). PROVED: if S₀(b) ≤ S*(m) ≈ 1.4·10^20 for every b ∈ I (m ≤ 10^3000; S₀ ≤ 262 for single-atom-per-prime systems for all m) then R ≥ 2L. PROVED identity: for the hot-set-excluded certificate, W_T = λ(L − Σ_{b∈T} ov(b)); hence R ≥ L follows from (NC): the "crowded" points T (those with 2·ov(b) > capacity, all with S₀(b) > S*(m); |T| ≤ 1.07m/S*(m)) carry at most half of the certificate mass.
- Barriers (refereed): certificates feasible on the whole window fail on reflected windows (m! − m, m!]; window-independent certificates fail beyond 10^2958. Both are escaped by excluding a single hot point.

## Targets
T1 (main): prove (NC) for every sparse window, or prove (SC_64) by any rigorous route, for all m. The crux: windows containing > 1.07m/S*(m) points each divisible by > 10^100 hot carriers ("crowding"). Tools: the moment bound (L ≤ mH^65/65!), the identity, Lemma A (mass per multiple ≤ θ^{2−r}H^r/r!), Lemma B (carrier counts), the Bonferroni repair in referee.md §6.3, Theorem C. A route to test first: show crowded points are so rare that Σ_{b∈T} ov(b) ≤ L/2 by bounding ov(b) via the atoms' mean H and the number of carriers through b (Lemma B), using that carriers through one point share its prime support.
T2: if T1 fails, produce an explicit family (all hypotheses verified) with (NC) false and compute W_T for every admissible T; if (SC_64) itself fails on it, that refutes the linear route via this reduction — say so plainly.
T3: whichever way, write the final theorem statement precisely and list what a Lean formalisation needs.

## Rules
Wall-clock cap 3 h; write /Users/roychen/workspace/claudecode/automath/engine/out/astra_708_r16/checkpoint.md every 30 min and report.md at the end (create the directory; touch nothing else; no git). Status tags PROVED / CONDITIONAL / REFUTED / OPEN on every claim; complete proofs for PROVED; exact arithmetic for witnesses; a check that cannot fail counts as no check; final block "final claim ← lemmas ← unproved items".
