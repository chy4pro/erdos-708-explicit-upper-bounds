# Final report audit

**PASS — no blocking mathematical, counting, or scope discrepancy found.**

Read the complete `report.md`, including its reproduced proof notebooks and final dependency block, `routes.md`, and `final_verification.json`. Checked the exact supplied k-split statement and atom-system threshold-17 statement against the local paper. No new search or numerical test was needed.

- The uniform bound is valid: k=3 handles m≥9n²; below it, r≤n+π(√m) and strict vertex rounding give G≤18n+π(3n)−1. The exact count of integers coprime to 6 in [1,3n] is n, proving π(3n)≤n+1, including n=1.
- The asymptotic bound is valid: k=18 handles m^17≥(18n)^19; below it √m<(18n)^(19/34). The resulting expression 18n+π((18n)^(19/34))−1 also dominates 18n in the outer regime. Its explicit power error is sublinear; the proved elementary prime estimate justifies the sharper logarithmic error.
- The CRT theorem, exact prime-power valuations, unique interval multiples, rational certificates, elementary prime-band termination, and its stated refutations are correct. Linear Ω(n) loss is distinguished from superlinear loss and from a counterexample exceeding additive n.
- The generalized monotone-profile hinge proof, modified-LP value bridge, demand-cap integral equivalence, and failure of level-LP equivalence are valid. The uncapped/capped distinction is maintained.
- Counts agree: 80 main jobs on 73 distinct instances plus 13 R3 jobs with one duplicate give 93 jobs on 85 distinct instances. The five initial DP exclusions were repaired exactly. Maximum normalized raw loss 99/100 agrees with the certificates. The final verifier's limited rechecking of DP optimality is explicitly disclosed; exhaustive DP computations, rather than unverified floating-point lower bounds, supply the other lower bounds.
- Repeated weaker bounds in the reproduced notebooks remain true and are expressly identified as weaker. They do not contradict the final stronger claim ledger or dependency block. The original additive-n and modified-LP rounding questions remain OPEN everywhere they are summarized.
- The stop criterion is supported by the brief's settled-target clause under the report's explicit standard interpretation of “≫n” as Ω(n). The report does not claim that all alternatives are settled, that open routes were frozen, or that the 45-minute review allotment was a wall-clock cap.

No new Lean verification or publication-priority claim is implied. The final dependency block correctly separates proved global cover bounds from the unresolved instancewise additive-n comparison.
