# PROOF CAMPAIGN (Lean 4) — Erdős 708 sparse-core theorem: formalise Section 14 as a statement-first decomposition

Context: you just proved the three milestone lemmas (Erdos708/Proofs/{Numerical,Hinge,Moment}.lean, all sorry-free with 3 standard
axioms) — reuse them by `import`? No: the project has no module structure for them; instead copy the needed lemma statements+proofs into
your new files or keep each new file self-contained (import Mathlib; open Finset BigOperators). Project: lean/proofenv (never lake update/build).

Goal theorem (card, compiles with sorry): Erdos708/SparseCore.lean, `Erdos708SparseCore.sparse_core` —
  ∀ A : AtomSystem, ∀ m > 4096, mean A < 17/16 → ∀ x, (141/128) * L A m ≤ R A x m.
Paper source: /Users/roychen/workspace/claudecode/automath/papers/erdos708/sec_signed.tex (Section 14: Theorem 14.1 and Lemmas 14.2–14.10,
with complete proofs). Read it in full first. The prose proof was refereed; your job is faithful formalisation, not new mathematics.

Method (Prove2Me-style cards; this is the workflow used to formalise FLT):
1. Definitions file Erdos708/Signed/Defs.lean: dyadic rounding of cumulative weights, retained levels with the cutoff q^(16/t) ≤ m
   (16/t is a natural number since t = 2^(-h)), b_p, B, H_B, L_B, R_B; the decreasing-value order with the (p,j) tie-break; hot k;
   effective levels; prefixes P_i(k); weights w_{k,i} = |[s_{i-1}, s_i) ∩ (2,3]|; carriers; μ(P), θ_P, M(P), K_P, c_P; T_θ, N_θ; U_P; F.
   Keep every definition computable-or-noncomputable as needed but Lean-checkable; avoid `Classical` where a Finset works.
2. Cards file Erdos708/Signed/Cards.lean: one `theorem` per paper lemma (14.2 rounding: H_B ≤ H, R_B ≤ R, L ≤ 2 L_B; 14.5 carried mass;
   14.6 carrier count; 14.7 values at a point ≤ 2B; 14.9 pointwise feasibility F(n) ≤ (B(n)-1)^+; 14.10 value on the window
   ≥ (141/64) L_B) — each stated faithfully and ending in `:= by sorry`, plus the composition theorem `sparse_core` proved FROM the cards
   (no sorry in the composition itself). Compile the cards file first; this is the deliverable that must exist even if no leaf is proved.
3. Then prove leaves in separate files Erdos708/Signed/Proofs/<Name>.lean in this order: 14.7 (values at a point), 14.2 (rounding),
   14.6 (carrier count), 14.10 (value on the window), 14.5 (carried mass), 14.9 (feasibility). Each proof file restates the card exactly
   and ends with `#print axioms`. A leaf that resists after ~25 minutes is left as `sorry` with the exact remaining goal recorded.
Rules: compile after every change (`lake env lean <file>`); no sorry/admit/native_decide/custom axioms in anything you call PROVED;
statements must match the paper (write a one-line read-back for each card in cards_readback.md: what the Lean says, blind to the prose);
wall-clock cap 2 hours; checkpoint.md every 30 minutes and report.md at the end under engine/out/astra_708_lean2/ (per card: PROVED with
axioms output, or OPEN with the remaining goal); touch only Erdos708/Signed/ and the output directory; no git; no internet.
