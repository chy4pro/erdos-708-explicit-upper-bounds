# PROOF CAMPAIGN (Lean 4) — Erdős 708: formalise the reduction chain from the sparse core to g(n) ≤ 81n (no wall-clock cap)

Context. A parallel campaign (same project, directory Erdos708/Signed/) is formalising Section 14 (the sparse-core theorem
Erdos708SparseCore.sparse_core: for every atom system with mean < 17/16, m > 4096 and window, (141/128)·L ≤ R). Do NOT touch
Erdos708/Signed/ or Erdos708/Proofs/ or Erdos708/SparseCore.lean. Your directory is Erdos708/Chain/ (create it). Project lean/proofenv
(Lean 4.34.0-rc1, Mathlib built; never lake update/build). Paper: /Users/roychen/workspace/claudecode/automath/papers/erdos708/main.tex —
read Sections 7 (sec:linear: Theorem thm:cond, Lemmas lem:dual, lem:round, lem:fewprimes), 5 (sec:long: Theorem thm:long) and 13
(sec:sparse: Lemma lem:largeatoms, Theorem thm:dense, Corollary cor:sparsecore) in full. Every proof there was refereed.

Goal. A kernel-checked statement of the final theorem and its proof from the sparse-core inequality, statement-first:
  theorem Erdos708Chain.linear_bound : ∀ n ≥ 1, ∀ (A : Finset ℕ) (hA : A.card = n) (h2 : ∀ a ∈ A, 2 ≤ a) (x : ℕ),
      ∃ B ⊆ Finset.Icc (x+1) (x + A.max' _), B.card ≤ 81 * n ∧ (∏ a ∈ A, a) ∣ (∏ b ∈ B, b)
  (pin the exact convention of the paper's definition of g(n): "at most g" — read Section 1 and the definition before writing the card),
proved from one hypothesis card `sparse_core_hyp` stated exactly like the Section-14 theorem (same AtomSystem/S0/mean/L/R definitions —
copy them verbatim from Erdos708/SparseCore.lean into your own namespace Erdos708Chain so the two campaigns do not depend on each other;
we will identify them later).

Method (statement-first cards, then leaves; same rules as before):
1. Erdos708/Chain/Defs.lean: the paper's objects for the reduction — weights z_p ∈ [0,1] on primes, w_z(n) = Σ z_p v_p(n), the atoms
   α_{p,j} = min(j z_p,1) − min((j−1)z_p,1), S = Σ α [p^j | ·], the split S = S_0 + S_1 at p^j ≤ m/64, H_64, the hinge sums with threshold c,
   the LP/dual objects of Section 7 (the fractional cover and its value), the rounding and few-primes counts.
2. Erdos708/Chain/Cards.lean: cards for lem:largeatoms, thm:dense, cor:sparsecore (as "hinge_65_of_sparse_core"), lem:dual, lem:round,
   lem:fewprimes, thm:long, thm:cond (threshold-65 variant giving 81n), each faithful to the paper and ending in `:= by sorry`; plus the
   composition theorem linear_bound proved from the cards with no sorry in the composition itself. cards_readback.md: one blind line per card.
3. Leaves in this order (easiest first): lem:largeatoms, lem:fewprimes, thm:long, lem:round, lem:dual, thm:dense, thm:cond. Each leaf a
   separate file Erdos708/Chain/Proofs/<Name>.lean restating the card exactly and ending with `#print axioms`. A leaf that resists after a
   45-minute first pass is left as sorry with the exact remaining goal recorded; the judge (you) may return to it after the others.
Rules: compile after every change; PROVED only with 3 standard axioms and no sorry/admit/native_decide/custom axioms; no wall-clock cap —
continue until every card is proved or your approaches are genuinely exhausted; checkpoint.md every 30 minutes and report.md at the end
under engine/out/astra_708_lean3/ (per card: PROVED with axiom output, or OPEN with the remaining goal); no git; no internet.
