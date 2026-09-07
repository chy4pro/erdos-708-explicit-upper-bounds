import Erdos708.Chain.Proofs.LargeAtoms
import Erdos708.Chain.Proofs.FewPrimes
import Erdos708.Chain.Proofs.LongInterval
import Erdos708.Chain.Proofs.Rounding
import Erdos708.Chain.Proofs.Dual
import Erdos708.Chain.Proofs.Dense
import Erdos708.Chain.Proofs.Conditional81
import Erdos708.Chain.Proofs.Hinge65

namespace Erdos708Chain
open Finset BigOperators

/-- Section 13, Lemma large atoms. k is positive, as throughout the paper. -/
theorem large_atoms (A : AtomSystem) (m : ℕ) (hm : 4096 ≤ m) :
    (∀ k ∈ Icc 1 m, S1 A m k ≤ 1) ∧
    (∀ k ∈ Icc 1 m, max (S A k - 65) 0 ≤ max (S0 (small A m) k - 64) 0) ∧
    (∀ b : ℕ, max (S0 (small A m) b - 1) 0 ≤ max (S A b - 1) 0) := by
  exact Proofs.large_atoms A m hm

/-- Section 13, dense branch; the atom-system conclusion and its weight consequence. -/
theorem dense :
    (∀ (A : AtomSystem) (m : ℕ), 1 ≤ m → 17 / 16 ≤ H64 A m → ∀ x : ℕ,
      hingeSum (S A) 65 0 m ≤ hingeSum (S A) 1 x m) ∧
    (∀ (z : Weight) (m : ℕ), 1 ≤ m → 17 / 16 ≤ weightH64 z m → ∀ x : ℕ,
      hingeSum (w z) 65 0 m ≤ hingeSum (w z) 1 x m) := by
  exact Proofs.dense

/-- Section 13, sparse-core reduction, including the capped-to-additive peel. -/
theorem hinge_65_of_sparse_core (hsc : sparse_core_hyp) : Hinge65 := by
  exact Proofs.hinge_65_of_sparse_core hsc

/-- Section 7, duality: the full nonnegative dual has a maximizer in the unit cube. -/
theorem dual (D : Problem) :
    ∃ z : ℕ → ℝ, (∀ p ∈ D.primes, 0 ≤ z p ∧ z p ≤ 1) ∧
      fractionalValue D = dualObjective D z ∧
      ∀ z' : ℕ → ℝ, (∀ p ∈ D.primes, 0 ≤ z' p) →
        dualObjective D z' ≤ dualObjective D z := by
  exact Proofs.dual D

/-- Section 7, rounding the fractional optimum. -/
theorem rounding (D : Problem) :
    ∃ B : Finset ℕ, Covers D B ∧ (B.card : ℝ) ≤ fractionalValue D + D.primes.card := by
  exact Proofs.rounding D

/-- Section 7, few primes. -/
theorem few_primes (D : Problem) (hm : D.m < 8 * D.n ^ 3) :
    D.primes.card < 16 * D.n := by
  exact Proofs.few_primes D hm

/-- Section 5, long intervals. -/
theorem long_interval (D : Problem) (hm : 8 * D.n ^ 3 ≤ D.m) :
    ∃ B : Finset ℕ, Covers D B ∧ B.card ≤ 2 * D.n := by
  exact Proofs.long_interval D hm

/-- Section 7, conditional theorem with threshold 65 instead of 2. -/
theorem conditional_81 (hhinge : Hinge65) (D : Problem) :
    ∃ B : Finset ℕ, Covers D B ∧ B.card ≤ 81 * D.n := by
  exact Proofs.conditional_81 hhinge D

/-- Section 1 uses "at most g", including windows shorter than the bound.
The only explicit external hypothesis is the independently stated sparse core. -/
theorem linear_bound (hsc : sparse_core_hyp) :
    ∀ (n : ℕ) (hn : 1 ≤ n), ∀ (A : Finset ℕ) (hA : A.card = n) (h2 : ∀ a ∈ A, 2 ≤ a) (x : ℕ),
      ∃ B ⊆ Finset.Icc (x+1) (x + A.max' (by
        have hp : 0 < A.card := by omega
        exact Finset.card_pos.mp hp)), B.card ≤ 81 * n ∧ (∏ a ∈ A, a) ∣ (∏ b ∈ B, b) := by
  intro n hn A hA h2 x
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  let D : Problem := ⟨A, hne, h2, x⟩
  obtain ⟨B, hB, hcard⟩ := conditional_81 (hinge_65_of_sparse_core hsc) D
  refine ⟨B, hB.1, ?_, hB.2⟩
  simpa [D, Problem.n, hA] using hcard

#print axioms large_atoms
#print axioms dense
#print axioms hinge_65_of_sparse_core
#print axioms dual
#print axioms rounding
#print axioms few_primes
#print axioms long_interval
#print axioms conditional_81
#print axioms linear_bound
end Erdos708Chain
