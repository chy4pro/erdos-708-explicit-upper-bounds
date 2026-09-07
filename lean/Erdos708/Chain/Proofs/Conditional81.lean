import Erdos708.Chain.Proofs.Dual
import Erdos708.Chain.Proofs.FewPrimes
import Erdos708.Chain.Proofs.LongInterval

namespace Erdos708Chain.Proofs
open Finset BigOperators

/-- Exact restatement of the threshold-65 conditional card. -/
theorem conditional_81 (hhinge : Hinge65) (D : Problem) :
    ∃ B : Finset ℕ, Covers D B ∧ B.card ≤ 81 * D.n := by
  by_cases hlong : 8 * D.n ^ 3 ≤ D.m
  · obtain ⟨B, hB, hcard⟩ := long_interval D hlong
    exact ⟨B, hB, hcard.trans (by omega)⟩
  have hshort : D.m < 8 * D.n ^ 3 := lt_of_not_ge hlong
  obtain ⟨v, hv, hdual, hmax⟩ := dual D
  let z : Weight := ⟨D.primes, v, fun p hp => Nat.prime_of_mem_primeFactors hp, hv⟩
  have hm : 1 ≤ D.m := by
    have hh := D.two_le D.m (max'_mem D.A D.nonempty)
    omega
  have hH := hhinge z D.m hm D.x
  have hsum : (∑ a ∈ D.A, w z a) ≤ 65 * (D.n : ℝ) + hingeSum (w z) 65 0 D.m := by
    have hpoint : (∑ a ∈ D.A, w z a) ≤ ∑ a ∈ D.A, (65 + max (w z a - 65) 0) := by
      apply sum_le_sum
      intro a ha
      have := le_max_left (w z a - 65) 0
      linarith
    have hsubset : (∑ a ∈ D.A, max (w z a - 65) 0) ≤
        ∑ k ∈ Icc 1 D.m, max (w z k - 65) 0 :=
      sum_le_sum_of_subset_of_nonneg (problem_subset_initial D) (fun _ _ _ => le_max_right _ _)
    simp only [sum_add_distrib, sum_const, nsmul_eq_mul] at hpoint
    simp only [hingeSum, zero_add]
    change _ ≤ (D.n : ℝ) * 65 + _ at hpoint
    linarith
  have htau : fractionalValue D ≤ 65 * (D.n : ℝ) := by
    rw [hdual]
    change (∑ a ∈ D.A, w z a) - hingeSum (w z) 1 D.x D.m ≤ _
    linarith
  obtain ⟨B, hB, hcard⟩ := rounding D
  have hprimes : (D.primes.card : ℝ) < 16 * (D.n : ℝ) := by
    exact_mod_cast few_primes D hshort
  refine ⟨B, hB, ?_⟩
  have hbound : (B.card : ℝ) ≤ 81 * (D.n : ℝ) := by linarith
  exact_mod_cast hbound

#print axioms conditional_81
end Erdos708Chain.Proofs
