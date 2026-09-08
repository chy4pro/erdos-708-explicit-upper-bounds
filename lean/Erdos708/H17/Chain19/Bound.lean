import Erdos708.H17.Chain19.Rounding
import Erdos708.H17.Chain19.Ksplit

open Finset BigOperators
namespace Erdos708H17Chain.Chain19
open Erdos708H17Chain.Proofs

/-- The dual estimate accepts any real hinge threshold. -/
lemma fractionalValue_le_of_hinge (c : ℝ)
    (hhinge : ∀ (z : Weight) (m : ℕ), 1 ≤ m → ∀ x : ℕ,
      hingeSum (w z) c 0 m ≤ hingeSum (w z) 1 x m) (D : Problem) :
    fractionalValue D ≤ c * D.n := by
  obtain ⟨v, hv, hdual, hmax⟩ := dual D
  let z : Weight := ⟨D.primes, v, fun p hp => Nat.prime_of_mem_primeFactors hp, hv⟩
  have hm : 1 ≤ D.m := by
    have hh := D.two_le D.m (max'_mem D.A D.nonempty)
    omega
  have hH := hhinge z D.m hm D.x
  have hsum : (∑ a ∈ D.A, w z a) ≤ c * (D.n : ℝ) + hingeSum (w z) c 0 D.m := by
    have hpoint : (∑ a ∈ D.A, w z a) ≤ ∑ a ∈ D.A, (c + max (w z a - c) 0) := by
      apply sum_le_sum
      intro a ha
      have := le_max_left (w z a - c) 0
      linarith
    have hsubset : (∑ a ∈ D.A, max (w z a - c) 0) ≤
        ∑ k ∈ Icc 1 D.m, max (w z k - c) 0 :=
      sum_le_sum_of_subset_of_nonneg (problem_subset_initial D) (fun _ _ _ => le_max_right _ _)
    simp only [sum_add_distrib, sum_const, nsmul_eq_mul] at hpoint
    simp only [hingeSum, zero_add]
    change _ ≤ (D.n : ℝ) * c + _ at hpoint
    linarith
  have htau : fractionalValue D ≤ c * (D.n : ℝ) := by
    rw [hdual]
    change (∑ a ∈ D.A, w z a) - hingeSum (w z) 1 D.x D.m ≤ _
    linarith
  exact htau

/-- A real hinge threshold `c ≥ 1` costs at most `⌈c n⌉ + 2 n` elements. -/
theorem bound_of_hinge (c : ℝ) (hc : 1 ≤ c)
    (hhinge : ∀ (z : Weight) (m : ℕ), 1 ≤ m → ∀ x : ℕ,
      hingeSum (w z) c 0 m ≤ hingeSum (w z) 1 x m) (D : Problem) :
    ∃ B, Covers D B ∧ B.card ≤ ⌈c * D.n⌉₊ + 2 * D.n := by
  classical
  have hceil := Nat.le_ceil (c * (D.n : ℝ))
  by_cases hlong : 9 * D.n ^ 2 ≤ D.m
  · obtain ⟨B,hB,hcard⟩ := ksplit3 D hlong
    have hnceil : D.n ≤ ⌈c * D.n⌉₊ := by
      have hnR : (D.n : ℝ) ≤ c * D.n := by nlinarith [Nat.cast_nonneg D.n (α := ℝ)]
      exact_mod_cast hnR.trans hceil
    exact ⟨B,hB,by omega⟩
  have hsqrt : Nat.sqrt D.m < 3 * D.n := Nat.sqrt_lt'.mpr (by nlinarith)
  have hpi : ((range (Nat.sqrt D.m + 1)).filter Nat.Prime).card ≤ D.n + 1 := by
    apply le_trans (card_le_card ?_) (pi_le D.n)
    intro p hp
    obtain ⟨hr,hp⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hr; omega),hp⟩
  have hr : D.primes.card ≤ 2 * D.n + 1 := by have := primes_card_le D; omega
  have htau := fractionalValue_le_of_hinge c hhinge D
  obtain ⟨B,hB,hcard⟩ := strict_rounding D
  have hrR : (D.primes.card : ℝ) ≤ 2 * (D.n : ℝ) + 1 := by exact_mod_cast hr
  have hltR : (B.card : ℝ) < (⌈c * D.n⌉₊ : ℝ) + 2 * (D.n : ℝ) + 1 := by linarith
  have hlt : B.card < ⌈c * D.n⌉₊ + 2 * D.n + 1 := by exact_mod_cast hltR
  exact ⟨B,hB,by omega⟩

#print axioms fractionalValue_le_of_hinge
#print axioms bound_of_hinge
end Erdos708H17Chain.Chain19
