import Erdos708.H17.Cards
import Erdos708.H17.ChainParts.Weights
import Erdos708.H17.ChainParts.Proofs.Dual
import Erdos708.H17.ChainParts.Proofs.FewPrimes
import Erdos708.H17.ChainParts.Proofs.LongInterval
open Finset BigOperators
namespace Erdos708H17Chain.Proofs
/-- The conditional reduction at any natural threshold: the rounding cost adds 16 n. -/
theorem conditional_bound (c : ℕ)
    (hhinge : ∀ (z : Weight) (m : ℕ), 1 ≤ m → ∀ x : ℕ,
      hingeSum (w z) (c:ℝ) 0 m ≤ hingeSum (w z) 1 x m) (D : Problem) :
    ∃ B : Finset ℕ, Covers D B ∧ B.card ≤ (c+16) * D.n := by
  by_cases hlong : 8 * D.n ^ 3 ≤ D.m
  · obtain ⟨B, hB, hcard⟩ := long_interval D hlong
    exact ⟨B, hB, hcard.trans (Nat.mul_le_mul_right D.n (by omega : 2 ≤ c+16))⟩
  have hshort : D.m < 8 * D.n ^ 3 := lt_of_not_ge hlong
  obtain ⟨v, hv, hdual, hmax⟩ := dual D
  let z : Weight := ⟨D.primes, v, fun p hp => Nat.prime_of_mem_primeFactors hp, hv⟩
  have hm : 1 ≤ D.m := by
    have hh := D.two_le D.m (max'_mem D.A D.nonempty)
    omega
  have hH := hhinge z D.m hm D.x
  have hsum : (∑ a ∈ D.A, w z a) ≤ (c:ℝ) * (D.n : ℝ) + hingeSum (w z) (c:ℝ) 0 D.m := by
    have hpoint : (∑ a ∈ D.A, w z a) ≤ ∑ a ∈ D.A, ((c:ℝ) + max (w z a - (c:ℝ)) 0) := by
      apply sum_le_sum
      intro a ha
      have := le_max_left (w z a - (c:ℝ)) 0
      linarith
    have hsubset : (∑ a ∈ D.A, max (w z a - (c:ℝ)) 0) ≤
        ∑ k ∈ Icc 1 D.m, max (w z k - (c:ℝ)) 0 :=
      sum_le_sum_of_subset_of_nonneg (problem_subset_initial D) (fun _ _ _ => le_max_right _ _)
    simp only [sum_add_distrib, sum_const, nsmul_eq_mul] at hpoint
    simp only [hingeSum, zero_add]
    change _ ≤ (D.n : ℝ) * (c:ℝ) + _ at hpoint
    linarith
  have htau : fractionalValue D ≤ (c:ℝ) * (D.n : ℝ) := by
    rw [hdual]
    change (∑ a ∈ D.A, w z a) - hingeSum (w z) 1 D.x D.m ≤ _
    linarith
  obtain ⟨B, hB, hcard⟩ := rounding D
  have hprimes : (D.primes.card : ℝ) < 16 * (D.n : ℝ) := by
    exact_mod_cast few_primes D hshort
  refine ⟨B, hB, ?_⟩
  have hbound : (B.card : ℝ) ≤ ((c+16:ℕ):ℝ) * (D.n : ℝ) := by push_cast; nlinarith
  exact_mod_cast hbound


#print axioms conditional_bound
end Erdos708H17Chain.Proofs

namespace Erdos708H17

def toCore (A : Erdos708H17Chain.AtomSystem) : AtomSystem :=
  ⟨A.atoms,A.weight,A.prime_of_mem,A.weight_nonneg,A.perPrime_le_one⟩
lemma toCore_value (A : Erdos708H17Chain.AtomSystem) (n : ℕ) :
    S (toCore A) n = Erdos708H17Chain.S A n := rfl

lemma weighted_hinge17 (hh : Hinge17) : Erdos708H17Chain.Hinge17 := by
  intro z m hm x
  apply Erdos708H17Chain.Proofs.capped_to_weight
  apply Erdos708H17Chain.Proofs.atoms_to_capped
  have ha := hh (toCore (Erdos708H17Chain.Proofs.ofWeight z m)) m x
  simpa only [L,R,hingeSum,toCore_value,Erdos708H17Chain.hingeSum] using ha

/-- Threshold 17 plus the proved rounding cost 16 gives 33. -/
theorem conditional_33 (hh : Hinge17) (D : Erdos708H17Chain.Problem) :
    ∃ B : Finset ℕ, Erdos708H17Chain.Covers D B ∧ B.card ≤ 33*D.n := by
  exact Erdos708H17Chain.Proofs.conditional_bound 17 (weighted_hinge17 hh) D

/-- The atom hinge gives the stated product cover in every positive window. -/
theorem g_le_33n :
    ∀ (n : ℕ) (hn : 1 ≤ n), ∀ (A : Finset ℕ) (hA : A.card = n) (h2 : ∀ a ∈ A, 2 ≤ a) (x : ℕ),
      ∃ B ⊆ Finset.Icc (x+1) (x + A.max' (by
        have hp : 0 < A.card := by omega
        exact Finset.card_pos.mp hp)), B.card ≤ 33*n ∧ (∏ a ∈ A,a) ∣ (∏ b ∈ B,b) := by
  intro n hn A hA h2 x
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  let D : Erdos708H17Chain.Problem := ⟨A,hne,h2,x⟩
  have hh : Hinge17 := by
    intro A m x
    simpa only [L,R,hingeSum,zero_add] using hinge17 A m x
  obtain ⟨B,hB,hcard⟩ := conditional_33 hh D
  refine ⟨B,hB.1,?_,hB.2⟩
  simpa only [D,Erdos708H17Chain.Problem.n,hA] using hcard

#print axioms weighted_hinge17
#print axioms conditional_33
#print axioms g_le_33n
end Erdos708H17
