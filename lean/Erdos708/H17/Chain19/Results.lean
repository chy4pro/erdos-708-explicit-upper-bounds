import Erdos708.H17.Chain
import Erdos708.H17.Chain19.Bound

open Finset BigOperators
namespace Erdos708H17Chain.Chain19

/-- The proved threshold-17 hinge gives an unconditional `19 n` cover. -/
theorem g_le_19n :
    ∀ (n : ℕ) (hn : 1 ≤ n), ∀ (A : Finset ℕ) (hA : A.card = n)
      (h2 : ∀ a ∈ A, 2 ≤ a) (x : ℕ),
      ∃ B ⊆ Finset.Icc (x+1) (x + A.max' (Finset.card_pos.mp (by omega))),
        B.card ≤ 19*n ∧ (∏ a ∈ A, a) ∣ (∏ b ∈ B, b) := by
  intro n hn A hA h2 x
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  let D : Problem := ⟨A,hne,h2,x⟩
  have hh : Erdos708H17.Hinge17 := by
    intro A m x
    simpa only [Erdos708H17.L, Erdos708H17.R, Erdos708H17.hingeSum, zero_add]
      using Erdos708H17.hinge17 A m x
  obtain ⟨B,hB,hcard⟩ := bound_of_hinge 17 (by norm_num)
    (Erdos708H17.weighted_hinge17 hh) D
  have hceil : ⌈(17 : ℝ) * D.n⌉₊ ≤ 17 * D.n := by
    apply Nat.ceil_le.mpr
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    exact le_rfl
  refine ⟨B,hB.1,?_,hB.2⟩
  have hnD : D.n = n := hA
  rw [hnD] at hcard hceil
  omega

/-- Threshold `97/10` would give a `12 n` cover, for every positive `n`. -/
theorem g_le_12n_of_hinge
    (h : ∀ (z : Weight) (m : ℕ), 1 ≤ m → ∀ x : ℕ,
      hingeSum (w z) (97/10 : ℝ) 0 m ≤ hingeSum (w z) 1 x m) :
    ∀ (n : ℕ) (hn : 1 ≤ n), ∀ (A : Finset ℕ) (hA : A.card = n)
      (h2 : ∀ a ∈ A, 2 ≤ a) (x : ℕ),
      ∃ B ⊆ Finset.Icc (x+1) (x + A.max' (Finset.card_pos.mp (by omega))),
        B.card ≤ 12*n ∧ (∏ a ∈ A, a) ∣ (∏ b ∈ B, b) := by
  intro n hn A hA h2 x
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  let D : Problem := ⟨A,hne,h2,x⟩
  obtain ⟨B,hB,hcard⟩ := bound_of_hinge (97/10) (by norm_num) h D
  have hceil : ⌈(97/10 : ℝ) * D.n⌉₊ ≤ 10 * D.n := by
    apply Nat.ceil_le.mpr
    push_cast
    nlinarith [Nat.cast_nonneg D.n (α := ℝ)]
  refine ⟨B,hB.1,?_,hB.2⟩
  have hnD : D.n = n := hA
  rw [hnD] at hcard hceil
  omega

#print axioms g_le_19n
#print axioms g_le_12n_of_hinge
end Erdos708H17Chain.Chain19
