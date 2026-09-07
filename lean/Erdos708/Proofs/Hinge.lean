import Mathlib

open Finset BigOperators

namespace Erdos708SparseCore

private lemma esymm_insert {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (x : ι → ℝ) (a : ι) (ha : a ∉ s) (k : ℕ) :
    (∑ t ∈ (insert a s).powersetCard (k + 1), ∏ i ∈ t, x i) =
      (∑ t ∈ s.powersetCard (k + 1), ∏ i ∈ t, x i) +
      x a * ∑ t ∈ s.powersetCard k, ∏ i ∈ t, x i := by
  rw [powersetCard_succ_insert ha, sum_union]
  · congr 1
    rw [sum_image, mul_sum]
    · apply sum_congr rfl
      intro t ht
      exact prod_insert (fun hat => ha ((mem_powersetCard.mp ht).1 hat))
    · intro t ht u hu heq
      have hat : a ∉ t := fun h => ha ((mem_powersetCard.mp ht).1 h)
      have hau : a ∉ u := fun h => ha ((mem_powersetCard.mp hu).1 h)
      simpa [hat, hau] using congrArg (erase · a) heq
  · apply disjoint_left.mpr
    intro t ht ht'
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ht'
    exact ha ((mem_powersetCard.mp ht).1 (mem_insert_self _ _))

 theorem hinge_le_esymm {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1)
    (C : ℕ) :
    max (∑ i ∈ s, x i - C) 0 ≤ ∑ t ∈ s.powersetCard (C + 1), ∏ i ∈ t, x i := by
  classical
  induction s using Finset.induction_on generalizing C with
  | empty =>
    have hempty : (∅ : Finset ι).powersetCard (C + 1) = ∅ :=
      powersetCard_eq_empty.mpr (by simp)
    simp [hempty]
  | @insert a s ha ih =>
    have hxa := hx a (mem_insert_self _ _)
    have hxs : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1 := fun i hi => hx i (mem_insert_of_mem hi)
    have hnonneg (k : ℕ) : 0 ≤ ∑ t ∈ s.powersetCard k, ∏ i ∈ t, x i := by
      apply sum_nonneg
      intro t ht
      exact prod_nonneg (fun i hi => (hxs i ((mem_powersetCard.mp ht).1 hi)).1)
    cases C with
    | zero =>
      simp only [Nat.cast_zero, sub_zero, Nat.zero_add, powersetCard_one, sum_map,
        Function.Embedding.coeFn_mk, prod_singleton]
      exact max_le (le_refl _) (sum_nonneg fun i hi => (hx i hi).1)
    | succ C =>
      rw [sum_insert ha, esymm_insert s x a ha (C + 1)]
      apply max_le
      · have h₁ := (le_max_left _ _).trans (ih hxs (C + 1))
        have h₂ := (le_max_left _ _).trans (ih hxs C)
        calc
          x a + ∑ i ∈ s, x i - (C + 1 : ℕ) =
              (1 - x a) * ((∑ i ∈ s, x i) - (C + 1 : ℕ)) +
              x a * ((∑ i ∈ s, x i) - (C : ℝ)) := by push_cast; ring
          _ ≤ (1 - x a) * (∑ t ∈ s.powersetCard (C + 1 + 1), ∏ i ∈ t, x i) +
              x a * (∑ t ∈ s.powersetCard (C + 1), ∏ i ∈ t, x i) :=
            add_le_add (mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr hxa.2))
              (mul_le_mul_of_nonneg_left h₂ hxa.1)
          _ ≤ _ := by nlinarith [mul_nonneg hxa.1 (hnonneg (C + 1 + 1))]
      · exact add_nonneg (hnonneg _) (mul_nonneg hxa.1 (hnonneg _))

#print axioms hinge_le_esymm

end Erdos708SparseCore
