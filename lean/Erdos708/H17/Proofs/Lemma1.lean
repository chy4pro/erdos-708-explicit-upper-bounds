import Erdos708.H17.Defs
open Finset BigOperators
namespace Erdos708H17.Proofs
noncomputable section
lemma esymm_insert {ι : Type*} [DecidableEq ι] (s : Finset ι)
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


lemma esymm_nonneg {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i) (r : ℕ) : 0 ≤ esymm s u r := by
  apply sum_nonneg
  intro t ht
  exact prod_nonneg (fun i hi => hu i ((mem_powersetCard.mp ht).1 hi))

lemma special_hinge_aux {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1) :
    (2 * (∑ i ∈ s, u i) - 7 ≤ esymm s u 4) ∧
    (2 * (∑ i ∈ s, u i) - 5 ≤ esymm s u 4 + esymm s u 3) ∧
    (2 * (∑ i ∈ s, u i) - 3 ≤ esymm s u 4 + 2*esymm s u 3 + esymm s u 2) ∧
    (2 * (∑ i ∈ s, u i) - 1 ≤ esymm s u 4 + 3*esymm s u 3 + 3*esymm s u 2 + esymm s u 1) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hz (r : ℕ) (hr : 0 < r) : esymm (∅ : Finset ι) u r = 0 := by
      rw [esymm, powersetCard_eq_empty.mpr (by simpa using hr), sum_empty]
    norm_num [hz 4 (by omega), hz 3 (by omega), hz 2 (by omega), hz 1 (by omega)]
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1 := fun i hi => hu i (mem_insert_of_mem hi)
    obtain ⟨h0,h1,h2,h3⟩ := ih hs
    have hx := hu a (mem_insert_self _ _)
    have en (r : ℕ) := esymm_nonneg s u (fun i hi => (hs i hi).1) r
    have e1 : esymm s u 1 = ∑ i ∈ s, u i := by simp [esymm, powersetCard_one]
    have e0 : esymm s u 0 = 1 := by simp [esymm, powersetCard_zero]
    have ei (r : ℕ) : esymm (insert a s) u (r+1) = esymm s u (r+1) + u a * esymm s u r :=
      esymm_insert s u a ha r
    rw [sum_insert ha, ei 3, ei 2, ei 1, ei 0, e0]
    have c0 := mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr h0)
    have c1 := mul_nonneg hx.1 (sub_nonneg.mpr h1)
    have c2 := mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr h1)
    have c3 := mul_nonneg hx.1 (sub_nonneg.mpr h2)
    have c4 := mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr h2)
    have c5 := mul_nonneg hx.1 (sub_nonneg.mpr h3)
    have c6 := mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr h3)
    have h4 : 2 * (∑ i ∈ s, u i) + 1 ≤
        esymm s u 4 + 4*esymm s u 3 + 6*esymm s u 2 + 4*esymm s u 1 + 1 := by
      nlinarith [en 4, en 3, en 2, en 1]
    have c7 := mul_nonneg hx.1 (sub_nonneg.mpr h4)
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith

lemma special_hinge {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1) :
    max (∑ i ∈ s, u i - 7/2) 0 ≤ (1/2) * esymm s u 4 := by
  apply max_le
  · linarith [(special_hinge_aux s u hu).1]
  · exact mul_nonneg (by norm_num) (esymm_nonneg s u (fun i hi => (hu i hi).1) 4)

#print axioms hinge_le_esymm
#print axioms special_hinge
end
end Erdos708H17.Proofs
