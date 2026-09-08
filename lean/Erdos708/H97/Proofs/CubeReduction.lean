import Erdos708.H97.Proofs.MomentBasics
open Finset BigOperators
namespace Erdos708H97.Proofs
noncomputable section
set_option maxHeartbeats 2000000

/-- G6: iterate one coordinate at a time; a separately concave function is bounded
below by its minimum over the vertices of the finite cube. -/
lemma cube_lower {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : (ι → ℝ) → ℝ)
    (hf : ∀ u i, i ∈ s → 0 ≤ u i → u i ≤ 1 →
      min (f (Function.update u i 0)) (f (Function.update u i 1)) ≤ f u)
    (hv : ∀ u, (∀ i ∈ s, u i = 0 ∨ u i = 1) → 0 ≤ f u)
    (u : ι → ℝ) (hu : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1) : 0 ≤ f u := by
  generalize hn : (s.filter (fun i => u i ≠ 0 ∧ u i ≠ 1)).card = n
  induction n using Nat.strong_induction_on generalizing u with
  | h n ih =>
    by_cases hz : n = 0
    · apply hv u
      intro i hi
      by_contra hh
      have hm : i ∈ s.filter (fun i => u i ≠ 0 ∧ u i ≠ 1) := mem_filter.mpr ⟨hi,by tauto⟩
      have he := card_eq_zero.mp (hn.trans hz)
      rw [he] at hm
      exact notMem_empty _ hm
    · have hs : (s.filter (fun i => u i ≠ 0 ∧ u i ≠ 1)).Nonempty := card_pos.mp (by omega)
      obtain ⟨i,hi⟩ := hs
      have hiS := (mem_filter.mp hi).1
      have hup (b : ℝ) (hb : b = 0 ∨ b = 1) : 0 ≤ f (Function.update u i b) := by
        have hcube : ∀ j ∈ s, 0 ≤ Function.update u i b j ∧ Function.update u i b j ≤ 1 := by
          intro j hj
          by_cases hji : j = i
          · subst j; simp only [Function.update_self]; rcases hb with rfl | rfl <;> norm_num
          · simpa [Function.update_of_ne hji] using hu j hj
        have he : s.filter (fun j => Function.update u i b j ≠ 0 ∧ Function.update u i b j ≠ 1) =
            (s.filter (fun j => u j ≠ 0 ∧ u j ≠ 1)).erase i := by
          ext j
          by_cases hji : j = i
          · subst j; rcases hb with rfl | rfl <;> simp
          · simp [Function.update_of_ne hji, hji]
        have hlt : (s.filter (fun j => Function.update u i b j ≠ 0 ∧ Function.update u i b j ≠ 1)).card < n := by
          rw [he,card_erase_of_mem hi,hn]
          omega
        exact ih _ hlt _ hcube rfl
      exact (le_min (hup 0 (Or.inl rfl)) (hup 1 (Or.inr rfl))).trans
        (hf u i hiS (hu i hiS).1 (hu i hiS).2)

lemma esymm_update_affine {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι → ℝ)
    (i : ι) (r : ℕ) :
    esymm s u r = (1-u i)*esymm s (Function.update u i 0) r +
      u i*esymm s (Function.update u i 1) r := by
  simp only [Erdos708H17.esymm,mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro t ht
  by_cases hi : i ∈ t
  · rw [prod_update_of_mem hi,prod_update_of_mem hi,← prod_erase_mul _ _ hi,sdiff_singleton_eq_erase]
    ring
  · rw [prod_update_of_notMem hi,prod_update_of_notMem hi]
    ring

lemma vertex_esymm {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, u i = 0 ∨ u i = 1) (r : ℕ) :
    esymm s u r = (((s.filter (fun i => u i = 1)).card).choose r : ℝ) := by
  let t := s.filter (fun i => u i = 1)
  have hprod : ∀ v ∈ t.powersetCard r, (∏ i ∈ v, u i) = 1 := by
    intro v hv
    apply prod_eq_one
    intro i hi
    exact (mem_filter.mp ((mem_powersetCard.mp hv).1 hi)).2
  have hs : (∑ v ∈ t.powersetCard r, ∏ i ∈ v, u i) = esymm s u r := by
    apply sum_subset (powersetCard_mono (filter_subset _ _))
    intro v hv hn
    have hnsub : ¬ v ⊆ t := by
      intro h
      exact hn (mem_powersetCard.mpr ⟨h,(mem_powersetCard.mp hv).2⟩)
    obtain ⟨i,hiv,hit⟩ := not_subset.mp hnsub
    have his := (mem_powersetCard.mp hv).1 hiv
    have hz : u i = 0 := (hu i his).resolve_right (fun h => hit (mem_filter.mpr ⟨his,h⟩))
    exact prod_eq_zero hiv hz
  rw [← hs,sum_congr rfl hprod]
  simp [card_powersetCard,t]

lemma vertex_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, u i = 0 ∨ u i = 1) :
    (∑ i ∈ s, u i) = ((s.filter (fun i => u i = 1)).card : ℝ) := by
  calc
    _ = ∑ i ∈ s, if u i = 1 then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro i hi
      rcases hu i hi with h | h <;> simp [h]
    _ = _ := by simp

lemma hinge_of_vertex_bound {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1) (a C : ℝ) (r : ℕ)
    (hv : ∀ h : ℕ, max ((h : ℝ)-a) 0 ≤ C*(h.choose r : ℝ)) :
    max (∑ i ∈ s, u i-a) 0 ≤ C*esymm s u r := by
  let f := fun v : ι → ℝ => C*esymm s v r-max (∑ i ∈ s, v i-a) 0
  have hh : 0 ≤ f u := by
    apply cube_lower s f _ _ u hu
    · intro v i hi hv0 hv1
      have he := esymm_update_affine s v i r
      have hs0 : (∑ j ∈ s, Function.update v i 0 j) = (∑ j ∈ s.erase i, v j) := by
        rw [sum_update_of_mem hi,sdiff_singleton_eq_erase]; ring
      have hs1 : (∑ j ∈ s, Function.update v i 1 j) = 1+(∑ j ∈ s.erase i, v j) := by
        rw [sum_update_of_mem hi,sdiff_singleton_eq_erase]
      have hs : (∑ j ∈ s, v j) = v i+(∑ j ∈ s.erase i, v j) := (add_sum_erase _ _ hi).symm
      have hmax : max (∑ j ∈ s, v j-a) 0 ≤
          (1-v i)*max ((∑ j ∈ s.erase i, v j)-a) 0 +
          v i*max (1+(∑ j ∈ s.erase i, v j)-a) 0 := by
        apply max_le
        · rw [hs]
          nlinarith [mul_le_mul_of_nonneg_left (le_max_left ((∑ j ∈ s.erase i, v j)-a) 0) (sub_nonneg.mpr hv1),
            mul_le_mul_of_nonneg_left (le_max_left (1+(∑ j ∈ s.erase i, v j)-a) 0) hv0]
        · positivity
      have hmin0 := min_le_left (f (Function.update v i 0)) (f (Function.update v i 1))
      have hmin1 := min_le_right (f (Function.update v i 0)) (f (Function.update v i 1))
      have h0 := mul_le_mul_of_nonneg_left hmin0 (sub_nonneg.mpr hv1)
      have h1 := mul_le_mul_of_nonneg_left hmin1 hv0
      dsimp only [f] at *
      simp only [hs0,hs1] at *
      nlinarith [congrArg (fun z : ℝ => C*z) he]
    · intro v hv'
      dsimp only [f]
      rw [vertex_esymm s v hv',vertex_sum s v hv']
      exact sub_nonneg.mpr (hv _)
  exact sub_nonneg.mp hh

#print axioms hinge_of_vertex_bound
end
end Erdos708H97.Proofs
