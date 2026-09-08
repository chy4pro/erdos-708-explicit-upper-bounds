import Erdos708.H97.Proofs.PointwiseSupport
import Erdos708.H97.Proofs.CountBounds
open Finset BigOperators
namespace Erdos708H97.Proofs
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

lemma mass_scale_bound (A : AtomSystem) (m n h d : ℕ) (hd : 1 ≤ d)
    (e : ℝ) (he : 0 ≤ e)
    (heps : ∀ P ∈ scaleCarriers A m n h d, coefficient A m P ≤ e) :
    (∑ P ∈ scaleCarriers A m n h d, coefficient A m P*(1-U A m P n/K)) ≤
      (carrierCount (Rounded.scaleJ h) (Rounded.scaleL h) d (activePrimes A m n h).card : ℝ)*e*
        countRatio (Rounded.scaleJ h) (Rounded.scaleL h) d (activePrimes A m n h).card*
        max (B A m n-1) 0 := by
  let D := scaleCarriers A m n h d
  let N := (activePrimes A m n h).card
  let j := Rounded.scaleJ h
  let L := Rounded.scaleL h
  let c := max (1-max 0 ((N : ℝ)*j/L-1-d/L)/K) 0
  let den := max ((d : ℝ)/L) ((N : ℝ)*j/L-1)
  have hL : (0 : ℝ) < L := by exact_mod_cast Rounded.scaleL_pos h
  have hc : 0 ≤ c := le_max_right _ _
  have hdenpos : 0 < den := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hk : (0 : ℝ) < K := by norm_num [K]
  have hb : 0 ≤ max (B A m n-1) 0 := le_max_right _ _
  have hmu (P : ℕ) (hP : P ∈ D) : mu A m P = 1+(d : ℝ)/L := by
    have hp := mem_filter.mp hP
    rw [carrier_mass_scale A m P hp.1,hp.2.2.1,hp.2.2.2]
  by_cases hD : D.Nonempty
  · obtain ⟨P0,hP0⟩ := hD
    have hden : den ≤ max (B A m n-1) 0 := by
      have hh := B_scale_lower A m n h d P0 hP0
      rw [hmu P0 hP0,Rounded.level_scale] at hh
      simpa only [den,N,j,L,add_sub_cancel_left,mul_div_assoc] using hh
    have hbound (P : ℕ) (hP : P ∈ D) : coefficient A m P*(1-U A m P n/K) ≤ e*c := by
      have hl := U_scale_lower A m n h d P hP
      rw [hmu P hP,Rounded.level_scale] at hl
      have hl' : max 0 ((N : ℝ)*j/L-1-d/L) ≤ U A m P n := by
        simpa only [sub_add_eq_sub_sub,mul_div_assoc] using hl
      have hclip : 1-U A m P n/K ≤ c :=
        (sub_le_sub_left (div_le_div_of_nonneg_right hl' hk.le) 1).trans (le_max_left _ _)
      exact (mul_le_mul_of_nonneg_left hclip (coefficient_nonneg A m P)).trans
        (mul_le_mul_of_nonneg_right (heps P hP) hc)
    have hcount : (D.card : ℝ) ≤ carrierCount j L d N := by exact_mod_cast carrier_count_exact A m n h d
    have hr : e*c ≤ (e*c/den)*max (B A m n-1) 0 := by
      calc
        _ = (e*c/den)*den := (div_mul_cancel₀ _ hdenpos.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hden (div_nonneg (mul_nonneg he hc) hdenpos.le)
    calc
      _ ≤ ∑ _P ∈ D, e*c := sum_le_sum hbound
      _ = (D.card : ℝ)*(e*c) := by simp
      _ ≤ (carrierCount j L d N : ℝ)*(e*c) := mul_le_mul_of_nonneg_right hcount (mul_nonneg he hc)
      _ ≤ (carrierCount j L d N : ℝ)*((e*c/den)*max (B A m n-1) 0) := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg _)
      _ = _ := by change _ = (carrierCount j L d N : ℝ)*e*(c/den)*_; ring
  · rw [show scaleCarriers A m n h d = ∅ from not_nonempty_iff_eq_empty.mp hD,sum_empty]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) he) (countRatio_nonneg _ _ _ _)) hb

def heightCarriers (A : AtomSystem) (m n h : ℕ) : Finset ℕ :=
  (carriers A m).filter (fun P => P ∣ n ∧ carrierHeight A m P = h)

lemma height_sum_eq (A : AtomSystem) (m n h : ℕ) :
    (∑ P ∈ heightCarriers A m n h, coefficient A m P*(1-U A m P n/K)) =
      ∑ d ∈ Icc 1 (Rounded.scaleJ h), ∑ P ∈ scaleCarriers A m n h d,
        coefficient A m P*(1-U A m P n/K) := by
  have hmap : ∀ P ∈ heightCarriers A m n h, carrierMassIndex A m P ∈ Icc 1 (Rounded.scaleJ h) := by
    intro P hP
    have hp := mem_filter.mp hP
    have hd := carrier_degree_bounds A m P hp.1
    rw [hp.2.2] at hd
    exact mem_Icc.mpr ⟨hd.1,hd.2.1⟩
  rw [← sum_fiberwise_of_maps_to hmap]
  apply sum_congr rfl
  intro d hd
  apply sum_congr
  · ext P
    simp only [heightCarriers,scaleCarriers,mem_filter]
    tauto
  · intros; rfl

lemma finite_height_bound (A : AtomSystem) (m : ℕ) (hH : H A m < Hstar) (n h : ℕ) :
    (∑ P ∈ heightCarriers A m n h, coefficient A m P*(1-U A m P n/K)) ≤
      AScale (Rounded.scaleJ h) (Rounded.scaleL h)*max (B A m n-1) 0 := by
  let j := Rounded.scaleJ h
  let L := Rounded.scaleL h
  have hj : 0 < j := by have := (Rounded.scaleJ_bounds h).1; omega
  have hL : 0 < L := Rounded.scaleL_pos h
  rw [height_sum_eq]
  calc
    _ ≤ ∑ d ∈ Icc 1 j,
        (carrierCount j L d (activePrimes A m n h).card : ℝ)*epsilon ((j : ℝ)/L) (1+(d : ℝ)/L)*
          countRatio j L d (activePrimes A m n h).card*max (B A m n-1) 0 := by
      apply sum_le_sum
      intro d hd
      apply mass_scale_bound A m n h d (mem_Icc.mp hd).1 _ (epsilon_nonneg _ _ (by positivity))
      intro P hP
      have hp := mem_filter.mp hP
      have hh := coefficient_bound A m hH P hp.1
      rw [carrier_mass_scale A m P hp.1,theta_scale,hp.2.2.1,hp.2.2.2] at hh
      exact hh
    _ = scaleValue j L (activePrimes A m n h).card*max (B A m n-1) 0 := by rw [← sum_mul]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right (scaleValue_le_AScale j L _ hj hL) (le_max_right _ _)

lemma tail_height_bound (A : AtomSystem) (m n h : ℕ)
    (heps : ∀ P ∈ carriers A m, coefficient A m P ≤ tailEpsilon (theta A m P)) :
    (∑ P ∈ heightCarriers A m n h, coefficient A m P*(1-U A m P n/K)) ≤
      tailAScale (Rounded.scaleJ h) (Rounded.scaleL h)*max (B A m n-1) 0 := by
  let j := Rounded.scaleJ h
  let L := Rounded.scaleL h
  have hj : 0 < j := by have := (Rounded.scaleJ_bounds h).1; omega
  have hL : 0 < L := Rounded.scaleL_pos h
  rw [height_sum_eq]
  calc
    _ ≤ ∑ d ∈ Icc 1 j,
        (carrierCount j L d (activePrimes A m n h).card : ℝ)*tailEpsilon ((j : ℝ)/L)*
          countRatio j L d (activePrimes A m n h).card*max (B A m n-1) 0 := by
      apply sum_le_sum
      intro d hd
      apply mass_scale_bound A m n h d (mem_Icc.mp hd).1 _ (tailEpsilon_nonneg _ (by positivity))
      intro P hP
      have hp := mem_filter.mp hP
      have hh := heps P hp.1
      rw [theta_scale,hp.2.2.1] at hh
      exact hh
    _ = tailScaleValue j L (activePrimes A m n h).card*max (B A m n-1) 0 := by rw [← sum_mul]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right (tailScaleValue_le_AScale j L _ hj hL) (le_max_right _ _)

#print axioms finite_height_bound
#print axioms tail_height_bound
end
end Erdos708H97.Proofs
