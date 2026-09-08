import Erdos708.H97.Proofs.Lemma5
open Finset BigOperators
namespace Erdos708H97.Proofs
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

lemma epsilon_le_moment (θ s : ℝ) (r : ℕ) (hr : r ∈ momentRange θ s) :
    epsilon θ s ≤ momentBound θ s r := by
  have hne : (momentRange θ s).Nonempty := ⟨r,hr⟩
  rw [epsilon,dif_pos hne]
  exact inf'_le (momentBound θ s) hr

lemma epsilon_nonneg (θ s : ℝ) (hθ : 0 < θ) : 0 ≤ epsilon θ s := by
  unfold epsilon
  split_ifs with hne
  · apply le_inf'
    intro r hr
    have hr' := mem_Icc.mp hr
    have hfpos : 0 < ⌊(T-s)/θ⌋₊ := by omega
    have ha1 : 1 ≤ (T-s)/θ := Nat.floor_pos.mp hfpos
    have hf := Nat.floor_le (show 0 ≤ (T-s)/θ by linarith)
    have hrr : (r : ℝ) ≤ (⌊(T-s)/θ⌋₊ : ℝ)+1 := by exact_mod_cast hr'.2
    have hra : (r : ℝ)-1 ≤ (T-s)/θ := by linarith
    have hv := maximizingVertex_bounds ((T-s)/θ) r hr'.1 hra
    have hC : 0 ≤ hingeMajorant ((T-s)/θ) r := div_nonneg (sub_nonneg.mpr hv.2.1.le) (Nat.cast_nonneg _)
    unfold momentBound
    exact div_nonneg (mul_nonneg (mul_nonneg hθ.le hC) (pow_nonneg (div_nonneg (by norm_num [Hstar]) hθ.le) r)) (Nat.cast_nonneg _)
  · exact le_rfl

lemma countRatio_nonneg (j L d N : ℕ) : 0 ≤ countRatio j L d N := by unfold countRatio; positivity
lemma scaleValue_nonneg (j L N : ℕ) (hj : 0 < j) (hL : 0 < L) : 0 ≤ scaleValue j L N := by
  apply sum_nonneg
  intro d hd
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (epsilon_nonneg _ _ (by positivity))) (countRatio_nonneg j L d N)
lemma AScale_nonneg (j L : ℕ) (hj : 0 < j) (hL : 0 < L) : 0 ≤ AScale j L :=
  (scaleValue_nonneg j L 0 hj hL).trans (le_sup' (scaleValue j L) (by simp))
lemma tailEpsilon_nonneg (θ : ℝ) (hθ : 0 ≤ θ) : 0 ≤ tailEpsilon θ := by
  unfold tailEpsilon a0
  positivity
lemma tailScaleValue_nonneg (j L N : ℕ) : 0 ≤ tailScaleValue j L N := by
  apply sum_nonneg
  intro d hd
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (tailEpsilon_nonneg _ (by positivity))) (countRatio_nonneg j L d N)
lemma tailAScale_nonneg (j L : ℕ) : 0 ≤ tailAScale j L :=
  (tailScaleValue_nonneg j L 0).trans (le_sup' (tailScaleValue j L) (by simp))

lemma countRatio_zero_of_large (j L d N : ℕ) (hj : 0 < j) (hL : 0 < L)
    (hd : d ≤ j) (hN : countLimit j L < N) : countRatio j L d N = 0 := by
  have hlim : 1 ≤ countLimit j L := Nat.le_add_left 1 _
  have hN0 : 1 ≤ N := hlim.trans hN.le
  have hdiv : (11*L)/(3*j) < N-1 := by unfold countLimit at hN; omega
  have hnat : 11*L < (N-1)*(3*j) := (Nat.div_lt_iff_lt_mul (by positivity : 0 < 3*j)).mp hdiv
  have hreal : (11 : ℝ)*L < ((N : ℝ)-1)*(3*j) := by
    have hh := congrArg (fun t : ℕ => (t : ℝ)) (Nat.sub_add_cancel hN0)
    exact_mod_cast hnat
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hdr : (d : ℝ) ≤ j := by exact_mod_cast hd
  have hclip : K ≤ (N : ℝ)*j/L-1-d/L := by
    have hform : (N : ℝ)*j/L-1-d/L = ((N : ℝ)*j-L-d)/L := by field_simp
    rw [hform]
    apply (le_div_iff₀ hLr).mpr
    norm_num [K]
    nlinarith
  have hk : (0 : ℝ) < K := by norm_num [K]
  have he : max (1-max 0 ((N : ℝ)*j/L-1-d/L)/K) 0 = 0 := by
    apply max_eq_right
    have hh : 1 ≤ max 0 ((N : ℝ)*j/L-1-d/L)/K :=
      (le_div_iff₀ hk).mpr (by simpa using hclip.trans (le_max_right _ _))
    linarith
  simp only [countRatio,he,zero_div]

lemma scaleValue_le_AScale (j L N : ℕ) (hj : 0 < j) (hL : 0 < L) : scaleValue j L N ≤ AScale j L := by
  by_cases hN : N ≤ countLimit j L
  · exact le_sup' (scaleValue j L) (mem_range.mpr (by omega))
  · have he : scaleValue j L N = 0 := by
      apply sum_eq_zero
      intro d hd
      rw [countRatio_zero_of_large j L d N hj hL (mem_Icc.mp hd).2 (by omega),mul_zero]
    rw [he]
    exact AScale_nonneg j L hj hL
lemma tailScaleValue_le_AScale (j L N : ℕ) (hj : 0 < j) (hL : 0 < L) : tailScaleValue j L N ≤ tailAScale j L := by
  by_cases hN : N ≤ countLimit j L
  · exact le_sup' (tailScaleValue j L) (mem_range.mpr (by omega))
  · have he : tailScaleValue j L N = 0 := by
      apply sum_eq_zero
      intro d hd
      rw [countRatio_zero_of_large j L d N hj hL (mem_Icc.mp hd).2 (by omega),mul_zero]
    rw [he]
    exact tailAScale_nonneg j L

#print axioms countRatio_zero_of_large
end
end Erdos708H97.Proofs
