import Erdos708.H17.Proofs.CarrierCount
open Finset BigOperators
open scoped NNReal
namespace Erdos708H17.Proofs
noncomputable section
attribute [local instance] Classical.propDecidable

lemma epsilon_nonneg (h : ℕ) : 0 ≤ epsilon h := by
  unfold epsilon gamma Hstar
  split_ifs <;> positivity
lemma countRatio_nonneg (h N : ℕ) : 0 ≤ countRatio h N := by unfold countRatio; positivity
lemma Rscale_nonneg (h : ℕ) : 0 ≤ Rscale h :=
  (countRatio_nonneg h 0).trans (le_sup' (countRatio h) (by simp))
lemma numericTerm_nonneg (h : ℕ) : 0 ≤ numericTerm h :=
  mul_nonneg (mul_nonneg (by norm_num) (epsilon_nonneg h)) (Rscale_nonneg h)

lemma countRatio_le_Rscale (h N : ℕ) : countRatio h N ≤ Rscale h := by
  by_cases hN : N ≤ countLimit h
  · exact le_sup' (countRatio h) (mem_range.mpr (by omega))
  · have he : (0:ℝ) < 2^h := by positivity
    have hmod := Nat.mod_lt (51*2^h) (by omega : 0 < 16)
    have hdecomp := Nat.mod_add_div (51*2^h) 16
    have hfloor : 51*2^h < 16*(51*2^h/16+1) := by omega
    have hNnat : 51*2^h < 16*(N-1) := by unfold countLimit at hN; omega
    have hN1 : 1 ≤ N := by unfold countLimit at hN; omega
    have hNr : (51:ℝ)*2^h < 16*((N:ℝ)-1) := by exact_mod_cast hNnat
    have hq : K ≤ ((N:ℝ)-2^h-1)/2^h := by
      apply (le_div_iff₀ he).mpr
      norm_num [K]
      linarith
    have hc : max (1 - max 0 (((N:ℝ)-2^h-1)/2^h)/K) 0 = 0 := by
      apply max_eq_right
      have hk : (0:ℝ) < K := by norm_num [K]
      have hh : 1 ≤ max 0 (((N:ℝ)-2^h-1)/2^h)/K :=
        (le_div_iff₀ hk).mpr (by simpa using hq.trans (le_max_right _ _))
      linarith
    simp only [countRatio,hc,mul_zero,zero_div]
    exact Rscale_nonneg h

lemma U_scale_lower (A : AtomSystem) (m n h P : ℕ) (hP : P ∈ scaleCarriers A m n h) :
    max 0 (((activePrimes A m n h).card : ℝ) * (2:ℝ)⁻¹^h - 1 - (2:ℝ)⁻¹^h) ≤ U A m P n := by
  have hp := mem_filter.mp hP
  have ht : theta A m P = (2:ℝ)⁻¹^h := by rw [theta_eq_height,hp.2.2]
  let t := Rounded.primes (small A m)
  let θ := theta A m P
  have hθ := theta_pos A m P
  have hU0 : 0 ≤ U A m P n := sum_nonneg (fun p hp => le_min (NNReal.coe_nonneg _) hθ.le)
  have hpart : (∑ p ∈ t.filter (fun p => p ∣ P), min (bp A m p n) θ) ≤ mu A m P := by
    calc
      _ ≤ ∑ p ∈ t.filter (fun p => p ∣ P), bp A m p P := by
        apply sum_le_sum
        intro p hpp
        obtain ⟨a,ha,hap⟩ := mem_image.mp (mem_filter.mp hpp).1
        have hprime : Nat.Prime p := hap ▸ ((small A m).prime_of_mem a ha).1
        obtain ⟨b,hb,hbp⟩ := (prime_dvd_carrier A m P p hp.1 hprime).mp (mem_filter.mp hpp).2
        have hheight := (carrier_data A m P hp.1).2.2.2 b hb
        have hlevel : theta A m P ≤ (Rounded.levelValue (small A m) b : ℝ) := by
          exact_mod_cast pow_le_pow_of_le_one (by positivity : (0:ℝ≥0) ≤ 2⁻¹)
            (by norm_num : (2:ℝ≥0)⁻¹ ≤ 1) hheight
        apply (min_le_right _ _).trans
        rw [← hbp]
        exact hlevel.trans_eq (Rounded.effective_value_eq_bp (small A m) m P b hb).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun p _ _ => NNReal.coe_nonneg _)
  have hT : ((activePrimes A m n h).card : ℝ) * (2:ℝ)⁻¹^h ≤ ∑ p ∈ t, min (bp A m p n) θ := by
    calc
      _ = ∑ p ∈ activePrimes A m n h, min (bp A m p n) θ := by
        have he : ∀ p ∈ activePrimes A m n h, min (bp A m p n) θ = θ := by
          intro p hp
          apply min_eq_right
          change theta A m P ≤ _
          rw [ht]
          exact (mem_filter.mp hp).2
        rw [sum_congr rfl he, sum_const, nsmul_eq_mul]
        change _ = _ * theta A m P
        rw [ht]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun p _ _ => le_min (NNReal.coe_nonneg _) hθ.le)
  have hsplit : (∑ p ∈ t, min (bp A m p n) θ) =
      (∑ p ∈ t.filter (fun p => p ∣ P), min (bp A m p n) θ) + U A m P n :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  rw [carrier_mu_exact A m P hp.1, ht] at hpart
  apply max_le hU0
  linarith

lemma B_scale_lower (A : AtomSystem) (m n h P : ℕ) (hP : P ∈ scaleCarriers A m n h) :
    max (1/(2:ℝ)^h) ((((activePrimes A m n h).card : ℝ)-2^h)/2^h) ≤ max (B A m n - 1) 0 := by
  have hp := mem_filter.mp hP
  have ht : theta A m P = (2:ℝ)⁻¹^h := by rw [theta_eq_height,hp.2.2]
  have hmono : mu A m P ≤ B A m n := Rounded.B_dvd_mono (small A m) m hp.2.1
  rw [carrier_mu_exact A m P hp.1,ht] at hmono
  have hN : ((activePrimes A m n h).card : ℝ) * (2:ℝ)⁻¹^h ≤ B A m n := by
    calc
      _ = ∑ _p ∈ activePrimes A m n h, (2:ℝ)⁻¹^h := by simp
      _ ≤ ∑ p ∈ activePrimes A m n h, bp A m p n := sum_le_sum (fun p hp => (mem_filter.mp hp).2)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => NNReal.coe_nonneg _)
  have he : ((activePrimes A m n h).card : ℝ) * (2:ℝ)⁻¹^h - 1 =
      (((activePrimes A m n h).card : ℝ)-2^h)/2^h := by simp only [inv_pow]; field_simp <;> ring
  have ht' : (2:ℝ)⁻¹^h = 1/(2:ℝ)^h := by simp [inv_pow]
  have hmax := le_max_left (B A m n - 1) 0
  apply max_le <;> linarith

lemma scale_sum_bound (A : AtomSystem) (m : ℕ) (hm : 2^48 ≤ m) (hH : H A m < Hstar) (n h : ℕ) :
    (∑ P ∈ scaleCarriers A m n h, coefficient A m P * (1-U A m P n/K)) ≤
      epsilon h * Rscale h * max (B A m n-1) 0 := by
  let D := scaleCarriers A m n h
  let N := (activePrimes A m n h).card
  let c := max (1 - max 0 (((N:ℝ)-2^h-1)/2^h)/K) 0
  let d := max (1/(2:ℝ)^h) (((N:ℝ)-2^h)/2^h)
  have hc : 0 ≤ c := le_max_right _ _
  have hd : 0 < d := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hk : (0:ℝ) < K := by norm_num [K]
  have hb : 0 ≤ max (B A m n-1) 0 := le_max_right _ _
  by_cases hD : D.Nonempty
  · obtain ⟨P0,hP0⟩ := hD
    have hden : d ≤ max (B A m n-1) 0 := B_scale_lower A m n h P0 hP0
    have hbound (P : ℕ) (hP : P ∈ D) : coefficient A m P * (1-U A m P n/K) ≤ epsilon h * c := by
      have hp := mem_filter.mp hP
      have heps := coefficient_scale_bound A m hm hH P hp.1 h (by rw [theta_eq_height,hp.2.2])
      have hl := U_scale_lower A m n h P hP
      have heq : ((N:ℝ)-2^h-1)/2^h = (N:ℝ)*(2:ℝ)⁻¹^h - 1 - (2:ℝ)⁻¹^h := by
        simp only [inv_pow]; field_simp <;> ring
      have hclip : 1-U A m P n/K ≤ c := by
        dsimp [c]
        rw [heq]
        exact (sub_le_sub_left (div_le_div_of_nonneg_right hl hk.le) 1).trans (le_max_left _ _)
      exact (mul_le_mul_of_nonneg_left hclip (coefficient_nonneg A m P)).trans
        (mul_le_mul_of_nonneg_right heps hc)
    have hcount : (D.card : ℝ) ≤ carrierCount h N := by exact_mod_cast carrier_count_exact A m n h
    have hratio : (carrierCount h N : ℝ)*c/d ≤ Rscale h := countRatio_le_Rscale h N
    have hnum : (carrierCount h N : ℝ)*c ≤ Rscale h * max (B A m n-1) 0 := by
      have hh := (div_le_iff₀ hd).mp hratio
      exact hh.trans (mul_le_mul_of_nonneg_left hden (Rscale_nonneg h))
    calc
      _ ≤ ∑ _P ∈ D, epsilon h * c := sum_le_sum hbound
      _ = (D.card:ℝ)*(epsilon h*c) := by simp
      _ ≤ (carrierCount h N:ℝ)*(epsilon h*c) := mul_le_mul_of_nonneg_right hcount (mul_nonneg (epsilon_nonneg h) hc)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hnum (epsilon_nonneg h)]
  · rw [show scaleCarriers A m n h = ∅ from not_nonempty_iff_eq_empty.mp hD, sum_empty]
    exact mul_nonneg (mul_nonneg (epsilon_nonneg h) (Rscale_nonneg h)) hb

lemma counting_reduction (A : AtomSystem) (m : ℕ) (hm : 2^48 ≤ m) (hH : H A m < Hstar)
    (hs : Summable numericTerm) (n : ℕ) :
    F A m n ≤ (∑' h, numericTerm h) * max (B A m n-1) 0 := by
  classical
  let D := (carriers A m).filter (fun P => P ∣ n)
  let heights := D.image (carrierHeight A m)
  have hsplit : F A m n = 24 * ∑ h ∈ heights,
      ∑ P ∈ scaleCarriers A m n h, coefficient A m P * (1-U A m P n/K) := by
    unfold F
    rw [← sum_filter]
    congr 1
    rw [← sum_fiberwise_of_maps_to (fun P hP => mem_image_of_mem (carrierHeight A m) hP)]
    apply sum_congr rfl
    intro h hh
    apply sum_congr
    · ext P
      simp only [D,scaleCarriers,mem_filter]
      tauto
    · intros; rfl
  rw [hsplit]
  calc
    _ ≤ 24 * ∑ h ∈ heights, epsilon h * Rscale h * max (B A m n-1) 0 :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun h hh => scale_sum_bound A m hm hH n h)) (by norm_num)
    _ = (∑ h ∈ heights, numericTerm h) * max (B A m n-1) 0 := by
      simp only [numericTerm, mul_sum, sum_mul]
      apply sum_congr rfl
      intros
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hs.sum_le_tsum heights (fun h _ => numericTerm_nonneg h)) (le_max_right _ _)

#print axioms counting_reduction
end
end Erdos708H17.Proofs
