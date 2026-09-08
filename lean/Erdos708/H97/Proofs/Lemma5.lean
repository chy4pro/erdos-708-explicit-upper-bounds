import Erdos708.H97.Proofs.Cofactor
import Erdos708.H97.Proofs.Capped
import Erdos708.H97.Proofs.ScalarHinge
open Finset BigOperators
namespace Erdos708H97
namespace Proofs
noncomputable section
set_option maxHeartbeats 2000000
lemma mass_le_sum (A : AtomSystem) (m P : ℕ) (f : ℕ → ℝ)
    (hf : ∀ u, 0 ≤ f u)
    (hpoint : ∀ k ∈ hot A m, carrierAt A m k = P → B A m k - T ≤ f (k/P)) :
    M A m P ≤ ∑ u ∈ Icc 1 (nu m P), f u := by
  classical
  let s := (hot A m).filter (fun k => carrierAt A m k = P)
  have hdiv (k : ℕ) (hk : k ∈ s) : P ∣ k := by
    rw [← (mem_filter.mp hk).2]
    exact carrier_divides A m k
  have hmap : ∀ k ∈ s, k/P ∈ Icc 1 (nu m P) := by
    intro k hk
    have hkm := mem_Icc.mp (mem_filter.mp (mem_filter.mp hk).1).1
    have heq : P * (k/P) = k := Nat.mul_div_cancel' (hdiv k hk)
    refine mem_Icc.mpr ⟨?_, Nat.div_le_div_right hkm.2⟩
    have hh : k/P ≠ 0 := by intro hz; rw [hz,mul_zero] at heq; omega
    exact Nat.one_le_iff_ne_zero.mpr hh
  have hinj : Set.InjOn (fun k => k/P) (s : Set ℕ) := by
    intro k hk l hl he
    calc
      k = P * (k/P) := (Nat.mul_div_cancel' (hdiv k hk)).symm
      _ = P * (l/P) := congrArg (P * ·) he
      _ = l := Nat.mul_div_cancel' (hdiv l hl)
  calc
    _ ≤ ∑ k ∈ s, f (k/P) := sum_le_sum (fun k hk => hpoint k (mem_filter.mp hk).1 (mem_filter.mp hk).2)
    _ = ∑ u ∈ s.image (fun k => k/P), f u := by rw [sum_image hinj]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (image_subset_iff.mpr hmap) (fun u _ _ => hf u)


lemma carrier_parameter_bounds (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) :
    3 ≤ (T-mu A m P)/theta A m P := by
  have hθ := theta_pos A m P
  have hθ1 := theta_le_one A m P
  have hmu := carrier_mu_upper A m P hP
  apply (le_div_iff₀ hθ).mpr
  norm_num [T]
  linarith

lemma coefficient_moment_bound (A : AtomSystem) (m : ℕ) (hH : H A m < Hstar)
    (P : ℕ) (hP : P ∈ carriers A m) (r : ℕ) (hr : 2 ≤ r)
    (hra : (r : ℝ)-1 ≤ (T-mu A m P)/theta A m P) :
    coefficient A m P ≤ momentBound (theta A m P) (mu A m P) r := by
  let θ := theta A m P
  let a := (T-mu A m P)/θ
  let C := hingeMajorant a r
  let s := (Rounded.primes (small A m)).filter (fun p => ¬ p ∣ P)
  let u := fun j p => min (bp A m p j) θ/θ
  let e := fun j => esymm s (u j) r
  have hθ : 0 < θ := theta_pos A m P
  have hC : 0 ≤ C := div_nonneg (sub_nonneg.mpr (maximizingVertex_bounds a r hr hra).2.1.le) (Nat.cast_nonneg _)
  have he (j : ℕ) : 0 ≤ e j := esymm_nonneg s (u j)
    (fun p _ => div_nonneg (le_min (Rounded.bp_nonneg (small A m) m p j) hθ.le) hθ.le) r
  have hmass : M A m P ≤ θ*C*∑ j ∈ Icc 1 (nu m P), e j := by
    rw [mul_sum]
    apply mass_le_sum A m P (fun j => θ*C*e j) (fun j => mul_nonneg (mul_nonneg hθ.le hC) (he j))
    intro k hk hPk
    have hsplit := carrier_split A m k hk
    rw [hPk] at hsplit
    have hsum : (∑ p ∈ s, u (k/P) p) = (∑ p ∈ s, bp A m p (k/P))/θ := by
      rw [sum_div]
      apply sum_congr rfl
      intro p hp
      change min (bp A m p (k/P)) θ/θ = _
      have hb := bp_outside_le_theta A m k hk p (by rw [hPk]; exact (mem_filter.mp hp).2)
      rw [hPk] at hb
      rw [min_eq_left hb]
    have hid : B A m k-T = θ*((∑ p ∈ s, u (k/P) p)-a) := by
      rw [hsum]
      dsimp only [a]
      field_simp
      linarith
    have hu : ∀ p ∈ s, 0 ≤ u (k/P) p ∧ u (k/P) p ≤ 1 := by
      intro p hp
      exact ⟨div_nonneg (le_min (Rounded.bp_nonneg (small A m) m p (k/P)) hθ.le) hθ.le,
        (div_le_one hθ).mpr (min_le_right _ _)⟩
    have hh := (le_max_left _ _).trans (optimized_hinge s (u (k/P)) hu a r hr hra)
    rw [hid]
    exact (mul_le_mul_of_nonneg_left hh hθ.le).trans_eq (by ring)
  have hmoment := Rounded.cap_moment (small A m) m (nu m P) r θ hθ s (filter_subset _ _)
  have hHB : Rounded.HB (small A m) m ≤ Hstar := (Rounded.HB_le_mean (small A m) m).trans hH.le
  have hHB0 : 0 ≤ Rounded.HB (small A m) m := sum_nonneg (fun b hb =>
    div_nonneg (Rounded.increment_nonneg (small A m) m hb) (Nat.cast_nonneg _))
  have hmoment' : (∑ j ∈ Icc 1 (nu m P), e j) ≤
      (nu m P : ℝ)*(Hstar/θ)^r/(Nat.factorial r : ℝ) := by
    apply hmoment.trans
    gcongr
  have hnu : (0 : ℝ) < nu m P := by exact_mod_cast carrier_nu_pos A m P hP
  unfold coefficient
  apply (div_le_iff₀ hnu).mpr
  have hh := hmass.trans (mul_le_mul_of_nonneg_left hmoment' (mul_nonneg hθ.le hC))
  convert hh using 1 <;> dsimp [momentBound,θ,C,a] <;> ring

lemma coefficient_bound (A : AtomSystem) (m : ℕ) (hH : H A m < Hstar)
    (P : ℕ) (hP : P ∈ carriers A m) :
    coefficient A m P ≤ epsilon (theta A m P) (mu A m P) := by
  have ha := carrier_parameter_bounds A m P hP
  have hfloor : 3 ≤ ⌊(T-mu A m P)/theta A m P⌋₊ := Nat.le_floor ha
  have hne : (momentRange (theta A m P) (mu A m P)).Nonempty :=
    ⟨2,mem_Icc.mpr ⟨le_rfl,by omega⟩⟩
  rw [epsilon,dif_pos hne]
  apply le_inf'
  intro r hr
  have hr' := mem_Icc.mp hr
  apply coefficient_moment_bound A m hH P hP r hr'.1
  have hf : (⌊(T-mu A m P)/theta A m P⌋₊ : ℝ) ≤ (T-mu A m P)/theta A m P :=
    Nat.floor_le (by linarith)
  have hrr : (r : ℝ) ≤ (⌊(T-mu A m P)/theta A m P⌋₊ : ℝ)+1 := by exact_mod_cast hr'.2
  linarith
end
end Proofs

theorem lemma5 (A : AtomSystem) (m : ℕ) (hH : H A m < Hstar) :
    ∀ P ∈ carriers A m, 0 ≤ coefficient A m P ∧
      coefficient A m P ≤ epsilon (theta A m P) (mu A m P) := by
  intro P hP
  exact ⟨Proofs.coefficient_nonneg A m P,Proofs.coefficient_bound A m hH P hP⟩
#print axioms lemma5
end Erdos708H97
