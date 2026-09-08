import Erdos708.H97.Proofs.ExponentialMoment
import Erdos708.H97.Proofs.Lemma5
import Erdos708.H97.Proofs.ScalarConstants
open Finset BigOperators
namespace Erdos708H97.Proofs
noncomputable section
set_option maxHeartbeats 2000000

lemma log_z_bounds : (3/2 : ℝ) < Real.log (9/2) ∧ 4 < Real.exp 1*Real.log (9/2) := by
  have he := exp_one_bounds
  have hp0 : (Real.exp 1)^3 < (87/32 : ℝ)^3 := by gcongr; exact he.2
  have hp : (Real.exp 1)^3 < (9/2 : ℝ)^2 := hp0.trans log_z_aux
  have hlog := Real.log_lt_log (by positivity : (0:ℝ)<(Real.exp 1)^3) hp
  rw [Real.log_pow,Real.log_exp,Real.log_pow] at hlog
  constructor
  · linarith
  · nlinarith

lemma chernoff_log_base : (7/2)*Hstar-(441/100)*Real.log (9/2) < Real.log a0 := by
  have h1 := Real.log_lt_log (Real.exp_pos _) exp_Hstar_upper
  rw [Real.log_exp] at h1
  have h2 := Real.log_lt_log (by positivity : (0:ℝ)<(133/4:ℝ)^100) chernoff_base_rational
  rw [Real.log_mul (pow_ne_zero _ (by norm_num [a0])) (by norm_num),Real.log_pow,Real.log_pow,Real.log_pow] at h2
  norm_num only [Nat.cast_ofNat] at h2
  linarith

lemma coefficient_exponential (A : AtomSystem) (m : ℕ) (hH : H A m < Hstar)
    (P : ℕ) (hP : P ∈ carriers A m) (t : ℝ) (ht : 0 < t) :
    coefficient A m P ≤ theta A m P/(Real.exp 1*t)*
      Real.exp (((Real.exp t-1)*Hstar-t*(T-mu A m P))/theta A m P) := by
  let θ := theta A m P
  let a := (T-mu A m P)/θ
  let s := (Rounded.primes (small A m)).filter (fun p => ¬ p ∣ P)
  let u := fun j p => min (bp A m p j) θ/θ
  have hθ : 0 < θ := theta_pos A m P
  have hden : 0 < Real.exp 1*t := mul_pos (Real.exp_pos _) ht
  have hu : ∀ j ∈ Icc 1 (nu m P), ∀ p ∈ s, 0 ≤ u j p ∧ u j p ≤ 1 := by
    intro j hj p hp
    exact ⟨div_nonneg (le_min (Rounded.bp_nonneg (small A m) m p j) hθ.le) hθ.le,
      (div_le_one hθ).mpr (min_le_right _ _)⟩
  have hHB : Rounded.HB (small A m) m ≤ Hstar := (Rounded.HB_le_mean (small A m) m).trans hH.le
  have hHB0 : 0 ≤ Rounded.HB (small A m) m := sum_nonneg (fun b hb =>
    div_nonneg (Rounded.increment_nonneg (small A m) m hb) (Nat.cast_nonneg _))
  have hmom (r : ℕ) : (∑ j ∈ Icc 1 (nu m P), esymm s (u j) r) ≤
      (nu m P : ℝ)*(Hstar/θ)^r/(Nat.factorial r : ℝ) := by
    apply (Rounded.cap_moment (small A m) m (nu m P) r θ hθ s (filter_subset _ _)).trans
    gcongr
  have hexp := finite_exponential_moment s u (nu m P) (Hstar/θ) t
    (div_nonneg (by norm_num [Hstar]) hθ.le) ht.le hu hmom
  let c := θ/(Real.exp 1*t)*Real.exp (-t*a)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hmass : M A m P ≤ c*∑ j ∈ Icc 1 (nu m P), Real.exp (t*∑ p ∈ s, u j p) := by
    rw [mul_sum]
    apply mass_le_sum A m P _ (fun j => mul_nonneg hc (Real.exp_pos _).le)
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
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left
      ((le_max_left _ _).trans (hinge_exp_bound ((∑ p ∈ s, u (k/P) p)-a) t ht)) hθ.le
    exact hh.trans_eq (by
      dsimp only [c]
      rw [mul_sub,Real.exp_sub,neg_mul,Real.exp_neg]
      ring)
  have hnu : (0 : ℝ) < nu m P := by exact_mod_cast carrier_nu_pos A m P hP
  unfold coefficient
  apply (div_le_iff₀ hnu).mpr
  have hh := hmass.trans (mul_le_mul_of_nonneg_left hexp hc)
  convert hh using 1
  dsimp only [c,a,θ]
  have hid : ((Real.exp t-1)*Hstar-t*(T-mu A m P))/theta A m P =
      -t*((T-mu A m P)/theta A m P)+(Real.exp t-1)*(Hstar/theta A m P) := by ring
  rw [hid,Real.exp_add]
  ring

lemma coefficient_tail_bound (A : AtomSystem) (m : ℕ) (hH : H A m < Hstar)
    (P : ℕ) (hP : P ∈ carriers A m) :
    coefficient A m P ≤ tailEpsilon (theta A m P) := by
  let θ := theta A m P
  let t := Real.log (9/2)
  have hθ : 0 < θ := theta_pos A m P
  have ht : 0 < t := by dsimp [t]; linarith [log_z_bounds.1]
  have hmu := carrier_mu_upper A m P hP
  have hbase := chernoff_log_base
  have harg : ((Real.exp t-1)*Hstar-t*(T-mu A m P))/θ ≤ t+Real.log a0/θ := by
    rw [Real.exp_log (by norm_num : (0:ℝ)<9/2)]
    apply (div_le_iff₀ hθ).mpr
    have hid : (t+Real.log a0/θ)*θ = t*θ+Real.log a0 := by field_simp
    rw [hid]
    dsimp only [t,T] at *
    nlinarith
  have hh := (coefficient_exponential A m hH P hP t ht).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity))
  apply hh.trans
  rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<9/2)]
  have hid : Real.exp (Real.log a0/θ) = a0^(1/θ) := by
    rw [Real.rpow_def_of_pos (by norm_num [a0])]
    congr 1
    ring
  rw [hid]
  change θ/(Real.exp 1*t)*((9/2)*a0^(1/θ)) ≤ 9*θ/8*a0^(1/θ)
  have hd : 4 ≤ Real.exp 1*t := log_z_bounds.2.le
  have hc : θ/(Real.exp 1*t) ≤ θ/4 := div_le_div_of_nonneg_left hθ.le (by norm_num) hd
  nlinarith [Real.rpow_pos_of_pos (by norm_num [a0] : (0:ℝ)<a0) (1/θ)]

#print axioms coefficient_tail_bound
end
end Erdos708H97.Proofs
