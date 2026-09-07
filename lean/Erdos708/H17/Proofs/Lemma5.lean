import Erdos708.H17.Proofs.CarrierResidual
import Erdos708.H17.Proofs.Capped
open Finset BigOperators
open scoped NNReal
namespace Erdos708H17.Proofs
noncomputable section
attribute [local instance] Classical.propDecidable

lemma mass_le_sum (A : AtomSystem) (m P : ℕ) (f : ℕ → ℝ)
    (hf : ∀ u, 0 ≤ f u)
    (hpoint : ∀ k ∈ hot A m, carrierAt A m k = P → B A m k - 11/2 ≤ f (k/P)) :
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

lemma scaled_residual (A : AtomSystem) (m k : ℕ) (hk : k ∈ hot A m) :
    B A m k - 11/2 = theta A m (carrierAt A m k) *
      ((∑ p ∈ (Rounded.primes (small A m)).filter (fun p => ¬ p ∣ carrierAt A m k),
        min (bp A m p (k / carrierAt A m k)) (theta A m (carrierAt A m k)) /
          theta A m (carrierAt A m k)) - (9/2 / theta A m (carrierAt A m k) - 1)) := by
  have hθ := theta_pos A m (carrierAt A m k)
  have hs := carrier_split A m k hk
  rw [carrier_mu_exact A m _ (mem_image_of_mem _ hk)] at hs
  have hsum : (∑ p ∈ (Rounded.primes (small A m)).filter (fun p => ¬ p ∣ carrierAt A m k),
      min (bp A m p (k / carrierAt A m k)) (theta A m (carrierAt A m k)) /
        theta A m (carrierAt A m k)) =
      (∑ p ∈ (Rounded.primes (small A m)).filter (fun p => ¬ p ∣ carrierAt A m k),
        bp A m p (k / carrierAt A m k)) / theta A m (carrierAt A m k) := by
    rw [sum_div]
    apply sum_congr rfl
    intro p hp
    rw [min_eq_left (bp_outside_le_theta A m k hk p (mem_filter.mp hp).2)]
  rw [hsum]
  field_simp
  linarith

lemma moment_order_pos (h : ℕ) : 1 ≤ momentOrder h := by
  unfold momentOrder
  split_ifs
  · omega
  · have hh : 1 ≤ (2:ℕ)^(h-1) := Nat.one_le_pow _ _ (by omega)
    omega

lemma scale_moment_order (h : ℕ) (hh : h ≠ 0) :
    (momentOrder h : ℝ) * (2:ℝ)⁻¹^h = 9/2 := by
  have hp : (2:ℝ)^h = (2:ℝ)^(h-1)*2 := by
    rw [← pow_succ]; congr 1; omega
  simp only [momentOrder, if_neg hh, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, inv_pow]
  rw [hp]
  field_simp
  <;> ring

lemma residual_esymm_bound (A : AtomSystem) (m k : ℕ) (hk : k ∈ hot A m)
    (h : ℕ) (hscale : theta A m (carrierAt A m k) = (2:ℝ)⁻¹^h) :
    B A m k - 11/2 ≤ (if h = 0 then (1/2 : ℝ) else theta A m (carrierAt A m k)) *
      esymm ((Rounded.primes (small A m)).filter (fun p => ¬ p ∣ carrierAt A m k))
        (fun p => min (bp A m p (k / carrierAt A m k)) (theta A m (carrierAt A m k)) /
          theta A m (carrierAt A m k)) (momentOrder h) := by
  let θ := theta A m (carrierAt A m k)
  let s := (Rounded.primes (small A m)).filter (fun p => ¬ p ∣ carrierAt A m k)
  let u := fun p => min (bp A m p (k/carrierAt A m k)) θ / θ
  have hθ : 0 < θ := theta_pos A m _
  have hu : ∀ p ∈ s, 0 ≤ u p ∧ u p ≤ 1 := by
    intro p hp
    exact ⟨div_nonneg (le_min (NNReal.coe_nonneg _) hθ.le) hθ.le,
      (div_le_one hθ).mpr (min_le_right _ _)⟩
  have hs := scaled_residual A m k hk
  change B A m k - 11/2 = θ * ((∑ p ∈ s, u p) - (9/2/θ-1)) at hs
  by_cases hh : h = 0
  · have ht : θ = 1 := by simpa only [hh,pow_zero] using hscale
    have he := (le_max_left _ _).trans (special_hinge s u hu)
    change B A m k - 11/2 ≤ (if h=0 then (1/2:ℝ) else θ) * esymm s u (momentOrder h)
    norm_num [hh, momentOrder] at ⊢
    norm_num [ht] at hs
    linarith
  · have hr := moment_order_pos h
    have horder : 9/2/θ - 1 = (momentOrder h - 1 : ℕ) := by
      have hh' : (momentOrder h : ℝ) * θ = 9/2 := by rw [show θ = (2:ℝ)⁻¹^h from hscale]; exact scale_moment_order h hh
      rw [Nat.cast_sub hr, Nat.cast_one]
      have heq : 9/2/θ = (momentOrder h : ℝ) := (div_eq_iff hθ.ne').mpr hh'.symm
      rw [heq]
    have he := (le_max_left _ _).trans (hinge_le_esymm s u hu (momentOrder h-1))
    have hrew : momentOrder h - 1 + 1 = momentOrder h := by omega
    simp only [hrew] at he
    rw [hs, horder, if_neg hh]
    exact mul_le_mul_of_nonneg_left he hθ.le

lemma coefficient_scale_bound (A : AtomSystem) (m : ℕ) (hm : 2^48 ≤ m)
    (hH : H A m < Hstar) (P : ℕ) (hP : P ∈ carriers A m)
    (h : ℕ) (hscale : theta A m P = (2:ℝ)⁻¹^h) : coefficient A m P ≤ epsilon h := by
  let θ := theta A m P
  let r := momentOrder h
  let a : ℝ := if h=0 then 1/2 else θ
  let s := (Rounded.primes (small A m)).filter (fun p => ¬ p ∣ P)
  let u := fun j p => min (bp A m p j) θ / θ
  let e := fun j => esymm s (u j) r
  have hθ : 0 < θ := theta_pos A m P
  have ha : 0 ≤ a := by dsimp [a]; split_ifs <;> positivity
  have he (j : ℕ) : 0 ≤ e j := esymm_nonneg s (u j)
    (fun p hp => div_nonneg (le_min (NNReal.coe_nonneg _) hθ.le) hθ.le) r
  have hmass : M A m P ≤ a * ∑ j ∈ Icc 1 (nu m P), e j := by
    rw [mul_sum]
    apply mass_le_sum A m P (fun j => a * e j) (fun j => mul_nonneg ha (he j))
    intro k hk hPk
    have hh := residual_esymm_bound A m k hk h (by rw [hPk]; exact hscale)
    rw [hPk] at hh
    exact hh
  have hmoment := Rounded.cap_moment (small A m) m (nu m P) r θ hθ s (filter_subset _ _)
  have hHB : Rounded.HB (small A m) m ≤ Hstar :=
    (Rounded.HB_le_mean (small A m) m).trans hH.le
  have hHB0 : 0 ≤ Rounded.HB (small A m) m := sum_nonneg (fun b hb =>
    div_nonneg (Rounded.increment_nonneg (small A m) m hb) (Nat.cast_nonneg _))
  have hmoment' : (∑ j ∈ Icc 1 (nu m P), e j) ≤
      (nu m P : ℝ) * (Hstar/θ)^r / (Nat.factorial r : ℝ) := by
    apply hmoment.trans
    gcongr
  have hnu : (0 : ℝ) < nu m P := by exact_mod_cast carrier_nu_pos A m (by omega) P hP
  have hcoeff : coefficient A m P ≤ a * (Hstar/θ)^r / (Nat.factorial r : ℝ) := by
    unfold coefficient
    apply (div_le_iff₀ hnu).mpr
    have hh := hmass.trans (mul_le_mul_of_nonneg_left hmoment' ha)
    convert hh using 1 <;> ring
  let t := a * (Hstar/θ)^r / (Nat.factorial r : ℝ)
  have hHstar0 : 0 ≤ Hstar := by norm_num [Hstar]
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hgamma : (1:ℝ) ≤ gamma := by norm_num [gamma]
  have heps : epsilon h = gamma * t := by
    by_cases hh : h = 0
    · have ht1 : θ = 1 := by simpa only [hh,pow_zero] using hscale
      simp only [epsilon, hh, t, a, r, momentOrder, ht1, div_one, ite_true, ↓reduceIte]
      ring
    · have hr : 1 ≤ r := moment_order_pos h
      have hθeq : θ = ((2:ℝ)^h)⁻¹ := by simpa only [inv_pow] using hscale
      have hp : ((2:ℝ)^h)^r = ((2:ℝ)^h)^(r-1) * (2:ℝ)^h := by
        rw [← pow_succ]; congr 1; omega
      simp only [epsilon, if_neg hh, t, a, hθeq, div_inv_eq_mul, mul_pow]
      rw [hp]
      field_simp
      <;> ring
  rw [heps]
  exact hcoeff.trans (by change t ≤ gamma*t; nlinarith)

#print axioms residual_esymm_bound
#print axioms coefficient_scale_bound
end
end Erdos708H17.Proofs
