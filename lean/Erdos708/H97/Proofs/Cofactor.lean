import Erdos708.H97.Proofs.CarrierResidual
open Finset BigOperators
namespace Erdos708H97.Proofs
noncomputable section
set_option maxHeartbeats 2000000

/-- G1: the outside mass exceeds three, so at least four distinct primes divide k/P. -/
lemma source_cofactor_ge_210 (A : AtomSystem) (m k : ℕ) (hk : k ∈ hot A m) :
    210 ≤ k/carrierAt A m k := by
  classical
  let P := carrierAt A m k
  let u := k/P
  let s := (Rounded.primes (small A m)).filter (fun p => ¬ p ∣ P)
  let t := s.filter (fun p => 0 < bp A m p u)
  have hP : P ∈ carriers A m := mem_image_of_mem _ hk
  have hsplit := carrier_split A m k hk
  have hmu : mu A m P ≤ 2 := (carrier_mu_upper A m P hP).trans (by linarith [theta_le_one A m P])
  have hh : T < B A m k := (mem_filter.mp hk).2
  have hmass : 3 < ∑ p ∈ s, bp A m p u := by
    change B A m k = mu A m P + ∑ p ∈ s, bp A m p u at hsplit
    norm_num [T] at hh
    linarith
  have hsum : (∑ p ∈ s, bp A m p u) = ∑ p ∈ t, bp A m p u := by
    symm
    apply sum_subset (filter_subset _ _)
    intro p hp hn
    have hnp : ¬ 0 < bp A m p u := fun h => hn (mem_filter.mpr ⟨hp,h⟩)
    exact le_antisymm (le_of_not_gt hnp) (Rounded.bp_nonneg (small A m) m p u)
  have hcard : 4 ≤ t.card := by
    have hs : (∑ p ∈ t, bp A m p u) ≤ (t.card : ℝ) := by
      calc
        _ ≤ ∑ _p ∈ t, (1 : ℝ) := sum_le_sum (fun p _ => Rounded.bp_le_one (small A m) m p u)
        _ = _ := by simp
    rw [hsum] at hmass
    have hc : (3 : ℝ) < t.card := hmass.trans_le hs
    have hc' : 3 < t.card := by exact_mod_cast hc
    omega
  have hp (p : ℕ) (hp : p ∈ t) : Nat.Prime p := by
    obtain ⟨a,ha,he⟩ := mem_image.mp (mem_filter.mp (mem_filter.mp hp).1).1
    exact he ▸ ((small A m).prime_of_mem a ha).1
  have hdiv (p : ℕ) (hp : p ∈ t) : p ∣ u := by
    by_contra hn
    have hz := Rounded.bp_zero_of_not_dvd (small A m) m p u hn
    have hh := (mem_filter.mp hp).2
    change 0 < Rounded.bp (small A m) m p u at hh
    rw [hz] at hh
    exact (lt_irrefl 0) hh
  have hprod := Erdos708H17.Proofs.prime_product_lower t hp 4 hcard ![2,3,5,7] (by decide)
  norm_num [Fin.prod_univ_succ] at hprod
  have hprodd : (∏ p ∈ t, p) ∣ u := by
    apply prod_dvd_of_isRelPrime
    · intro p hpt q hqt hpq
      exact Nat.coprime_iff_isRelPrime.mp ((hp p hpt).coprime_iff_not_dvd.mpr
        (fun h => hpq ((Nat.prime_dvd_prime_iff_eq (hp p hpt) (hp q hqt)).mp h)))
    · exact hdiv
  have hu : 0 < u := by
    have he : P*(k/P) = k := Nat.mul_div_cancel' (carrier_divides A m k)
    have hk0 := (mem_Icc.mp (mem_filter.mp hk).1).1
    change 0 < k/P
    by_contra hn
    have hz : (k/P : ℕ) = 0 := Nat.eq_zero_of_not_pos hn
    rw [hz,mul_zero] at he
    omega
  exact hprod.trans (Nat.le_of_dvd hu hprodd)

lemma carrier_nu_ge_210 (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) : 210 ≤ nu m P := by
  obtain ⟨k,hk,rfl⟩ := mem_image.mp hP
  exact (source_cofactor_ge_210 A m k hk).trans
    (Nat.div_le_div_right (mem_Icc.mp (mem_filter.mp hk).1).2)

lemma carrier_nu_pos (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) : 0 < nu m P := by
  have := carrier_nu_ge_210 A m P hP
  omega

lemma carrier_floor_ratio_strict (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) :
    (m : ℝ)/((P : ℝ)*(nu m P : ℝ)) < gamma := by
  have hp := carrier_pos A m P hP
  have hn := carrier_nu_ge_210 A m P hP
  have hpR : (0 : ℝ) < P := by exact_mod_cast hp
  have hnR : (210 : ℝ) ≤ nu m P := by exact_mod_cast hn
  have hfloor : m < P*(nu m P+1) := by
    have he := Nat.mod_add_div m P
    have hr := Nat.mod_lt m hp
    change m < P*(m/P+1)
    nlinarith
  have hfR : (m : ℝ) < (P : ℝ)*((nu m P : ℝ)+1) := by exact_mod_cast hfloor
  apply (div_lt_iff₀ (mul_pos hpR (by linarith))).mpr
  have hh : (nu m P : ℝ)+1 ≤ gamma*(nu m P : ℝ) := by norm_num [gamma]; linarith
  have hm := mul_le_mul_of_nonneg_left hh hpR.le
  nlinarith

lemma carrier_floor_ratio (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) :
    (m : ℝ)/P ≤ gamma*(nu m P : ℝ) := by
  have hpR : (0 : ℝ) < P := by exact_mod_cast carrier_pos A m P hP
  have hnR : (0 : ℝ) < nu m P := by exact_mod_cast carrier_nu_pos A m P hP
  have hh := (div_lt_iff₀ (mul_pos hpR hnR)).mp (carrier_floor_ratio_strict A m P hP)
  apply (div_le_iff₀ hpR).mpr
  nlinarith

#print axioms source_cofactor_ge_210
#print axioms carrier_floor_ratio_strict
end
end Erdos708H97.Proofs
