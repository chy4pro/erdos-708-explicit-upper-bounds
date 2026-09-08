import Erdos708.H97.Proofs.CarrierCount
import Erdos708.H97.Proofs.Lemma5
open Finset BigOperators
open scoped NNReal
namespace Erdos708H97.Proofs
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
lemma theta_eq_height (A : AtomSystem) (m P : ℕ) :
    theta A m P = (Rounded.level (carrierHeight A m P) : ℝ) := rfl

lemma carrier_mass_scale (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) :
    mu A m P = 1+(carrierMassIndex A m P : ℝ)/Rounded.scaleL (carrierHeight A m P) := by
  have he := carrierDegree_eq A m P hP
  rw [(carrier_degree_bounds A m P hP).2.2,Nat.cast_add] at he
  have hL : (0 : ℝ) < Rounded.scaleL (carrierHeight A m P) := by exact_mod_cast Rounded.scaleL_pos _
  field_simp
  linarith

lemma U_scale_lower (A : AtomSystem) (m n h d P : ℕ) (hP : P ∈ scaleCarriers A m n h d) :
    max 0 (((activePrimes A m n h).card : ℝ) * (Rounded.level h : ℝ) - mu A m P) ≤ U A m P n := by
  have hp := mem_filter.mp hP
  have ht : theta A m P = (Rounded.level h : ℝ) := by rw [theta_eq_height,hp.2.2.1]
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
          exact_mod_cast Rounded.level_antitone hheight
        apply (min_le_right _ _).trans
        rw [← hbp]
        exact hlevel.trans_eq (Rounded.effective_value_eq_bp (small A m) m P b hb).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun p _ _ => NNReal.coe_nonneg _)
  have hT : ((activePrimes A m n h).card : ℝ) * (Rounded.level h : ℝ) ≤ ∑ p ∈ t, min (bp A m p n) θ := by
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
  apply max_le hU0
  linarith

lemma B_scale_lower (A : AtomSystem) (m n h d P : ℕ) (hP : P ∈ scaleCarriers A m n h d) :
    max (mu A m P-1) (((activePrimes A m n h).card : ℝ)*(Rounded.level h : ℝ)-1) ≤ max (B A m n-1) 0 := by
  have hp := mem_filter.mp hP
  have hmono : mu A m P ≤ B A m n := Rounded.B_dvd_mono (small A m) m hp.2.1
  have hN : ((activePrimes A m n h).card : ℝ)*(Rounded.level h : ℝ) ≤ B A m n := by
    calc
      _ = ∑ _p ∈ activePrimes A m n h, (Rounded.level h : ℝ) := by simp
      _ ≤ ∑ p ∈ activePrimes A m n h, bp A m p n := sum_le_sum (fun p hp => (mem_filter.mp hp).2)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => NNReal.coe_nonneg _)
  have hmax := le_max_left (B A m n-1) 0
  apply max_le <;> linarith

#print axioms U_scale_lower
#print axioms B_scale_lower
end
end Erdos708H97.Proofs
