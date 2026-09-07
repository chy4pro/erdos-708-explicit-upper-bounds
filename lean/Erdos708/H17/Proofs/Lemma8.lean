import Erdos708.H17.Proofs.Pointwise
open Finset BigOperators
open scoped NNReal
namespace Erdos708H17.Proofs
noncomputable section
attribute [local instance] Classical.propDecidable

lemma negative_window_count (A : AtomSystem) (m : ℕ) (hm : 2^48 ≤ m)
    (P : ℕ) (hP : P ∈ carriers A m) (x : ℕ) :
    (∑ a ∈ (Rounded.retained (small A m) m).filter (fun a => ¬ a.1 ∣ P),
      delta A m (theta A m P) a * (windowCount x m (P * Rounded.modulus a) : ℝ)) ≤
      2 * ((m : ℝ) / P) * HB A m := by
  have hPpos : (0 : ℝ) < P := by exact_mod_cast carrier_pos A m P hP
  calc
    _ ≤ ∑ a ∈ (Rounded.retained (small A m) m).filter (fun a => ¬ a.1 ∣ P),
        delta A m (theta A m P) a * (2 * ((m : ℝ) / (P * Rounded.modulus a : ℕ))) := by
      apply sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_left _ (Rounded.capIncrement_bounds (small A m) m _ a (mem_filter.mp ha).1).1
      apply windowCount_upper_two
      · exact Nat.mul_pos (carrier_pos A m P hP) (Rounded.retained_modulus_pos (small A m) m (mem_filter.mp ha).1)
      · exact negative_modulus_le A m (by omega) P hP a (mem_filter.mp ha).1
    _ = 2 * ((m : ℝ) / P) *
        ∑ a ∈ (Rounded.retained (small A m) m).filter (fun a => ¬ a.1 ∣ P),
          delta A m (theta A m P) a / (Rounded.modulus a : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro a ha
      rw [Nat.cast_mul]
      field_simp
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (delta_mean_le A m P) (by positivity)

lemma window_factor : 24 * (1 - 2*gamma*Hstar/K) = (62248/30583 : ℝ) := by
  norm_num [gamma,Hstar,K]

lemma window_value (A : AtomSystem) (m : ℕ) (hm : 2^48 ≤ m) (hH : H A m < Hstar) (x : ℕ) :
    (62248/30583 : ℝ) * LB A m ≤ ∑ n ∈ Icc (x+1) (x+m), F A m n := by
  have hHB0 : 0 ≤ HB A m := sum_nonneg (fun a ha =>
    div_nonneg (Rounded.increment_nonneg (small A m) m ha) (Nat.cast_nonneg _))
  have hHB : HB A m ≤ Hstar := (Rounded.HB_le_mean (small A m) m).trans hH.le
  have hLB : 0 ≤ LB A m := by unfold LB hingeSum; exact sum_nonneg (fun k hk => le_max_right _ _)
  have hK : (0:ℝ) < K := by norm_num [K]
  have hG : 0 ≤ gamma := by norm_num [gamma]
  rw [F_window_eq]
  calc
    _ ≤ (24 - (48*gamma/K) * HB A m) * LB A m := by
      have hw := window_factor
      have hh := mul_le_mul_of_nonneg_left hHB (show 0 ≤ 48*gamma/K by positivity)
      have hbase : (62248/30583:ℝ) ≤ 24-(48*gamma/K)*HB A m := by
        have he : 24*(1-2*gamma*Hstar/K) = 24-(48*gamma/K)*Hstar := by ring
        rw [he] at hw
        linarith
      exact mul_le_mul_of_nonneg_right hbase hLB
    _ = ∑ P ∈ carriers A m, (24 - (48*gamma/K)*HB A m) * M A m P := by
      rw [← total_carried_mass,mul_sum]
    _ ≤ _ := by
      apply sum_le_sum
      intro P hP
      have hc := coefficient_nonneg A m P
      have hnu : (0:ℝ) < nu m P := by exact_mod_cast carrier_nu_pos A m (by omega) P hP
      have hcnu : coefficient A m P * (nu m P:ℝ) = M A m P := div_mul_cancel₀ _ hnu.ne'
      have hcount : (nu m P:ℝ) ≤ windowCount x m P := by exact_mod_cast windowCount_lower x m P
      have hpos : 24*M A m P ≤ 24*coefficient A m P*(windowCount x m P:ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hcount hc]
      have hneg : (24/K)*coefficient A m P*
          (∑ a ∈ (Rounded.retained (small A m) m).filter (fun a => ¬ a.1 ∣ P),
            delta A m (theta A m P) a * (windowCount x m (P*Rounded.modulus a):ℝ)) ≤
          (48*gamma/K)*HB A m*M A m P := by
        calc
          _ ≤ (24/K)*coefficient A m P*(2*((m:ℝ)/P)*HB A m) :=
            mul_le_mul_of_nonneg_left (negative_window_count A m hm P hP x) (by positivity)
          _ ≤ (24/K)*coefficient A m P*(2*(gamma*(nu m P:ℝ))*HB A m) := by
            gcongr
            exact carrier_floor_ratio A m hm P hP
          _ = _ := by rw [← hcnu]; ring
      nlinarith

#print axioms window_value
end
end Erdos708H17.Proofs
