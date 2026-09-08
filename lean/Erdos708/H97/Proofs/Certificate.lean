import Erdos708.H97.Proofs.CarrierBudget
import Erdos708.H97.Proofs.Cofactor
import Erdos708.H97.Proofs.Capped
open Finset BigOperators
open scoped NNReal
namespace Erdos708H97.Proofs
noncomputable section
attribute [local instance] Classical.propDecidable
def windowCount (x m d : ℕ) : ℕ :=
  #((Icc (x + 1) (x + m)).filter (fun n => d ∣ n))

lemma initialCount (N d : ℕ) : #((Icc 1 N).filter (fun n => d ∣ n)) = N / d := by
  have heq : (Icc 1 N).filter (fun n => d ∣ n) =
      (range N.succ).filter (fun n => n ≠ 0 ∧ d ∣ n) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_range]
    omega
  rw [heq, Nat.card_multiples']

lemma windowCount_add (x m d : ℕ) : x / d + windowCount x m d = (x + m) / d := by
  have hu : (Icc 1 (x + m)).filter (fun n => d ∣ n) =
      (Icc 1 x).filter (fun n => d ∣ n) ∪
      (Icc (x + 1) (x + m)).filter (fun n => d ∣ n) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_union]
    omega
  have hd : Disjoint ((Icc 1 x).filter (fun n => d ∣ n))
      ((Icc (x + 1) (x + m)).filter (fun n => d ∣ n)) := by
    apply disjoint_left.mpr
    intro n hn hn'
    have h1 := (mem_Icc.mp (mem_filter.mp hn).1).2
    have h2 := (mem_Icc.mp (mem_filter.mp hn').1).1
    omega
  have hh := congrArg Finset.card hu
  rw [card_union_of_disjoint hd, initialCount, initialCount] at hh
  exact hh.symm

lemma windowCount_lower (x m d : ℕ) : m / d ≤ windowCount x m d := by
  have hh : x / d + m / d ≤ (x + m) / d := Nat.div_add_div_le_add_div
  have hc := windowCount_add x m d
  omega

lemma windowCount_upper (x m d : ℕ) (hd : 0 < d) :
    (windowCount x m d : ℝ) ≤ (m : ℝ) / d + 1 := by
  have hc := windowCount_add x m d
  have hlo := Nat.div_mul_le_self (x + m) d
  rw [← hc, Nat.add_mul] at hlo
  have hx : x < x / d * d + d := by
    have hh := Nat.mod_add_div x d
    have hr := Nat.mod_lt x hd
    nlinarith
  have hloR : ((x / d : ℕ) : ℝ) * d + (windowCount x m d : ℝ) * d ≤ x + m := by
    exact_mod_cast hlo
  have hxR : (x : ℝ) < ((x / d : ℕ) : ℝ) * d + d := by exact_mod_cast hx
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hh : (windowCount x m d : ℝ) ≤ ((m : ℝ) + d) / d := by
    apply (le_div_iff₀ hdR).2
    linarith
  simpa only [add_div, div_self (ne_of_gt hdR)] using hh

lemma windowCount_upper_two (x m d : ℕ) (hd : 0 < d) (hdm : d ≤ m) :
    (windowCount x m d : ℝ) ≤ 2 * ((m : ℝ) / d) := by
  have hh := windowCount_upper x m d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hratio : (1 : ℝ) ≤ (m : ℝ) / d := (le_div_iff₀ hdR).2 (by simpa only [one_mul] using (show (d : ℝ) ≤ m by exact_mod_cast hdm))
  linarith


lemma negative_modulus_le (A : AtomSystem) (m : ℕ) 
    (P : ℕ) (hP : P ∈ carriers A m) (a : ℕ × ℕ) (ha : a ∈ Rounded.retained (small A m) m) :
    P * Rounded.modulus a ≤ m := by
  have hp := carrier_cube A m P hP
  have hq := Rounded.retained_cube_le (small A m) m a ha
  have hc : (P * Rounded.modulus a)^3 ≤ m^3 := by
    calc
      _ = P^3 * Rounded.modulus a^3 := mul_pow _ _ _
      _ ≤ m^2 * m := Nat.mul_le_mul hp hq
      _ = _ := by ring
  by_contra hh
  have hlt : m^3 < (P * Rounded.modulus a)^3 := pow_lt_pow_left₀ (by omega) (by omega) (by omega)
  omega

lemma U_eq_delta_sum (A : AtomSystem) (m P n : ℕ) :
    U A m P n = ∑ a ∈ (Rounded.retained (small A m) m).filter (fun a => ¬ a.1 ∣ P ∧ Rounded.modulus a ∣ n),
      delta A m (theta A m P) a := by
  classical
  calc
    _ = ∑ p ∈ (Rounded.primes (small A m)).filter (fun p => ¬ p ∣ P),
        ∑ a ∈ (Rounded.retained (small A m) m).filter (fun a => a.1 = p ∧ Rounded.modulus a ∣ n),
          delta A m (theta A m P) a := by
      apply sum_congr rfl
      intro p hp
      exact (Rounded.capIncrement_telescope (small A m) m p n _ (theta_pos A m P).le).symm
    _ = _ := by
      have hmap : ∀ a ∈ (Rounded.retained (small A m) m).filter (fun a => ¬ a.1 ∣ P ∧ Rounded.modulus a ∣ n),
          a.1 ∈ (Rounded.primes (small A m)).filter (fun p => ¬ p ∣ P) := by
        intro a ha
        exact mem_filter.mpr ⟨mem_image_of_mem Prod.fst
          (Rounded.rounding_retained_mem_atoms (small A m) m (mem_filter.mp ha).1), (mem_filter.mp ha).2.1⟩
      rw [← sum_fiberwise_of_maps_to hmap (delta A m (theta A m P))]
      apply sum_congr rfl
      intro p hp
      apply sum_congr
      · ext a
        simp only [mem_filter]
        constructor
        · rintro ⟨ha, hap, had⟩
          exact ⟨⟨ha, hap ▸ (mem_filter.mp hp).2, had⟩, hap⟩
        · rintro ⟨⟨ha, hpa, had⟩, hap⟩
          exact ⟨ha, hap, had⟩
      · intro a ha
        rfl

lemma outside_coprime (A : AtomSystem) (m P : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ Rounded.retained (small A m) m) (hpa : ¬ a.1 ∣ P) : Nat.Coprime P (Rounded.modulus a) :=
  ((Rounded.carrier_retained_prime (small A m) m ha).1.coprime_iff_not_dvd.mpr hpa).symm.pow_right _

lemma indicator_U (A : AtomSystem) (m P n : ℕ) :
    (if P ∣ n then U A m P n else 0) =
      ∑ a ∈ (Rounded.retained (small A m) m).filter (fun a => ¬ a.1 ∣ P),
        if P * Rounded.modulus a ∣ n then delta A m (theta A m P) a else 0 := by
  classical
  by_cases hPn : P ∣ n
  · rw [if_pos hPn, U_eq_delta_sum]
    rw [sum_filter, sum_filter]
    apply sum_congr rfl
    intro a ha
    by_cases hp : a.1 ∣ P
    · simp [hp]
    · have he : P * Rounded.modulus a ∣ n ↔ Rounded.modulus a ∣ n :=
        ⟨fun hh => (dvd_mul_left (Rounded.modulus a) P).trans hh,
          fun hh => (outside_coprime A m P ha hp).mul_dvd_of_dvd_of_dvd hPn hh⟩
      simp [hp, he]
  · rw [if_neg hPn]
    symm
    apply sum_eq_zero
    intro a ha
    exact if_neg (fun hh => hPn ((dvd_mul_right P (Rounded.modulus a)).trans hh))

lemma F_expanded (A : AtomSystem) (m n : ℕ) :
    F A m n =
      (∑ P ∈ carriers A m, if P ∣ n then lambda * coefficient A m P else 0) -
      (lambda / K) * ∑ P ∈ carriers A m, coefficient A m P *
        ∑ a ∈ (Rounded.retained (small A m) m).filter (fun a => ¬ a.1 ∣ P),
          if P * Rounded.modulus a ∣ n then delta A m (theta A m P) a else 0 := by
  classical
  rw [F, mul_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro P hP
  rw [← indicator_U]
  by_cases hPn : P ∣ n <;> simp [hPn] <;> ring

lemma delta_mean_le (A : AtomSystem) (m P : ℕ) :
    (∑ a ∈ (Rounded.retained (small A m) m).filter (fun a => ¬ a.1 ∣ P),
      delta A m (theta A m P) a / (Rounded.modulus a : ℝ)) ≤ HB A m := by
  calc
    _ ≤ ∑ a ∈ (Rounded.retained (small A m) m).filter (fun a => ¬ a.1 ∣ P),
        Rounded.increment (small A m) m a / (Rounded.modulus a : ℝ) := by
      apply sum_le_sum
      intro a ha
      exact div_le_div_of_nonneg_right (Rounded.capIncrement_bounds (small A m) m _ a (mem_filter.mp ha).1).2 (Nat.cast_nonneg _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun a ha hn =>
      div_nonneg (Rounded.increment_nonneg (small A m) m ha) (Nat.cast_nonneg _))

lemma indicator_window_sum (x m d : ℕ) (w : ℝ) :
    (∑ n ∈ Icc (x + 1) (x + m), if d ∣ n then w else 0) = w * (windowCount x m d : ℝ) := by
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  exact mul_comm _ _

lemma F_window_eq (A : AtomSystem) (m x : ℕ) :
    (∑ n ∈ Icc (x + 1) (x + m), F A m n) =
      ∑ P ∈ carriers A m, (lambda * coefficient A m P * (windowCount x m P : ℝ) -
        (lambda / K) * coefficient A m P *
          ∑ a ∈ (Rounded.retained (small A m) m).filter (fun a => ¬ a.1 ∣ P),
            delta A m (theta A m P) a * (windowCount x m (P * Rounded.modulus a) : ℝ)) := by
  classical
  have hf (n : ℕ) : F A m n = ∑ P ∈ carriers A m,
      ((if P ∣ n then lambda * coefficient A m P else 0) -
        ((lambda / K) * coefficient A m P) *
          ∑ a ∈ (Rounded.retained (small A m) m).filter (fun a => ¬ a.1 ∣ P),
            if P * Rounded.modulus a ∣ n then delta A m (theta A m P) a else 0) := by
    rw [sum_sub_distrib]
    simp_rw [mul_assoc]
    rw [← mul_sum]
    exact F_expanded A m n
  simp_rw [hf]
  rw [sum_comm]
  apply sum_congr rfl
  intro P hP
  rw [sum_sub_distrib, indicator_window_sum, ← mul_sum, sum_comm]
  congr 2
  apply sum_congr rfl
  intro a ha
  exact indicator_window_sum x m _ _

lemma delta_sum (s : Finset ℕ) (d : ℕ) (w : ℝ) (f : ℕ → ℝ) (hd : d ∈ s) :
    (∑ D ∈ s, (if d = D then w else 0) * f D) = w * f d := by
  classical
  simp [ite_mul, hd]

lemma F_signed_expansion (A : AtomSystem) (m n : ℕ) :
    F A m n = ∑ D ∈ certificateSupport A m,
      signedCoefficient A m D * (if D ∣ n then 1 else 0) := by
  classical
  have hPmem (P : ℕ) (hP : P ∈ carriers A m) : P ∈ certificateSupport A m := mem_union_left _ hP
  have hqmem (P : ℕ) (hP : P ∈ carriers A m) (a : ℕ × ℕ)
      (ha : a ∈ (Rounded.retained (small A m) m).filter (fun a => ¬ a.1 ∣ P)) : P * Rounded.modulus a ∈ certificateSupport A m :=
    mem_union_right _ (mem_biUnion.mpr ⟨P, hP, mem_image_of_mem _ ha⟩)
  rw [F_expanded]
  symm
  unfold signedCoefficient
  simp_rw [sub_mul, mul_assoc]
  rw [sum_sub_distrib, ← mul_sum]
  congr 1
  · simp_rw [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro P hP
    rw [delta_sum _ P _ _ (hPmem P hP)]
    split_ifs <;> ring
  · congr 1
    simp_rw [sum_mul, mul_assoc]
    rw [sum_comm]
    apply sum_congr rfl
    intro P hP
    rw [← mul_sum]
    congr 1
    simp_rw [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    rw [delta_sum _ _ _ _ (hqmem P hP a ha)]
    split_ifs <;> ring


lemma negative_support_le (A : AtomSystem) (m : ℕ) 
    (D : ℕ) (hD : signedCoefficient A m D < 0) : D ≤ m := by
  classical
  by_contra hlarge
  have hz (P : ℕ) (hP : P ∈ carriers A m) :
      (∑ a ∈ (Rounded.retained (small A m) m).filter (fun a => ¬ a.1 ∣ P),
        if P * Rounded.modulus a = D then delta A m (theta A m P) a else 0) = 0 := by
    apply sum_eq_zero
    intro a ha
    apply if_neg
    intro he
    have hh := negative_modulus_le A m P hP a (mem_filter.mp ha).1
    omega
  have hpos : 0 ≤ ∑ P ∈ carriers A m, if P = D then lambda * coefficient A m P else 0 := by
    apply sum_nonneg
    intro P hP
    split_ifs
    · exact mul_nonneg (by norm_num [lambda]) (coefficient_nonneg A m P)
    · exact le_rfl
  unfold signedCoefficient at hD
  have hzero : (∑ P ∈ carriers A m, coefficient A m P *
      ∑ a ∈ (Rounded.retained (small A m) m).filter (fun a => ¬ a.1 ∣ P),
        if P * Rounded.modulus a = D then delta A m (theta A m P) a else 0) = 0 := by
    apply sum_eq_zero
    intro P hP
    rw [hz P hP, mul_zero]
  rw [hzero,mul_zero,sub_zero] at hD
  linarith

#print axioms F_signed_expansion
#print axioms negative_support_le
#print axioms carrier_floor_ratio
end
end Erdos708H97.Proofs
