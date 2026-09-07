import Erdos708.H17.ChainParts.Arithmetic
import Erdos708.H17.ChainParts.Proofs.LargeAtoms

namespace Erdos708H17Chain.Proofs
open Finset BigOperators

lemma atom_modulus_pos (A : AtomSystem) (a : ℕ × ℕ) (ha : a ∈ A.atoms) : 0 < a.1 ^ a.2 :=
  pow_pos (A.prime_of_mem a ha).1.pos _

lemma atom_modulus_two (A : AtomSystem) (a : ℕ × ℕ) (ha : a ∈ A.atoms) : 2 ≤ a.1 ^ a.2 := by
  have h := A.prime_of_mem a ha
  have hp : a.1 ≤ a.1 ^ a.2 := by
    simpa using pow_le_pow_right₀ h.1.one_lt.le h.2
  exact h.1.two_le.trans hp

lemma mean_nonneg (A : AtomSystem) : 0 ≤ mean A := by
  apply sum_nonneg
  intro a ha
  exact div_nonneg (A.weight_nonneg a ha) (pow_nonneg (Nat.cast_nonneg _) _)

lemma s0_le_prime_card (A : AtomSystem) (k : ℕ) (hk : 0 < k) :
    S0 A k ≤ (k.primeFactors.card : ℝ) := by
  classical
  let T := A.atoms.filter (fun a => a.1 ^ a.2 ∣ k)
  have hmap : ∀ a ∈ T, a.1 ∈ k.primeFactors := by
    intro a ha
    have h := mem_filter.mp ha
    have hp := A.prime_of_mem a h.1
    exact hp.1.mem_primeFactors ((dvd_pow_self a.1 (by omega)).trans h.2) hk.ne'
  change (∑ a ∈ T, A.weight a) ≤ _
  rw [← sum_fiberwise_of_maps_to hmap]
  calc
    (∑ p ∈ k.primeFactors, ∑ a ∈ T.filter (fun a => a.1 = p), A.weight a) ≤
        ∑ _p ∈ k.primeFactors, (1 : ℝ) := by
      apply sum_le_sum
      intro p hp
      apply le_trans _ (A.perPrime_le_one p)
      apply sum_le_sum_of_subset_of_nonneg
      · intro a ha
        exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp ha).1).1, (mem_filter.mp ha).2⟩
      · intro a ha _
        exact A.weight_nonneg a (mem_filter.mp ha).1
    _ = k.primeFactors.card := by simp

lemma prime_card_small (k : ℕ) (hk : 0 < k) (hkm : k ≤ 4096) : k.primeFactors.card ≤ 12 := by
  have hpow : 2 ^ k.primeFactors.card ≤ k := by
    calc
      2 ^ k.primeFactors.card = ∏ _p ∈ k.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ k.primeFactors, p :=
        prod_le_prod (fun _ _ => Nat.zero_le _) (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ k := Nat.le_of_dvd hk (Nat.prod_primeFactors_dvd k)
  by_contra hbad
  have hh : 2 ^ 13 ≤ 2 ^ k.primeFactors.card := pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at hh
  omega

lemma atom_hinge_small (A : AtomSystem) (m : ℕ) (hm : m ≤ 4096) (x : ℕ) :
    hingeSum (S A) 65 0 m ≤ hingeSum (S A) 1 x m := by
  have hl : hingeSum (S A) 65 0 m = 0 := by
    apply sum_eq_zero
    intro k hk
    have hk' : k ∈ Icc 1 m := by simpa using hk
    have h1 := (mem_Icc.mp hk').1
    have h2 := (mem_Icc.mp hk').2
    have hS := s0_le_prime_card A k (by omega)
    have hcard : (k.primeFactors.card : ℝ) ≤ 12 := by exact_mod_cast prime_card_small k (by omega) (by omega)
    apply max_eq_right
    change S0 A k - 65 ≤ 0
    linarith
  rw [hl]
  exact sum_nonneg (fun _ _ => le_max_right _ _)

lemma s0_sum_counts (A : AtomSystem) (T : Finset ℕ) :
    (∑ k ∈ T, S0 A k) = ∑ a ∈ A.atoms, A.weight a * ((T.filter (a.1 ^ a.2 ∣ ·)).card : ℝ) := by
  classical
  simp only [S0, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  rw [← sum_filter]
  simp [mul_comm]

lemma initial_first_moment (A : AtomSystem) (m : ℕ) :
    (∑ k ∈ Icc 1 m, S0 A k) = ∑ a ∈ A.atoms, A.weight a * (m / a.1 ^ a.2 : ℕ) := by
  rw [s0_sum_counts]
  simp only [initial_multiples]

lemma floor_ratio_upper (m q : ℕ) (hq : 0 < q) : (m / q : ℕ) ≤ (m : ℝ) / q := by
  apply (le_div_iff₀ (by exact_mod_cast hq)).mpr
  exact_mod_cast Nat.div_mul_le_self m q

lemma first_moment_upper (A : AtomSystem) (m : ℕ) :
    (∑ k ∈ Icc 1 m, S0 A k) ≤ (m : ℝ) * mean A := by
  rw [initial_first_moment]
  unfold mean
  rw [mul_sum]
  apply sum_le_sum
  intro a ha
  have h := mul_le_mul_of_nonneg_left (floor_ratio_upper m _ (atom_modulus_pos A a ha)) (A.weight_nonneg a ha)
  push_cast at h
  convert h using 1 <;> ring

lemma affine_window (A : AtomSystem) (x m : ℕ) :
    (∑ k ∈ Icc 1 m, S0 A k) - m ≤ R A x m := by
  have hcount : (∑ k ∈ Icc 1 m, S0 A k) ≤ ∑ b ∈ Icc (x+1) (x+m), S0 A b := by
    rw [s0_sum_counts, s0_sum_counts]
    apply sum_le_sum
    intro a ha
    apply mul_le_mul_of_nonneg_left _ (A.weight_nonneg a ha)
    exact_mod_cast (initial_multiples m (a.1 ^ a.2)).trans_le (window_multiples_lower x m _)
  have hhinge : (∑ b ∈ Icc (x+1) (x+m), S0 A b) - m ≤ R A x m := by
    have hh := sum_le_sum (s := Icc (x+1) (x+m)) (fun b _ => le_max_left (S0 A b - 1) 0)
    simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc] at hh
    have hc : x + m + 1 - (x+1) = m := by omega
    simpa only [hc, R] using hh
  linarith

lemma floor_ratio_lower (m q : ℕ) (hq : 0 < q) (hsmall : 64 * q ≤ m) :
    (63 / 64 : ℝ) * ((m : ℝ) / q) ≤ (m / q : ℕ) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hratio : (64 : ℝ) ≤ (m : ℝ) / q := (le_div_iff₀ hqr).mpr (by exact_mod_cast hsmall)
  have hfloor : (m : ℝ) / q < (m / q : ℕ) + 1 := by
    apply (div_lt_iff₀ hqr).mpr
    have hmod := Nat.mod_lt m hq
    have heq := Nat.mod_add_div m q
    have hh : m < (m / q + 1) * q := by nlinarith
    exact_mod_cast hh
  linarith

lemma first_moment_lower (A : AtomSystem) (m : ℕ)
    (hsmall : ∀ a ∈ A.atoms, 64 * a.1 ^ a.2 ≤ m) :
    (63 / 64 : ℝ) * m * mean A ≤ ∑ k ∈ Icc 1 m, S0 A k := by
  rw [initial_first_moment]
  unfold mean
  rw [mul_sum]
  apply sum_le_sum
  intro a ha
  have h := mul_le_mul_of_nonneg_left
    (floor_ratio_lower m _ (atom_modulus_pos A a ha) (hsmall a ha)) (A.weight_nonneg a ha)
  push_cast at h
  convert h using 1 <;> ring

noncomputable def primePart (A : AtomSystem) (p : ℕ) : AtomSystem := restrict A (fun a => a.1 = p)
noncomputable def atomPrimes (A : AtomSystem) : Finset ℕ := A.atoms.image Prod.fst

lemma primePart_nonneg (A : AtomSystem) (p k : ℕ) : 0 ≤ S0 (primePart A p) k := s0_nonneg _ _
lemma primePart_le_one (A : AtomSystem) (p k : ℕ) : S0 (primePart A p) k ≤ 1 := by
  simp only [S0, primePart, restrict]
  apply le_trans _ (A.perPrime_le_one p)
  apply sum_le_sum_of_subset_of_nonneg
  · intro a ha
    simp only [mem_filter] at ha ⊢
    exact ha.1
  · intro a ha _
    exact A.weight_nonneg a (mem_filter.mp ha).1

lemma mean_primePart_le_half (A : AtomSystem) (p : ℕ) : mean (primePart A p) ≤ 1 / 2 := by
  have hsum := A.perPrime_le_one p
  have hbound : mean (primePart A p) ≤ (∑ a ∈ A.atoms.filter (fun a => a.1 = p), A.weight a) / 2 := by
    unfold mean primePart restrict
    dsimp
    rw [div_eq_mul_inv, sum_mul]
    simp only [sum_filter]
    apply sum_le_sum
    intro a hmem
    split_ifs with ha
    ·
      have htwo : (2 : ℝ) ≤ (a.1 : ℝ) ^ a.2 := by exact_mod_cast atom_modulus_two A a hmem
      simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_left (A.weight_nonneg a hmem) (by norm_num : (0 : ℝ) < 2) htwo
    · rfl
  linarith

lemma s0_prime_decomposition (A : AtomSystem) (k : ℕ) :
    (∑ p ∈ atomPrimes A, S0 (primePart A p) k) = S0 A k := by
  classical
  simp only [S0, primePart, restrict, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  have hmem : a.1 ∈ atomPrimes A := mem_image_of_mem Prod.fst ha
  rw [sum_eq_single a.1]
  · simp
  · intro p hp hne
    simp only [ite_eq_right hne.symm]
  · intro h
    exact False.elim (h hmem)

lemma mean_prime_decomposition (A : AtomSystem) :
    (∑ p ∈ atomPrimes A, mean (primePart A p)) = mean A := by
  classical
  simp only [mean, primePart, restrict, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  have hmem : a.1 ∈ atomPrimes A := mem_image_of_mem Prod.fst ha
  rw [sum_eq_single a.1]
  · simp
  · intro p hp hne
    simp only [ite_eq_right hne.symm]
  · intro h
    exact False.elim (h hmem)

lemma cross_moment_upper (A B : AtomSystem) (m : ℕ)
    (hcop : ∀ a ∈ A.atoms, ∀ b ∈ B.atoms, (a.1 ^ a.2).Coprime (b.1 ^ b.2)) :
    (∑ k ∈ Icc 1 m, S0 A k * S0 B k) ≤ (m : ℝ) * mean A * mean B := by
  classical
  have hind (a b : ℕ × ℕ) (ha : a ∈ A.atoms) (hb : b ∈ B.atoms) (k : ℕ) :
      (if a.1 ^ a.2 ∣ k then A.weight a else 0) * (if b.1 ^ b.2 ∣ k then B.weight b else 0) =
      if a.1 ^ a.2 * b.1 ^ b.2 ∣ k then A.weight a * B.weight b else 0 := by
    have hiff : a.1 ^ a.2 * b.1 ^ b.2 ∣ k ↔ a.1 ^ a.2 ∣ k ∧ b.1 ^ b.2 ∣ k :=
      ⟨fun h => ⟨(dvd_mul_right _ _).trans h, (dvd_mul_left _ _).trans h⟩,
        fun h => (hcop a ha b hb).mul_dvd_of_dvd_of_dvd h.1 h.2⟩
    simp only [hiff]
    split_ifs <;> simp_all
  have heq : (∑ k ∈ Icc 1 m, S0 A k * S0 B k) =
      ∑ a ∈ A.atoms, ∑ b ∈ B.atoms, A.weight a * B.weight b * (m / (a.1 ^ a.2 * b.1 ^ b.2) : ℕ) := by
    simp only [S0, sum_filter]
    simp only [sum_mul]
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    rw [sum_comm]
    apply sum_congr rfl
    intro b hb
    simp_rw [hind a b ha hb]
    rw [← sum_filter]
    simp [initial_multiples, mul_comm]
  rw [heq]
  unfold mean
  simp only [sum_mul, mul_sum]
  conv_rhs => rw [sum_comm]
  apply sum_le_sum
  intro a ha
  apply sum_le_sum
  intro b hb
  have h := mul_le_mul_of_nonneg_left (floor_ratio_upper m _
    (Nat.mul_pos (atom_modulus_pos A a ha) (atom_modulus_pos B b hb)))
      (mul_nonneg (A.weight_nonneg a ha) (B.weight_nonneg b hb))
  push_cast at h
  convert h using 1 <;> ring

#print axioms cross_moment_upper
#print axioms atom_hinge_small
#print axioms first_moment_upper
#print axioms affine_window
end Erdos708H17Chain.Proofs
