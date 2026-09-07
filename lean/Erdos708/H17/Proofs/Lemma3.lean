import Erdos708.H17.Proofs.Lemma1
import Erdos708.H17.Proofs.Lemma2
open Finset BigOperators
namespace Erdos708H17.Proofs
noncomputable section
lemma initial_multiples (m d : ℕ) : ((Icc 1 m).filter (d ∣ ·)).card = m / d := by
  have h : Icc 1 m = Ioc 0 m := by ext k; simp only [mem_Icc, mem_Ioc]; omega
  rw [h, Nat.Ioc_filter_dvd_card_eq_div]

lemma window_multiples (x m d : ℕ) :
    ((Icc (x+1) (x+m)).filter (d ∣ ·)).card = (x+m) / d - x / d := by
  classical
  have heq : (Icc (x+1) (x+m)).filter (d ∣ ·) =
      ((Ioc 0 (x+m)).filter (d ∣ ·)) \ ((Ioc 0 x).filter (d ∣ ·)) := by
    ext k
    simp only [mem_filter, mem_Icc, mem_sdiff, mem_Ioc]
    omega
  rw [heq, card_sdiff_of_subset]
  · rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div]
  · intro k hk
    simp only [mem_filter, mem_Ioc] at hk ⊢
    omega

lemma window_multiples_lower (x m d : ℕ) :
    m / d ≤ ((Icc (x+1) (x+m)).filter (d ∣ ·)).card := by
  rw [window_multiples]
  have := Nat.div_add_div_le_add_div (x := x) (y := m) (z := d)
  omega


lemma atom_modulus_pos (A : AtomSystem) (a : ℕ × ℕ) (ha : a ∈ A.atoms) : 0 < a.1 ^ a.2 :=
  pow_pos (A.prime_of_mem a ha).1.pos _

lemma S_sum_counts (A : AtomSystem) (T : Finset ℕ) :
    (∑ k ∈ T, S A k) = ∑ a ∈ A.atoms, A.weight a * ((T.filter (a.1 ^ a.2 ∣ ·)).card : ℝ) := by
  classical
  simp only [S, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  rw [← sum_filter]
  simp [mul_comm]

lemma initial_first_moment (A : AtomSystem) (m : ℕ) :
    (∑ k ∈ Icc 1 m, S A k) = ∑ a ∈ A.atoms, A.weight a * (m / a.1 ^ a.2 : ℕ) := by
  rw [S_sum_counts]
  simp only [initial_multiples]

lemma floor_ratio_upper (m q : ℕ) (hq : 0 < q) : (m / q : ℕ) ≤ (m : ℝ) / q := by
  apply (le_div_iff₀ (by exact_mod_cast hq)).mpr
  exact_mod_cast Nat.div_mul_le_self m q

lemma first_moment_upper (A : AtomSystem) (m : ℕ) :
    (∑ k ∈ Icc 1 m, S A k) ≤ (m : ℝ) * mean A := by
  rw [initial_first_moment]
  unfold mean
  rw [mul_sum]
  apply sum_le_sum
  intro a ha
  have h := mul_le_mul_of_nonneg_left (floor_ratio_upper m _ (atom_modulus_pos A a ha)) (A.weight_nonneg a ha)
  push_cast at h
  convert h using 1 <;> ring

lemma affine_window (A : AtomSystem) (x m : ℕ) :
    (∑ k ∈ Icc 1 m, S A k) - m ≤ R A x m := by
  have hcount : (∑ k ∈ Icc 1 m, S A k) ≤ ∑ b ∈ Icc (x+1) (x+m), S A b := by
    rw [S_sum_counts, S_sum_counts]
    apply sum_le_sum
    intro a ha
    apply mul_le_mul_of_nonneg_left _ (A.weight_nonneg a ha)
    exact_mod_cast (initial_multiples m (a.1 ^ a.2)).trans_le (window_multiples_lower x m _)
  have hhinge : (∑ b ∈ Icc (x+1) (x+m), S A b) - m ≤ R A x m := by
    have hh := sum_le_sum (s := Icc (x+1) (x+m)) (fun b _ => le_max_left (S A b - 1) 0)
    simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc] at hh
    have hc : x + m + 1 - (x+1) = m := by omega
    simpa only [hc, R, hingeSum] using hh
  linarith

lemma floor_ratio_lower (m q : ℕ) (hq : 0 < q) (hsmall : 65536 * q ≤ m) :
    (65535 / 65536 : ℝ) * ((m : ℝ) / q) ≤ (m / q : ℕ) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hratio : (65536 : ℝ) ≤ (m : ℝ) / q := (le_div_iff₀ hqr).mpr (by exact_mod_cast hsmall)
  have hfloor : (m : ℝ) / q < (m / q : ℕ) + 1 := by
    apply (div_lt_iff₀ hqr).mpr
    have hmod := Nat.mod_lt m hq
    have heq := Nat.mod_add_div m q
    have hh : m < (m / q + 1) * q := by nlinarith
    exact_mod_cast hh
  linarith

lemma first_moment_lower (A : AtomSystem) (m : ℕ)
    (hsmall : ∀ a ∈ A.atoms, 65536 * a.1 ^ a.2 ≤ m) :
    (65535 / 65536 : ℝ) * m * mean A ≤ ∑ k ∈ Icc 1 m, S A k := by
  rw [initial_first_moment]
  unfold mean
  rw [mul_sum]
  apply sum_le_sum
  intro a ha
  have h := mul_le_mul_of_nonneg_left
    (floor_ratio_lower m _ (atom_modulus_pos A a ha) (hsmall a ha)) (A.weight_nonneg a ha)
  push_cast at h
  convert h using 1 <;> ring


def scale (A : AtomSystem) (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) : AtomSystem where
  atoms := A.atoms
  weight a := c * A.weight a
  prime_of_mem := A.prime_of_mem
  weight_nonneg a ha := mul_nonneg hc (A.weight_nonneg a ha)
  perPrime_le_one p := by
    rw [← mul_sum]
    exact (mul_le_mul_of_nonneg_left (A.perPrime_le_one p) hc).trans (by simpa using hc1)

lemma scale_value (A : AtomSystem) (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    S (scale A c hc hc1) n = c * S A n := by simp only [S, scale, mul_sum]
lemma scale_mean (A : AtomSystem) (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    mean (scale A c hc hc1) = c * mean A := by
  simp only [mean, scale, mul_sum, mul_div_assoc]

lemma component_le_one (A : AtomSystem) (p n : ℕ) : component A p n ≤ 1 := by
  apply le_trans _ (A.perPrime_le_one p)
  apply sum_le_sum_of_subset_of_nonneg
  · intro a ha
    exact mem_filter.mpr ⟨(mem_filter.mp ha).1, (mem_filter.mp ha).2.1⟩
  · intro a ha _
    exact A.weight_nonneg a (mem_filter.mp ha).1

lemma atom_hinge_moment (A : AtomSystem) (N c : ℕ) :
    (∑ n ∈ Icc 1 N, max (S A n - c) 0) ≤
      (N : ℝ) * mean A ^ (c+1) / (Nat.factorial (c+1) : ℝ) := by
  apply le_trans _ (atom_moment A N (c+1))
  apply sum_le_sum
  intro n hn
  rw [← sum_components]
  exact hinge_le_esymm (Rounded.primes A) (fun p => component A p n)
    (fun p hp => ⟨component_nonneg A p n, component_le_one A p n⟩) c

lemma dense_truncation (A : AtomSystem) (m : ℕ) (hm : 1 ≤ m) (hH : Hstar ≤ H A m) :
    (m : ℝ) ≤ ∑ k ∈ Icc 1 m, min (S_0 A m k) 17 := by
  classical
  have hH0 : 0 < H A m := lt_of_lt_of_le (by norm_num [Hstar]) hH
  let c := Hstar / H A m
  have hc : 0 ≤ c := div_nonneg (by norm_num [Hstar]) hH0.le
  have hc1 : c ≤ 1 := (div_le_one hH0).mpr hH
  let V := scale (small A m) c hc hc1
  have hmean : mean V = Hstar := by
    rw [scale_mean]
    exact div_mul_cancel₀ _ hH0.ne'
  have hV (k : ℕ) : S V k ≤ S_0 A m k := by
    rw [scale_value]
    have hS : 0 ≤ S (small A m) k :=
      sum_nonneg (fun a ha => (small A m).weight_nonneg a (mem_filter.mp ha).1)
    exact (mul_le_mul_of_nonneg_right hc1 hS).trans_eq (one_mul _)
  have hfirst := first_moment_lower V m (by
    intro a ha
    simp only [V, scale, small, restrict, mem_filter] at ha
    exact ha.2)
  rw [hmean] at hfirst
  have heighth := atom_hinge_moment V m 7
  rw [hmean] at heighth
  have hid : (∑ k ∈ Icc 1 m, S V k) = (∑ k ∈ Icc 1 m, min (S V k) 7) +
      ∑ k ∈ Icc 1 m, max (S V k - 7) 0 := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    simp only [min_def, max_def]
    split_ifs <;> linarith
  have hnum : 1 < (65535/65536 : ℝ) * Hstar - Hstar^8 / (Nat.factorial 8 : ℝ) := by
    norm_num [Hstar]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have htrunc : (m : ℝ) ≤ ∑ k ∈ Icc 1 m, min (S V k) 7 := by
    nlinarith
  apply htrunc.trans
  apply sum_le_sum
  intro k hk
  exact min_le_min (hV k) (by norm_num)

lemma dense_branch (A : AtomSystem) (m : ℕ) (hm : 1 ≤ m) (hH : Hstar ≤ H A m) (x : ℕ) :
    L A m ≤ R A x m := by
  have hmass := dense_truncation A m hm hH
  have heq : L A m = (∑ k ∈ Icc 1 m, S_0 A m k) -
      ∑ k ∈ Icc 1 m, min (S_0 A m k) 17 := by
    simp only [L, hingeSum, zero_add, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k hk
    rw [deletion_hinge A m 17 (by norm_num) k hk]
    simp only [min_def, max_def]
    split_ifs <;> linarith
  have hwin := affine_window (small A m) x m
  have hR : R (small A m) x m ≤ R A x m := by
    unfold R hingeSum
    apply sum_le_sum
    intro k hk
    exact max_le_max (sub_le_sub_right (S_restrict_le A _ k) 1) le_rfl
  have hleft : L A m ≤ (∑ k ∈ Icc 1 m, S_0 A m k) - m := by rw [heq]; linarith
  exact hleft.trans (hwin.trans hR)

#print axioms dense_truncation
#print axioms dense_branch
end
end Erdos708H17.Proofs
