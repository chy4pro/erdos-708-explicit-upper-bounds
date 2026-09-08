import Erdos708.H97.Defs
import Erdos708.H17.Proofs.Lemma3
open Finset BigOperators
namespace Erdos708H97
namespace Proofs
noncomputable section
open Erdos708H17.Proofs

lemma deletion_hinge (A : AtomSystem) (m : ℕ) (c : ℝ) (hc : 7 ≤ c)
    (k : ℕ) (hk : k ∈ Icc 1 m) : max (S A k-c) 0 = max (S_0 A m k-c) 0 :=
  Erdos708H17.Proofs.deletion_hinge A m c hc k hk
lemma S_small_le (A : AtomSystem) (m n : ℕ) : S_0 A m n ≤ S A n :=
  Erdos708H17.Proofs.S_restrict_le A _ n
lemma tiny_hinge_zero (A : AtomSystem) (m : ℕ) (hm : m ≤ 1) : L A m = 0 := by
  unfold L Erdos708H17.hingeSum
  apply sum_eq_zero
  intro k hk
  have hk1 : k = 1 := by simp only [zero_add, mem_Icc] at hk; omega
  subst k
  have hs := S_le_prime_card A 1 (by omega)
  norm_num at hs
  exact max_eq_right (by linarith)
lemma dense_truncation (A : AtomSystem) (m : ℕ) (hm : 1 ≤ m) (hH : Hstar ≤ H A m) :
    (m : ℝ) ≤ ∑ k ∈ Icc 1 m, min (S_0 A m k) (97/10) := by
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
      ∑ k ∈ Icc 1 m, min (S_0 A m k) (97/10) := by
    simp only [L, hingeSum, zero_add, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k hk
    rw [deletion_hinge A m (97/10) (by norm_num) k hk]
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


end
end Proofs
 theorem lemma2 (A : AtomSystem) (m : ℕ) :
    (∀ c : ℝ, 7 ≤ c → ∀ k ∈ Icc 1 m,
      max (S A k-c) 0 = max (S_0 A m k-c) 0) ∧
    (∀ n, S_0 A m n ≤ S A n) ∧
    (m ≤ 1 → L A m = 0) ∧
    (1 ≤ m → Hstar ≤ H A m →
      (m : ℝ) ≤ ∑ k ∈ Icc 1 m, min (S_0 A m k) (97/10)) ∧
    (1 ≤ m → Hstar ≤ H A m → ∀ x, L A m ≤ R A x m) := by
  exact ⟨fun c hc k hk => Proofs.deletion_hinge A m c hc k hk,
    Proofs.S_small_le A m, Proofs.tiny_hinge_zero A m,
    Proofs.dense_truncation A m, Proofs.dense_branch A m⟩
#print axioms lemma2
end Erdos708H97
