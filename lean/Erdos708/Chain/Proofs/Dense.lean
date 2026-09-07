import Erdos708.Chain.Weights

namespace Erdos708Chain.Proofs
open Finset BigOperators

lemma sum_crossing {ι : Type*} (s : Finset ι) (f : ι → ℝ) (t K : ℝ)
    (ht : 0 < t) (hf : ∀ i ∈ s, f i ≤ K) (hs : t ≤ ∑ i ∈ s, f i) :
    ∃ Q ⊆ s, t ≤ ∑ i ∈ Q, f i ∧ (∑ i ∈ Q, f i) ≤ t + K := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty] at hs; linarith
  | @insert a s ha ih =>
    by_cases htail : t ≤ ∑ i ∈ s, f i
    · obtain ⟨Q,hQ,hlo,hhi⟩ := ih (fun i hi => hf i (mem_insert_of_mem hi)) htail
      exact ⟨Q,hQ.trans (subset_insert a s),hlo,hhi⟩
    · refine ⟨insert a s, subset_rfl, hs, ?_⟩
      rw [sum_insert ha]
      have := hf a (mem_insert_self a s)
      linarith

lemma prime_second_moment (A : AtomSystem) (Q : Finset ℕ) (m : ℕ) :
    (∑ k ∈ Icc 1 m, (∑ p ∈ Q, S0 (primePart A p) k) ^ 2) ≤
      (m : ℝ) * ((∑ p ∈ Q, mean (primePart A p)) + (∑ p ∈ Q, mean (primePart A p)) ^ 2) := by
  classical
  let h : ℕ → ℝ := fun p => mean (primePart A p)
  have hpair (p q : ℕ) :
      (∑ k ∈ Icc 1 m, S0 (primePart A p) k * S0 (primePart A q) k) ≤
        (m : ℝ) * ((if p = q then h p else 0) + h p * h q) := by
    by_cases hpq : p = q
    · subst q
      simp only [ite_true]
      have hh : (∑ k ∈ Icc 1 m, S0 (primePart A p) k * S0 (primePart A p) k) ≤
          ∑ k ∈ Icc 1 m, S0 (primePart A p) k := by
        apply sum_le_sum
        intro k hk
        have := primePart_nonneg A p k
        have := primePart_le_one A p k
        nlinarith
      have hu := first_moment_upper (primePart A p) m
      have hnon : 0 ≤ (m : ℝ) * h p * h p := mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (mean_nonneg _)) (mean_nonneg _)
      change _ ≤ (m : ℝ) * h p at hu
      nlinarith
    · simp only [ite_eq_right hpq, zero_add]
      rw [← mul_assoc]
      apply cross_moment_upper
      intro a ha b hb
      have ha' : a ∈ A.atoms ∧ a.1 = p := by simpa only [primePart, restrict, mem_filter] using ha
      have hb' : b ∈ A.atoms ∧ b.1 = q := by simpa only [primePart, restrict, mem_filter] using hb
      exact Nat.coprime_pow_primes _ _ (A.prime_of_mem a ha'.1).1 (A.prime_of_mem b hb'.1).1
        (by intro heq; exact hpq (ha'.2.symm.trans (heq.trans hb'.2)))
  have heq : (∑ k ∈ Icc 1 m, (∑ p ∈ Q, S0 (primePart A p) k) ^ 2) =
      ∑ p ∈ Q, ∑ q ∈ Q, ∑ k ∈ Icc 1 m, S0 (primePart A p) k * S0 (primePart A q) k := by
    simp only [pow_two, sum_mul]
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro p hp
    rw [sum_comm]
  rw [heq]
  have hh := sum_le_sum (s := Q) (fun p hp => sum_le_sum (s := Q) (fun q hq => hpair p q))
  apply hh.trans_eq
  have hdiag : (∑ p ∈ Q, ∑ q ∈ Q, if p = q then h p else 0) = ∑ p ∈ Q, h p := by
    apply sum_congr rfl
    intro p hp
    simp [hp]
  have hsquare : (∑ p ∈ Q, ∑ q ∈ Q, h p * h q) = (∑ p ∈ Q, h p) ^ 2 := by
    rw [pow_two, sum_mul]
    simp only [mul_sum]
  change _ = (m : ℝ) * ((∑ p ∈ Q, h p) + (∑ p ∈ Q, h p)^2)
  simp only [← mul_sum, sum_add_distrib]
  rw [hdiag, ← sum_mul]
  ring

lemma dense_atoms (A : AtomSystem) (m : ℕ) (hm : 1 ≤ m) (hH : 17 / 16 ≤ H64 A m) (x : ℕ) :
    hingeSum (S A) 65 0 m ≤ hingeSum (S A) 1 x m := by
  classical
  by_cases hsmallm : m ≤ 4096
  · exact atom_hinge_small A m hsmallm x
  have hm4096 : 4096 ≤ m := by omega
  let A₀ := small A m
  let h : ℕ → ℝ := fun p => mean (primePart A₀ p)
  have hmean : (∑ p ∈ atomPrimes A₀, h p) = H64 A m := mean_prime_decomposition A₀
  obtain ⟨Q,hQ,hlo,hhi⟩ := sum_crossing (atomPrimes A₀) h (17/16) (1/2)
    (by norm_num) (fun p _ => mean_primePart_le_half A₀ p) (by rw [hmean]; exact hH)
  let H := ∑ p ∈ Q, h p
  let T : ℕ → ℝ := fun k => ∑ p ∈ Q, S0 (primePart A₀ p) k
  have hTnon : ∀ k, 0 ≤ T k := fun k => sum_nonneg (fun p _ => s0_nonneg _ _)
  have hTle : ∀ k, T k ≤ S0 A₀ k := by
    intro k
    rw [← s0_prime_decomposition A₀ k]
    exact sum_le_sum_of_subset_of_nonneg hQ (fun p hp _ => s0_nonneg _ _)
  have hfirst : (1071 / 1024 : ℝ) * m ≤ ∑ k ∈ Icc 1 m, T k := by
    have hh : (63 / 64 : ℝ) * m * H ≤ ∑ k ∈ Icc 1 m, T k := by
      change _ ≤ ∑ k ∈ Icc 1 m, ∑ p ∈ Q, S0 (primePart A₀ p) k
      rw [sum_comm]
      dsimp [H]
      rw [mul_sum]
      apply sum_le_sum
      intro p hp
      apply first_moment_lower
      intro a ha
      have ha' : (a ∈ A.atoms ∧ 64 * a.1 ^ a.2 ≤ m) ∧ a.1 = p := by
        simpa only [primePart, A₀, small, restrict, mem_filter] using ha
      exact ha'.1.2
    change 17/16 ≤ H at hlo
    nlinarith [mul_le_mul_of_nonneg_right hlo (Nat.cast_nonneg m)]
  have hsecond : (∑ k ∈ Icc 1 m, T k ^ 2) ≤ (1025 / 256 : ℝ) * m := by
    have hh := prime_second_moment A₀ Q m
    change (∑ k ∈ Icc 1 m, T k ^ 2) ≤ (m : ℝ) * (H + H^2) at hh
    have hH0 : 0 ≤ H := sum_nonneg (fun p _ => mean_nonneg _)
    change H ≤ 17/16 + 1/2 at hhi
    have hn : H + H^2 ≤ 1025/256 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg m)]
  have htrunc : (m : ℝ) ≤ ∑ k ∈ Icc 1 m, min (S0 A₀ k) 64 := by
    have hpoint : ∀ k ∈ Icc 1 m, T k - T k ^ 2 / 256 ≤ min (S0 A₀ k) 64 := by
      intro k hk
      apply le_min
      · have h := hTle k
        nlinarith [sq_nonneg (T k)]
      · nlinarith [sq_nonneg (T k - 128)]
    have hh := sum_le_sum hpoint
    simp only [sum_sub_distrib, div_eq_mul_inv, ← sum_mul] at hh
    nlinarith [show (0 : ℝ) ≤ m by positivity]
  have hleft : hingeSum (S A) 65 0 m ≤ L A₀ m := by
    simp only [hingeSum, L, zero_add]
    apply sum_le_sum
    intro k hk
    exact (large_atoms A m hm4096).2.1 k (by simpa using hk)
  have hid : L A₀ m = (∑ k ∈ Icc 1 m, S0 A₀ k) - ∑ k ∈ Icc 1 m, min (S0 A₀ k) 64 := by
    unfold L
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro k hk
    by_cases h : S0 A₀ k ≤ 64
    · rw [min_eq_left h, max_eq_right (by linarith), sub_self]
    · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
  have hright : R A₀ x m ≤ hingeSum (S A) 1 x m := by
    unfold R hingeSum
    apply sum_le_sum
    intro b hb
    exact (large_atoms A m hm4096).2.2 b
  have haff := affine_window A₀ x m
  rw [hid] at hleft
  linarith

/-- Exact restatement of the dense-branch card. -/
theorem dense :
    (∀ (A : AtomSystem) (m : ℕ), 1 ≤ m → 17 / 16 ≤ H64 A m → ∀ x : ℕ,
      hingeSum (S A) 65 0 m ≤ hingeSum (S A) 1 x m) ∧
    (∀ (z : Weight) (m : ℕ), 1 ≤ m → 17 / 16 ≤ weightH64 z m → ∀ x : ℕ,
      hingeSum (w z) 65 0 m ≤ hingeSum (w z) 1 x m) := by
  refine ⟨dense_atoms, ?_⟩
  intro z m hm hH x
  apply capped_to_weight
  apply atoms_to_capped
  exact dense_atoms (ofWeight z m) m hm (by simpa only [ofWeight_mean] using hH) x

#print axioms prime_second_moment
#print axioms dense_atoms
#print axioms dense
end Erdos708Chain.Proofs
