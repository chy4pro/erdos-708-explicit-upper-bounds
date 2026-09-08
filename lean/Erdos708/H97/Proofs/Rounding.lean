import Erdos708.H97.Proofs.Retention
open Finset BigOperators
open scoped NNReal
namespace Erdos708H97.Rounded
noncomputable section
set_option maxHeartbeats 2000000

/-- G2: the first crossing modulus divides the source point; log m is positive. -/
lemma local_rounding_cost (A : AtomSystem) (m p k : ℕ) (hm : 2 ≤ m) :
    ∃ (e : ℕ) (b : Bool), p^e ∣ k ∧
      ap A p k * Real.log m ≤ (5/4)*bp A m p k*Real.log m +
        (45/16)*Real.log (p^e : ℕ) + (if b then Real.log m/16 else 0) ∧
      (b = true → Real.log m < 3*Real.log (p^e : ℕ)) := by
  have hmlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hb0 := bp_nonneg A m p k
  by_cases hf : 0 < ap A p k
  · obtain ⟨a, ha, hap, hak, hnear⟩ := rounded_current_level A p k hf
    have hqa : (0 : ℝ) < modulus a := by
      exact_mod_cast pow_pos (A.prime_of_mem a (mem_filter.mp ha).1).1.pos a.2
    by_cases hr : (modulus a : ℝ) ≤ (m : ℝ)^eta (levelValue A a)
    · have ham : a ∈ retained A m := mem_filter.mpr ⟨ha,hr⟩
      have hbp : (levelValue A a : ℝ) ≤ bp A m p k := by
        exact_mod_cast (Finset.le_sup (f := levelValue A) (mem_filter.mpr ⟨ham,hap,hak⟩) :
          levelValue A a ≤ bpNN A m p k)
      refine ⟨0, false, by simp, ?_, by simp⟩
      simp only [pow_zero, Nat.cast_one, Real.log_one, mul_zero, Bool.false_eq_true, ↓reduceIte, add_zero]
      nlinarith [mul_le_mul_of_nonneg_right hnear hmlog.le,
        mul_le_mul_of_nonneg_right hbp hmlog.le]
    · have hlog : eta (levelValue A a)*Real.log m < Real.log (modulus a : ℝ) := by
        have hh := Real.log_lt_log (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < m by omega)) _)
          (lt_of_not_ge hr)
        rwa [Real.log_rpow (by exact_mod_cast (show 0 < m by omega))] at hh
      by_cases hh : (1/2 : ℝ) < levelValue A a
      · refine ⟨a.2, true, by simpa only [modulus,hap] using hak, ?_, ?_⟩
        · simp only [eta, if_pos hh] at hlog
          have hf1 : ap A p k ≤ 1 := Erdos708H17.Proofs.component_le_one A p k
          have hfl := mul_le_mul_of_nonneg_right hf1 hmlog.le
          have hb := mul_nonneg hb0 hmlog.le
          simp only [Bool.true_eq, ↓reduceIte]
          have he : Real.log (p^a.2 : ℕ) = Real.log (modulus a : ℝ) := by simp only [modulus,hap]
          rw [he]
          nlinarith
        · simp only [eta, if_pos hh] at hlog
          intro _
          simpa only [modulus,hap] using (show Real.log (m : ℝ) < 3*Real.log (modulus a : ℝ) by linarith)
      · refine ⟨a.2, false, by simpa only [modulus,hap] using hak, ?_, by simp⟩
        simp only [eta, if_neg hh] at hlog
        have hnearlog := mul_le_mul_of_nonneg_right hnear hmlog.le
        have hb := mul_nonneg hb0 hmlog.le
        simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
        have he : Real.log (p^a.2 : ℕ) = Real.log (modulus a : ℝ) := by simp only [modulus,hap]
        rw [he]
        nlinarith
  · refine ⟨0, false, by simp, ?_, by simp⟩
    have hf0 : ap A p k ≤ 0 := le_of_not_gt hf
    have hl := mul_nonpos_of_nonpos_of_nonneg hf0 hmlog.le
    simp only [pow_zero, Nat.cast_one, Real.log_one, mul_zero, Bool.false_eq_true, ↓reduceIte, add_zero]
    exact hl.trans (by positivity)

lemma S_le_rounded (A : AtomSystem) (m k : ℕ) (hm : 2 ≤ m)
    (hk : 0 < k) (hkm : k ≤ m) : S A k ≤ (5/4)*B A m k+47/16 := by
  classical
  choose e b he using (fun p => local_rounding_cost A m p k hm)
  have hprime (p : ℕ) (hp : p ∈ primes A) : Nat.Prime p := by
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hp
    exact (A.prime_of_mem a ha).1
  have hprod : (∏ p ∈ primes A, p^e p) ∣ k := by
    apply prod_dvd_of_isRelPrime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp
        (Nat.coprime_pow_primes (e p) (e q) (hprime p hp) (hprime q hq) hpq)
    · intro p hp
      exact (he p).1
  have hprodpos := Nat.pos_of_dvd_of_pos hprod hk
  have hprodle := Nat.le_of_dvd hk hprod
  have hlogs : (∑ p ∈ primes A, Real.log (p^e p : ℕ)) ≤ Real.log (m : ℝ) := by
    calc
      _ = Real.log (∏ p ∈ primes A, ((p^e p : ℕ) : ℝ)) := by
        symm
        exact Real.log_prod (fun p hp => by exact_mod_cast (pow_pos (hprime p hp).pos (e p)).ne')
      _ = Real.log ((∏ p ∈ primes A, p^e p : ℕ) : ℝ) := by rw [Nat.cast_prod]
      _ ≤ Real.log (k : ℝ) := Real.log_le_log (by exact_mod_cast hprodpos) (by exact_mod_cast hprodle)
      _ ≤ Real.log (m : ℝ) := Real.log_le_log (by exact_mod_cast hk) (by exact_mod_cast hkm)
  have hmlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  let high := (primes A).filter (fun p => b p = true)
  have hcard : high.card ≤ 2 := by
    by_contra hn
    have hne : high.Nonempty := card_pos.mp (by omega)
    have hh : (high.card : ℝ)*Real.log m < 3*∑ p ∈ high, Real.log (p^e p : ℕ) := by
      have hs := sum_lt_sum (s := high)
        (fun p hp => ((he p).2.2 (mem_filter.mp hp).2).le)
        (by obtain ⟨p,hp⟩ := hne; exact ⟨p,hp,(he p).2.2 (mem_filter.mp hp).2⟩)
      simpa only [sum_const, nsmul_eq_mul, ← mul_sum] using hs
    have hsub : (∑ p ∈ high, Real.log (p^e p : ℕ)) ≤ ∑ p ∈ primes A, Real.log (p^e p : ℕ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Real.log_natCast_nonneg _)
    have hc : (3 : ℝ) ≤ high.card := by exact_mod_cast (show 3 ≤ high.card by omega)
    nlinarith [mul_le_mul_of_nonneg_right hc hmlog.le]
  have hsum := sum_le_sum (s := primes A) (fun p hp => (he p).2.1)
  have hif : (∑ p ∈ primes A, if b p then Real.log (m : ℝ)/16 else 0) =
      (high.card : ℝ)*Real.log m/16 := by
    rw [← sum_filter]
    simp [high, mul_div_assoc]
  simp only [sum_add_distrib, ← sum_mul, ← mul_sum, sum_ap_eq_S, hif] at hsum
  have hc : (high.card : ℝ) ≤ 2 := by exact_mod_cast hcard
  have hbound : S A k*Real.log m ≤ ((5/4)*B A m k+47/16)*Real.log m := by
    change S A k*Real.log m ≤ _ at hsum
    change S A k*Real.log m ≤ (5/4)*B A m k*Real.log m +
      (45/16)*(∑ p ∈ primes A, Real.log (p^e p : ℕ)) + (high.card : ℝ)*Real.log m/16 at hsum
    nlinarith [mul_le_mul_of_nonneg_right hc hmlog.le]
  exact (mul_le_mul_iff_left₀ hmlog).mp hbound

lemma hinge_rounding (A : AtomSystem) (m : ℕ) (hm : 2 ≤ m) :
    hingeSum (S A) (97/10) 0 m ≤ (5/4)*LB A m := by
  simp only [hingeSum, zero_add, LB, mul_sum]
  apply sum_le_sum
  intro k hk
  have hh := S_le_rounded A m k hm (mem_Icc.mp hk).1 (mem_Icc.mp hk).2
  apply max_le
  · have hz := le_max_left (B A m k-T) 0
    dsimp only [T] at hz ⊢
    linarith
  · exact mul_nonneg (by norm_num) (le_max_right _ _)

#print axioms S_le_rounded
#print axioms hinge_rounding
end
end Erdos708H97.Rounded
