import Erdos708.H17.ChainParts.Proofs.LongInterval

open Finset BigOperators
namespace Erdos708H17Chain.Chain19
open Erdos708H17Chain.Proofs

/-- The three-bin case of the paper's atom-packing lemma. -/
lemma three_bin_packing {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : ι → ℝ) (C : ℝ)
    (hC : 1 ≤ C) (hq : ∀ i ∈ s, 1 < q i ∧ q i ≤ C)
    (hP : (∏ i ∈ s, q i) ≤ C ^ 2) :
    ∃ u ⊆ s, ∃ v ⊆ s \ u, (∏ i ∈ u, q i) ≤ C ∧
      (∏ i ∈ v, q i) ≤ C ∧ (∏ i ∈ (s \ u) \ v, q i) ≤ C := by
  classical
  let P := ∏ i ∈ s, q i
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hroot : 0 < Real.sqrt C := Real.sqrt_pos.mpr hCp
  have hroot2 := Real.sq_sqrt hCp.le
  have hrootC : Real.sqrt C ≤ C := by nlinarith
  by_cases hsmall : P ≤ C
  · refine ⟨s, subset_rfl, ∅, empty_subset _, hsmall, ?_, ?_⟩ <;> simpa using hC
  have hC1 : 1 < C := by
    have : C ≠ 1 := by intro h; subst C; dsimp only [P] at hsmall; norm_num at hP; exact hsmall hP
    exact lt_of_le_of_ne hC (Ne.symm this)
  have ht : 1 < Real.sqrt C := by nlinarith
  have hchoose : ∃ u ⊆ s, Real.sqrt C ≤ ∏ i ∈ u, q i ∧ (∏ i ∈ u, q i) ≤ C := by
    by_cases hbig : ∃ i ∈ s, Real.sqrt C < q i
    · obtain ⟨i,hi,hlarge⟩ := hbig
      exact ⟨{i}, singleton_subset_iff.mpr hi, by simpa using hlarge.le, by simpa using (hq i hi).2⟩
    · obtain ⟨u,hu,hlo,hhi⟩ := product_crossing s q (Real.sqrt C) (Real.sqrt C) ht hroot
        (fun i hi => ⟨(hq i hi).1.le, le_of_not_gt (fun h => hbig ⟨i,hi,h⟩)⟩)
        (hrootC.trans (le_of_not_ge hsmall))
      exact ⟨u,hu,hlo,by nlinarith⟩
  obtain ⟨u,hu,hlo,hhi⟩ := hchoose
  let U := ∏ i ∈ u, q i
  let R := ∏ i ∈ s \ u, q i
  have hRpos : 0 < R := prod_pos (fun i hi => (hq i (mem_sdiff.mp hi).1).1.trans' zero_lt_one)
  have hUpos : 0 < U := lt_of_lt_of_le hroot hlo
  have hid : R * U = P := prod_sdiff hu
  have hU2 : C ≤ U ^ 2 := by dsimp only [U]; nlinarith
  have hP0 : 0 ≤ P := by rw [← hid]; positivity
  have hP4 : P ^ 2 ≤ C ^ 4 := by
    change P ≤ C ^ 2 at hP
    nlinarith [sq_nonneg (C ^ 2 - P)]
  have hrest : R ^ 2 ≤ C ^ 3 := by
    have hh : R ^ 2 * C ≤ P ^ 2 := by
      calc
        R ^ 2 * C ≤ R ^ 2 * U ^ 2 := mul_le_mul_of_nonneg_left hU2 (sq_nonneg R)
        _ = P ^ 2 := by rw [← mul_pow, hid]
    have : R ^ 2 * C ≤ C ^ 3 * C := by nlinarith [hh]
    exact (mul_le_mul_iff_left₀ hCp).mp this
  obtain ⟨v,hv,hvC,hrestC⟩ := two_bin_packing (s \ u) q C hC
    (fun i hi => hq i (mem_sdiff.mp hi).1) hrest
  exact ⟨u,hu,v,hv,hhi,hvC,hrestC⟩

/-- At `m ≥ H²`, three demands suffice; only the first can be a large atom. -/
lemma split_integer3 (a H m : ℕ) (ha : 0 < a) (ham : a ≤ m)
    (hH : 1 ≤ H) (hm : H ^ 2 ≤ m) :
    ∃ d e f : ℕ, a = d * e * f ∧ e * H ≤ m ∧ f * H ≤ m ∧
      (d * H ≤ m ∨ ∃ p : ℕ, p.Prime ∧ d = p ^ a.factorization p) := by
  classical
  let C : ℝ := (m : ℝ) / H
  have hHr : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hmr : (0 : ℝ) < m := by exact_mod_cast (ha.trans_le ham)
  have hHM : (H : ℝ) ^ 2 ≤ m := by exact_mod_cast hm
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hC : 1 ≤ C := by
    apply (le_div_iff₀ hHr).mpr
    nlinarith
  have hC2 : (m : ℝ) ≤ C ^ 2 := by
    dsimp [C]
    rw [div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos hHr)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hHM hmr.le]
  let q : ℕ → ℕ := fun p => p ^ a.factorization p
  have hprod : (∏ p ∈ a.primeFactors, q p) = a := (Nat.prod_primeFactors_pow_factorization ha.ne').symm
  have hprodR : (∏ p ∈ a.primeFactors, (q p : ℝ)) = a := by exact_mod_cast hprod
  have hqpos : ∀ p ∈ a.primeFactors, 1 < q p := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have he := hprime.factorization_pos_of_dvd ha.ne' (Nat.dvd_of_mem_primeFactors hp)
    exact Nat.one_lt_pow (by omega) hprime.one_lt
  by_cases hbig : ∃ p ∈ a.primeFactors, C < (q p : ℝ)
  · obtain ⟨p,hp,hlarge⟩ := hbig
    let e := ∏ r ∈ a.primeFactors \ {p}, q r
    have hid : e * q p = a := by
      simpa only [prod_singleton, hprod] using prod_sdiff (f := q) (singleton_subset_iff.mpr hp)
    have he : e * H ≤ m := by
      have hidR : (e : ℝ) * (q p : ℝ) = a := by exact_mod_cast hid
      have haR : (a : ℝ) ≤ m := by exact_mod_cast ham
      have heR : (e : ℝ) ≤ C := by nlinarith [show (0 : ℝ) ≤ e from Nat.cast_nonneg e]
      exact_mod_cast (le_div_iff₀ hHr).mp heR
    refine ⟨q p,e,1,by simpa only [mul_one] using ((mul_comm (q p) e).trans hid).symm,he,?_,
      Or.inr ⟨p,Nat.prime_of_mem_primeFactors hp,rfl⟩⟩
    nlinarith
  · have hb : ∀ p ∈ a.primeFactors, 1 < (q p : ℝ) ∧ (q p : ℝ) ≤ C := by
      intro p hp
      exact ⟨by exact_mod_cast hqpos p hp, le_of_not_gt (fun h => hbig ⟨p,hp,h⟩)⟩
    obtain ⟨u,hu,v,hv,huC,hvC,hwC⟩ := three_bin_packing a.primeFactors (fun p => (q p : ℝ)) C hC hb
      (by rw [hprodR]; exact (by exact_mod_cast ham : (a : ℝ) ≤ m).trans hC2)
    refine ⟨∏ p ∈ u, q p, ∏ p ∈ v, q p, ∏ p ∈ (a.primeFactors \ u) \ v, q p, ?_, ?_, ?_, Or.inl ?_⟩
    · rw [mul_assoc, mul_comm (∏ p ∈ v, q p), prod_sdiff hv, mul_comm, prod_sdiff hu, hprod]
    · exact_mod_cast (le_div_iff₀ hHr).mp hvC
    · exact_mod_cast (le_div_iff₀ hHr).mp hwC
    · exact_mod_cast (le_div_iff₀ hHr).mp huC

#print axioms three_bin_packing
#print axioms split_integer3
end Erdos708H17Chain.Chain19
