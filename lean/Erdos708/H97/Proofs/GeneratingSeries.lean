import Erdos708.H97.Proofs.ScalarConstants
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
open Finset BigOperators
namespace Erdos708H97.Proofs
noncomputable section
set_option maxHeartbeats 2000000

lemma late_band_bound (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) (r : ℕ) :
    (∑ a ∈ Icc 4 7, x^(a*2^(r+5))) ≤
      x^128*(x^4)^r*(1+x+x^2+x^3) := by
  have hp (a : ℕ) (ha : a ∈ Icc 4 7) :
      x^(a*2^(r+5)) ≤ x^(128+4*r+(a-4)) := by
    apply pow_le_pow_of_le_one hx hx1.le
    have hr : r+1 ≤ 2^r := Nat.lt_two_pow_self
    have ha' := mem_Icc.mp ha
    rw [pow_add]
    norm_num
    have hmul : a*(r+1) ≤ a*2^r := Nat.mul_le_mul_left a hr
    have hmul2 : 4*r ≤ a*r := Nat.mul_le_mul_right r ha'.1
    have hsub : a-4+4=a := Nat.sub_add_cancel ha'.1
    nlinarith
  apply (sum_le_sum hp).trans_eq
  norm_num [sum_Icc_succ_top]
  simp only [pow_add,pow_mul]
  ring

lemma late_series (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun r : ℕ => ∑ a ∈ Icc 4 7, x^(a*2^(r+5))) ∧
    (∑' r : ℕ, ∑ a ∈ Icc 4 7, x^(a*2^(r+5))) ≤ x^128/(1-x) := by
  have hx4 : x^4 < 1 := pow_lt_one₀ hx hx1 (by decide)
  have hs := ((summable_geometric_of_lt_one (pow_nonneg hx 4) hx4).mul_left (x^128)).mul_right (1+x+x^2+x^3)
  have hn (r : ℕ) : 0 ≤ ∑ a ∈ Icc 4 7, x^(a*2^(r+5)) := sum_nonneg (fun a ha => pow_nonneg hx _)
  have hf := hs.of_nonneg_of_le hn (late_band_bound x hx hx1)
  refine ⟨hf, (hf.tsum_le_tsum (late_band_bound x hx hx1) hs).trans_eq ?_⟩
  rw [tsum_mul_right,tsum_mul_left,tsum_geometric_of_lt_one (pow_nonneg hx 4) hx4]
  have hd : 1-x ≠ 0 := by linarith
  have hd4 : 1-x^4 ≠ 0 := by linarith
  field_simp
  ring

lemma band_series_summable (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun r : ℕ => ∑ a ∈ Icc 4 7, x^(a*2^(r+1))) := by
  have hh := (late_series x hx hx1).1
  exact (summable_nat_add_iff 4).mp (by simpa only [Nat.add_assoc] using hh)

lemma generating_series_upper (j : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    generatingSeries j x ≤ generatingUpper j x := by
  have hs := band_series_summable x hx hx1
  have he := hs.sum_add_tsum_nat_add 4
  have ht := (late_series x hx hx1).2
  have hf : (∑ r ∈ range 4, ∑ a ∈ Icc 4 7, x^(a*2^(r+1))) =
      ∑ r ∈ Icc 1 4, ∑ a ∈ Icc 4 7, x^(a*2^r) := by
    norm_num [sum_range_succ,sum_Icc_succ_top]
  rw [hf] at he
  simp only [Nat.add_assoc] at he
  dsimp only [generatingSeries,generatingUpper]
  linarith

/-- Distinct coefficients of the finite polynomial are covered by the series, including degree L. -/
lemma finite_generating_le (j L : ℕ) (hj : j ∈ Icc 4 7) (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    1+(∑ e ∈ exponents j L, x^e) ≤ generatingSeries j x := by
  classical
  have hwitness (e : ℕ) (he : e ∈ exponents j L) :
      ∃ v : ℕ × ℕ, v ∈ (range (L+1)).product (Icc 4 7) ∧
        e=v.2*2^v.1 ∧ j ≤ e := by
    simp only [exponents,mem_filter,mem_Icc] at he
    obtain ⟨⟨hj',hL⟩,a,ha,h,hh,he⟩ := he
    exact ⟨(h,a),mem_product.mpr ⟨hh,mem_Icc.mpr ha⟩,he,hj'⟩
  choose f hf using hwitness
  let w := fun v : ℕ × ℕ => if v.1=0 ∧ v.2<j then 0 else x^(v.2*2^v.1)
  have hn (v : ℕ × ℕ) : 0 ≤ w v := by dsimp [w]; split_ifs <;> positivity
  let t := (exponents j L).attach.image (fun e => f e.val e.property)
  have hinj : Set.InjOn (fun e : {e // e ∈ exponents j L} => f e.val e.property)
      ((exponents j L).attach : Set {e // e ∈ exponents j L}) := by
    intro e he g hg heq
    apply Subtype.ext
    exact (hf e.val e.property).2.1.trans ((congrArg (fun v : ℕ × ℕ => v.2*2^v.1) heq).trans (hf g.val g.property).2.1.symm)
  have hsub : t ⊆ (range (L+1)).product (Icc 4 7) := by
    intro v hv
    obtain ⟨e,he,rfl⟩ := mem_image.mp hv
    exact (hf e.val e.property).1
  have heq : (∑ e ∈ exponents j L, x^e) = ∑ v ∈ t, w v := by
    rw [show (∑ v ∈ t, w v) = ∑ e ∈ (exponents j L).attach, w (f e.val e.property) by exact sum_image hinj]
    rw [← sum_attach (exponents j L) (fun e => x^e)]
    apply sum_congr rfl
    intro e he
    dsimp only [w]
    rw [if_neg]
    · exact congrArg (fun n : ℕ => x^n) (hf e.val e.property).2.1
    · rintro ⟨h0,hsmall⟩
      have hE := (hf e.val e.property).2.1
      rw [h0,pow_zero,mul_one] at hE
      have := (hf e.val e.property).2.2
      omega
  have hb := (sum_le_sum_of_subset_of_nonneg hsub (fun v hv hnot => hn v))
  have hsum : (∑ v ∈ (range (L+1)).product (Icc 4 7), w v) =
      (∑ a ∈ Icc j 7, x^a)+(∑ r ∈ range L, ∑ a ∈ Icc 4 7, x^(a*2^(r+1))) := by
    rw [Finset.product_eq_sprod,Finset.sum_product,sum_range_succ']
    simp only [w,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,false_and,↓reduceIte,pow_zero,mul_one,true_and]
    have hfilter : (Icc 4 7).filter (fun a => ¬ a<j) = Icc j 7 := by
      ext a
      have hj' := mem_Icc.mp hj
      simp only [mem_filter,mem_Icc]
      omega
    have hzero : (∑ a ∈ Icc 4 7, if a<j then 0 else x^a) = ∑ a ∈ Icc j 7, x^a := by
      rw [← hfilter,sum_filter]
      apply sum_congr rfl
      intro a ha
      simp only [ite_not]
    rw [hzero]
    ring
  rw [hsum] at hb
  have ht := (band_series_summable x hx hx1).sum_le_tsum (range L)
    (fun r hr => sum_nonneg (fun a ha => pow_nonneg hx _))
  rw [heq]
  dsimp only [generatingSeries]
  linarith

lemma generating_series_bound (j : ℕ) (hj : j ∈ Icc 4 7) :
    generatingSeries j (tailX j) ≤ tailF j :=
  (generating_series_upper j (tailX j) (tail_parameters j hj).1.le (tail_parameters j hj).2.1).trans
    (tail_parameters j hj).2.2.2.1

#print axioms generating_series_bound
#print axioms finite_generating_le
end
end Erdos708H97.Proofs
