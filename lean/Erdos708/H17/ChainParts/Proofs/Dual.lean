import Erdos708.H17.ChainParts.Proofs.Rounding
import Erdos708.H17.ChainParts.LP

namespace Erdos708H17Chain.Proofs
open Finset BigOperators

lemma weighted_sum_swap (T P : Finset ℕ) (z : ℕ → ℝ) :
    (∑ a ∈ T, weightedValuation P z a) = ∑ p ∈ P, z p * ∑ a ∈ T, (a.factorization p : ℝ) := by
  unfold weightedValuation
  rw [sum_comm]
  simp only [mul_sum]

lemma weak_dual (D : Problem) (z : ℕ → ℝ) (hz : ∀ p ∈ D.primes, 0 ≤ z p)
    (y : ℕ → ℝ) (hy : FractionalCover D y) : dualObjective D z ≤ coverCost D y := by
  have hc : (∑ a ∈ D.A, weightedValuation D.primes z a) ≤
      ∑ b ∈ D.interval, weightedValuation D.primes z b * y b := by
    rw [weighted_sum_swap]
    calc
      (∑ p ∈ D.primes, z p * ∑ a ∈ D.A, (a.factorization p : ℝ)) ≤
          ∑ p ∈ D.primes, z p * ∑ b ∈ D.interval, (b.factorization p : ℝ) * y b :=
        sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hy.2 p hp) (hz p hp))
      _ = ∑ b ∈ D.interval, weightedValuation D.primes z b * y b := by
        simp only [mul_sum, weightedValuation, sum_mul]
        rw [sum_comm]
        apply sum_congr rfl
        intro b hb
        apply sum_congr rfl
        intro p hp
        ring
  have hp : ∀ b ∈ D.interval, weightedValuation D.primes z b * y b ≤
      y b + max (weightedValuation D.primes z b - 1) 0 := by
    intro b hb
    have hyb := hy.1 b hb
    by_cases hw : weightedValuation D.primes z b ≤ 1
    · rw [max_eq_right (by linarith)]
      nlinarith
    · rw [max_eq_left (by linarith)]
      nlinarith
  have hs := sum_le_sum hp
  rw [sum_add_distrib] at hs
  unfold dualObjective hingeSum coverCost
  change (∑ a ∈ D.A, weightedValuation D.primes z a) -
    (∑ b ∈ D.interval, max (weightedValuation D.primes z b - 1) 0) ≤ ∑ b ∈ D.interval, y b
  linarith

lemma weak_dual_value (D : Problem) (z : ℕ → ℝ) (hz : ∀ p ∈ D.primes, 0 ≤ z p) :
    dualObjective D z ≤ fractionalValue D := by
  apply le_csInf
  · exact ⟨coverCost D (fun _ => 1), ⟨fun _ => 1, ones_cover D, rfl⟩⟩
  · rintro t ⟨y,hy,rfl⟩
    exact weak_dual D z hz y hy

lemma clip_hinge (P : Finset ℕ) (z : ℕ → ℝ) (hz : ∀ p ∈ P, 0 ≤ z p) (n : ℕ) :
    max (weightedValuation P z n - 1) 0 =
      max (weightedValuation P (fun p => min (z p) 1) n - 1) 0 +
      (weightedValuation P z n - weightedValuation P (fun p => min (z p) 1) n) := by
  let c := weightedValuation P (fun p => min (z p) 1) n
  have hle : c ≤ weightedValuation P z n := by
    apply sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)
  by_cases hc : 1 ≤ c
  · change max (_ - 1) 0 = max (c - 1) 0 + (_ - c)
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    ring
  · have heq : weightedValuation P z n = c := by
      apply sum_congr rfl
      intro p hp
      by_cases hv : n.factorization p = 0
      · simp [hv]
      have hv1 : (1 : ℝ) ≤ n.factorization p := by exact_mod_cast (show 1 ≤ n.factorization p by omega)
      have hterm : min (z p) 1 * (n.factorization p : ℝ) ≤ c :=
        single_le_sum (fun q hq => mul_nonneg (le_min (hz q hq) zero_le_one) (Nat.cast_nonneg _)) hp
      have hzp : z p ≤ 1 := by
        by_contra hh
        rw [min_eq_right (by linarith)] at hterm
        simp only [one_mul] at hterm
        linarith
      simp only [min_eq_left hzp]
    change max (_ - 1) 0 = max (c - 1) 0 + (_ - c)
    rw [heq, sub_self, add_zero]

lemma clip_dual (D : Problem) (z : ℕ → ℝ) (hz : ∀ p ∈ D.primes, 0 ≤ z p) :
    dualObjective D z ≤ dualObjective D (fun p => min (z p) 1) := by
  let zc : ℕ → ℝ := fun p => min (z p) 1
  let dz : ℕ → ℝ := fun p => z p - zc p
  have hdz : ∀ p ∈ D.primes, 0 ≤ dz p := fun p _ => sub_nonneg.mpr (min_le_left _ _)
  have hdemand : (∑ a ∈ D.A, weightedValuation D.primes dz a) ≤
      ∑ b ∈ D.interval, weightedValuation D.primes dz b := by
    rw [weighted_sum_swap, weighted_sum_swap]
    apply sum_le_sum
    intro p hp
    have h := (ones_cover D).2 p hp
    simp only [mul_one] at h
    exact mul_le_mul_of_nonneg_left h (hdz p hp)
  have hdiff (n : ℕ) : weightedValuation D.primes dz n =
      weightedValuation D.primes z n - weightedValuation D.primes zc n := by
    simp only [weightedValuation, dz, sub_mul, sum_sub_distrib]
  simp_rw [hdiff, sum_sub_distrib] at hdemand
  have hhinge : hingeSum (weightedValuation D.primes z) 1 D.x D.m =
      hingeSum (weightedValuation D.primes zc) 1 D.x D.m +
      ((∑ b ∈ D.interval, weightedValuation D.primes z b) -
        ∑ b ∈ D.interval, weightedValuation D.primes zc b) := by
    unfold hingeSum
    simp_rw [clip_hinge D.primes z hz, sum_add_distrib, sum_sub_distrib]
    rfl
  unfold dualObjective
  rw [hhinge]
  linarith

noncomputable def finiteDual (D : Problem) (z : D.primes → ℝ) : ℝ :=
  (∑ p, z p * demand D p.val) - ∑ b : D.interval,
    max ((∑ p : D.primes, z p * (b.val.factorization p.val : ℝ)) - 1) 0

lemma finiteDual_eq (D : Problem) (z : D.primes → ℝ) (z₀ : ℕ → ℝ)
    (hz : ∀ p : D.primes, z₀ p.val = z p) : finiteDual D z = dualObjective D z₀ := by
  unfold finiteDual dualObjective
  rw [weighted_sum_swap]
  unfold hingeSum
  change _ = (∑ p ∈ D.primes, z₀ p * demand D p) -
    ∑ b ∈ D.interval, max (weightedValuation D.primes z₀ b - 1) 0
  rw [← sum_coe_sort D.primes (fun p => z₀ p * demand D p),
    ← sum_coe_sort D.interval (fun b => max (weightedValuation D.primes z₀ b - 1) 0)]
  simp only [hz]
  congr 1
  apply sum_congr rfl
  intro b hb
  congr 2
  unfold weightedValuation
  rw [← sum_coe_sort D.primes (fun p => z₀ p * (b.val.factorization p : ℝ))]
  simp only [hz]

lemma dual_above (D : Problem) (r : ℝ) (hr : r < fractionalValue D) :
    ∃ z : ℕ → ℝ, (∀ p ∈ D.primes, 0 ≤ z p) ∧ r < dualObjective D z := by
  classical
  have hfeas : ∃ y : D.interval → ℝ, (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧
      ∀ p : D.primes, demand D p.val ≤ ∑ b, (b.val.factorization p.val : ℝ) * y b := by
    refine ⟨fun _ => 1, fun _ => ⟨by norm_num, le_rfl⟩, ?_⟩
    intro p
    have h := (ones_cover D).2 p.val p.property
    rw [sum_coe_sort D.interval (fun b => (b.factorization p.val : ℝ) * 1)]
    exact h
  have hstrict (y : D.interval → ℝ) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1)
      (hc : ∀ p : D.primes, demand D p.val ≤ ∑ b, (b.val.factorization p.val : ℝ) * y b) :
      r < ∑ i, y i := by
    let y₀ : ℕ → ℝ := fun i => if h : i ∈ D.interval then y ⟨i,h⟩ else 0
    have hy₀ (i : D.interval) : y₀ i.val = y i := by simp [y₀, i.property]
    have hcover : FractionalCover D y₀ := by
      refine ⟨fun i hi => ?_, fun p hp => ?_⟩
      · simpa only [y₀, dite_eq_left hi] using hy ⟨i,hi⟩
      · rw [← sum_coe_sort D.interval (fun b => (b.factorization p : ℝ) * y₀ b)]
        simpa only [hy₀] using hc ⟨p,hp⟩
    have hval : fractionalValue D ≤ coverCost D y₀ := by
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro t ⟨v,hv,rfl⟩
        exact sum_nonneg (fun i hi => (hv.1 i hi).1)
      · exact ⟨y₀,hcover,rfl⟩
    have hcost : coverCost D y₀ = ∑ i, y i := by
      unfold coverCost
      rw [← sum_coe_sort D.interval y₀]
      simp only [hy₀]
    exact hr.trans_le (hcost ▸ hval)
  obtain ⟨z, hz, hobj⟩ := separating_dual
    (fun (p : D.primes) (b : D.interval) => (b.val.factorization p.val : ℝ))
    (fun p : D.primes => demand D p.val) r hfeas hstrict
  let z₀ : ℕ → ℝ := fun p => if h : p ∈ D.primes then z ⟨p,h⟩ else 0
  have hz₀ (p : D.primes) : z₀ p.val = z p := by simp [z₀, p.property]
  refine ⟨z₀, ?_, ?_⟩
  · intro p hp
    simpa only [z₀, dite_eq_left hp] using hz ⟨p,hp⟩
  · exact (finiteDual_eq D z z₀ hz₀) ▸ hobj

/-- Exact restatement of the duality card. -/
theorem dual (D : Problem) :
    ∃ z : ℕ → ℝ, (∀ p ∈ D.primes, 0 ≤ z p ∧ z p ≤ 1) ∧
      fractionalValue D = dualObjective D z ∧
      ∀ z' : ℕ → ℝ, (∀ p ∈ D.primes, 0 ≤ z' p) →
        dualObjective D z' ≤ dualObjective D z := by
  classical
  have hcont : Continuous (finiteDual D) := by
    unfold finiteDual
    fun_prop
  have hcompact : IsCompact (Set.Icc (0 : D.primes → ℝ) 1) := isCompact_Icc
  have hnonempty : (Set.Icc (0 : D.primes → ℝ) 1).Nonempty := ⟨0, le_rfl, by intro p; norm_num⟩
  obtain ⟨z, hz, hmax⟩ := hcompact.exists_isMaxOn hnonempty hcont.continuousOn
  let z₀ : ℕ → ℝ := fun p => if h : p ∈ D.primes then z ⟨p,h⟩ else 0
  have hz₀ (p : D.primes) : z₀ p.val = z p := by simp [z₀, p.property]
  have hbounds : ∀ p ∈ D.primes, 0 ≤ z₀ p ∧ z₀ p ≤ 1 := by
    intro p hp
    have hh : 0 ≤ z ⟨p,hp⟩ ∧ z ⟨p,hp⟩ ≤ 1 := ⟨hz.1 ⟨p,hp⟩, hz.2 ⟨p,hp⟩⟩
    simpa only [z₀, dite_eq_left hp] using hh
  have hglobal : ∀ z' : ℕ → ℝ, (∀ p ∈ D.primes, 0 ≤ z' p) →
      dualObjective D z' ≤ dualObjective D z₀ := by
    intro z' hz'
    let zc : D.primes → ℝ := fun p => min (z' p.val) 1
    have hzc : zc ∈ Set.Icc 0 1 :=
      ⟨fun p => le_min (hz' p.val p.property) zero_le_one, fun p => min_le_right _ _⟩
    have hh : finiteDual D zc ≤ finiteDual D z := hmax hzc
    have hleft := finiteDual_eq D zc (fun p => min (z' p) 1) (fun _ => rfl)
    have hright := finiteDual_eq D z z₀ hz₀
    rw [hleft, hright] at hh
    exact (clip_dual D z' hz').trans hh
  refine ⟨z₀, hbounds, ?_, hglobal⟩
  apply le_antisymm
  · by_contra hbad
    obtain ⟨v, hv, hgt⟩ := dual_above D (dualObjective D z₀) (lt_of_not_ge hbad)
    exact (not_lt_of_ge (hglobal v hv)) hgt
  · exact weak_dual_value D z₀ (fun p hp => (hbounds p hp).1)

#print axioms weak_dual_value
#print axioms clip_dual
#print axioms dual_above
#print axioms dual
end Erdos708H17Chain.Proofs
