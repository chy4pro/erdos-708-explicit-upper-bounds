import Mathlib

open Finset BigOperators

namespace Erdos708SparseCore

private lemma moment_esymm_insert {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (x : ι → ℝ) (a : ι) (ha : a ∉ s) (k : ℕ) :
    (∑ t ∈ (insert a s).powersetCard (k + 1), ∏ i ∈ t, x i) =
      (∑ t ∈ s.powersetCard (k + 1), ∏ i ∈ t, x i) +
      x a * ∑ t ∈ s.powersetCard k, ∏ i ∈ t, x i := by
  rw [powersetCard_succ_insert ha, sum_union]
  · congr 1
    rw [sum_image, mul_sum]
    · apply sum_congr rfl
      intro t ht
      exact prod_insert (fun hat => ha ((mem_powersetCard.mp ht).1 hat))
    · intro t ht u hu heq
      have hat : a ∉ t := fun h => ha ((mem_powersetCard.mp ht).1 h)
      have hau : a ∉ u := fun h => ha ((mem_powersetCard.mp hu).1 h)
      simpa [hat, hau] using congrArg (erase · a) heq
  · apply disjoint_left.mpr
    intro t ht ht'
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ht'
    exact ha ((mem_powersetCard.mp ht).1 (mem_insert_self _ _))

private lemma factorial_mul_esymm_le {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (r : ℕ) :
    (Nat.factorial r : ℝ) * (∑ t ∈ s.powersetCard r, ∏ i ∈ t, x i) ≤
      (∑ i ∈ s, x i) ^ r := by
  classical
  induction s using Finset.induction_on generalizing r with
  | empty =>
    cases r with
    | zero => simp [powersetCard_zero]
    | succ r =>
      have hempty : (∅ : Finset ι).powersetCard (r + 1) = ∅ :=
        powersetCard_eq_empty.mpr (by simp)
      simp [hempty]
  | @insert a s ha ih =>
    have hxa : 0 ≤ x a := hx a (mem_insert_self _ _)
    have hxs : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (mem_insert_of_mem hi)
    have hs : 0 ≤ ∑ i ∈ s, x i := sum_nonneg hxs
    cases r with
    | zero => simp [powersetCard_zero]
    | succ r =>
      rw [moment_esymm_insert s x a ha r, sum_insert ha]
      calc
        _ = (Nat.factorial (r + 1) : ℝ) *
              (∑ t ∈ s.powersetCard (r + 1), ∏ i ∈ t, x i) +
            ((r + 1 : ℕ) : ℝ) * x a *
              ((Nat.factorial r : ℝ) * (∑ t ∈ s.powersetCard r, ∏ i ∈ t, x i)) := by
          rw [Nat.factorial_succ, Nat.cast_mul]
          ring
        _ ≤ (∑ i ∈ s, x i) ^ (r + 1) +
            ((r + 1 : ℕ) : ℝ) * x a * (∑ i ∈ s, x i) ^ r :=
          add_le_add (ih hxs (r + 1))
            (mul_le_mul_of_nonneg_left (ih hxs r) (by positivity))
        _ ≤ (x a + ∑ i ∈ s, x i) ^ (r + 1) := by
          simpa [mul_assoc, mul_left_comm, mul_comm, add_comm] using
            (pow_add_mul_le_add_pow hs (by positivity : 0 ≤ 2 * (∑ i ∈ s, x i) + x a)
              (r + 1))

private lemma coprime_indicator_sum_le {ι : Type*} (s : Finset ι)
    (q : ι → ℕ) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hcop : ∀ i ∈ s, ∀ k ∈ s, i ≠ k → Nat.Coprime (q i) (q k)) (N : ℕ) :
    (∑ j ∈ Icc 1 N, ∏ i ∈ s, if q i ∣ j then w i else 0) ≤
      (N : ℝ) * ∏ i ∈ s, w i / (q i : ℝ) := by
  classical
  have hdvd (j : ℕ) : (∏ i ∈ s, q i) ∣ j ↔ ∀ i ∈ s, q i ∣ j := by
    constructor
    · intro h i hi
      exact (dvd_prod_of_mem q hi).trans h
    · exact prod_dvd_of_isRelPrime
        (fun i hi k hk hik => Nat.coprime_iff_isRelPrime.mp (hcop i hi k hk hik))
  have hc : #((Icc 1 N).filter (fun j => (∏ i ∈ s, q i) ∣ j)) = N / (∏ i ∈ s, q i) := by
    have heq : (Icc 1 N).filter (fun j => (∏ i ∈ s, q i) ∣ j) =
        (range N.succ).filter (fun j => j ≠ 0 ∧ (∏ i ∈ s, q i) ∣ j) := by
      ext j
      simp only [mem_filter, mem_Icc, mem_range]
      omega
    rw [heq, Nat.card_multiples']
  calc
    _ = ((N / (∏ i ∈ s, q i) : ℕ) : ℝ) * ∏ i ∈ s, w i := by
      simp_rw [prod_ite_zero, ← hdvd]
      rw [← sum_filter, sum_const, nsmul_eq_mul, hc]
    _ ≤ ((N : ℝ) / (∏ i ∈ s, q i : ℕ)) * ∏ i ∈ s, w i :=
      mul_le_mul_of_nonneg_right Nat.cast_div_le (prod_nonneg hw)
    _ = _ := by
      rw [prod_div_distrib, Nat.cast_prod]
      ring

private lemma level_product_sum_le (T : Finset ℕ) (hT : ∀ p ∈ T, Nat.Prime p)
    (levels : ℕ → Finset (ℕ × ℝ))
    (hlev : ∀ p ∈ T, ∀ l ∈ levels p, (∃ e : ℕ, 1 ≤ e ∧ l.1 = p ^ e) ∧ 0 ≤ l.2)
    (N : ℕ) :
    (∑ j ∈ Icc 1 N, ∏ p ∈ T, ∑ l ∈ (levels p).filter (fun l => l.1 ∣ j), l.2) ≤
      (N : ℝ) * ∏ p ∈ T, ∑ l ∈ levels p, l.2 / (l.1 : ℝ) := by
  classical
  simp_rw [sum_filter, prod_sum]
  rw [sum_comm, mul_sum]
  apply sum_le_sum
  intro f hf
  apply coprime_indicator_sum_le
  · intro p hp
    exact (hlev p.1 p.2 (f p.1 p.2) (mem_pi.mp hf p.1 p.2)).2
  · intro p hp k hk hpk
    obtain ⟨⟨e, he, hqe⟩, _⟩ := hlev p.1 p.2 (f p.1 p.2) (mem_pi.mp hf p.1 p.2)
    obtain ⟨⟨d, hd, hqd⟩, _⟩ := hlev k.1 k.2 (f k.1 k.2) (mem_pi.mp hf k.1 k.2)
    rw [hqe, hqd]
    exact Nat.coprime_pow_primes e d (hT p.1 p.2) (hT k.1 k.2)
      (fun h => hpk (Subtype.ext h))

 theorem moment_bound (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (levels : ℕ → Finset (ℕ × ℝ))
    (hlev : ∀ p ∈ P, ∀ l ∈ levels p, (∃ e : ℕ, 1 ≤ e ∧ l.1 = p ^ e) ∧ 0 ≤ l.2)
    (N r : ℕ) (hN : 1 ≤ N) (hr : 1 ≤ r) :
    ∑ j ∈ Icc 1 N,
        ∑ T ∈ P.powersetCard r, ∏ p ∈ T, (∑ l ∈ (levels p).filter (fun l => l.1 ∣ j), l.2)
      ≤ (N : ℝ) * (∑ p ∈ P, ∑ l ∈ levels p, l.2 / (l.1 : ℝ)) ^ r / (Nat.factorial r : ℝ) := by
  classical
  have hh : ∀ p ∈ P, 0 ≤ ∑ l ∈ levels p, l.2 / (l.1 : ℝ) := by
    intro p hp
    exact sum_nonneg fun l hl => div_nonneg (hlev p hp l hl).2 (Nat.cast_nonneg _)
  calc
    _ = ∑ T ∈ P.powersetCard r,
          ∑ j ∈ Icc 1 N, ∏ p ∈ T, ∑ l ∈ (levels p).filter (fun l => l.1 ∣ j), l.2 :=
      sum_comm
    _ ≤ ∑ T ∈ P.powersetCard r,
          (N : ℝ) * ∏ p ∈ T, ∑ l ∈ levels p, l.2 / (l.1 : ℝ) := by
      apply sum_le_sum
      intro T hT
      exact level_product_sum_le T (fun p hp => hP p ((mem_powersetCard.mp hT).1 hp))
        levels (fun p hp => hlev p ((mem_powersetCard.mp hT).1 hp)) N
    _ = (N : ℝ) * ∑ T ∈ P.powersetCard r, ∏ p ∈ T, ∑ l ∈ levels p, l.2 / (l.1 : ℝ) :=
      (mul_sum _ _ _).symm
    _ ≤ _ := by
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < Nat.factorial r)).2
      simpa only [mul_comm] using
        factorial_mul_esymm_le P (fun p => ∑ l ∈ levels p, l.2 / (l.1 : ℝ)) hh r

#print axioms moment_bound

end Erdos708SparseCore
