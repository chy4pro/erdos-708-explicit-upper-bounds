import Erdos708.H17.ChainParts.Atoms

namespace Erdos708H17Chain.Proofs
open Finset BigOperators

lemma increments_sum (f : ℕ → ℝ) (hf : f 0 = 0) (N : ℕ) :
    (∑ j ∈ Icc 1 N, (f j - f (j-1))) = f N := by
  induction N with
  | zero => simp [hf]
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    simp only [Nat.add_sub_cancel]
    ring

lemma valuation_increments (p k N : ℕ) (hp : p.Prime) (hk : 0 < k)
    (f : ℕ → ℝ) (hf : f 0 = 0) :
    (∑ j ∈ Icc 1 N, if p ^ j ∣ k then f j - f (j-1) else 0) = f (min N (k.factorization p)) := by
  classical
  rw [← sum_filter]
  have heq : (Icc 1 N).filter (p ^ · ∣ k) = Icc 1 (min N (k.factorization p)) := by
    ext j
    simp only [mem_filter, mem_Icc, hp.pow_dvd_iff_le_factorization hk.ne', le_min_iff]
    tauto
  rw [heq, increments_sum f hf]

lemma monotone_valuation_window (p : ℕ) (hp : p.Prime) (f : ℕ → ℝ)
    (hf : Monotone f) (hf0 : f 0 = 0) (x m : ℕ) :
    (∑ k ∈ Icc 1 m, f (k.factorization p)) ≤ ∑ b ∈ Icc (x+1) (x+m), f (b.factorization p) := by
  classical
  let N := x+m
  have heq (T : Finset ℕ) (hT : T ⊆ Icc 1 N) :
      (∑ k ∈ T, f (k.factorization p)) = ∑ j ∈ Icc 1 N,
        (f j - f (j-1)) * ((T.filter (p ^ j ∣ ·)).card : ℝ) := by
    have hexp (k : ℕ) (hk : k ∈ T) : f (k.factorization p) =
        ∑ j ∈ Icc 1 N, if p ^ j ∣ k then f j - f (j-1) else 0 := by
      have hkm := mem_Icc.mp (hT hk)
      have hv : k.factorization p ≤ N := (Nat.factorization_lt p (by omega)).le.trans hkm.2
      rw [valuation_increments p k N hp (by omega) f hf0, min_eq_right hv]
    rw [sum_congr rfl hexp, sum_comm]
    apply sum_congr rfl
    intro j hj
    rw [← sum_filter]
    simp [mul_comm]
    ring
  rw [heq (Icc 1 m) (by intro k hk; simp only [mem_Icc] at hk ⊢; dsimp [N]; omega),
    heq (Icc (x+1) (x+m)) (by intro k hk; simp only [mem_Icc] at hk ⊢; dsimp [N]; omega)]
  apply sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left
  · exact_mod_cast (initial_multiples m (p ^ j)).trans_le (window_multiples_lower x m _)
  · exact sub_nonneg.mpr (hf (Nat.sub_le j 1))

lemma alpha_nonneg (z : Weight) (p : ℕ) (hp : p ∈ z.primes) (j : ℕ) : 0 ≤ alpha z p j := by
  unfold alpha
  apply sub_nonneg.mpr
  apply min_le_min_right
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le j 1) (z.bounds p hp).1

lemma alpha_sum (z : Weight) (p N : ℕ) : (∑ j ∈ Icc 1 N, alpha z p j) = min ((N : ℝ) * z.z p) 1 := by
  exact increments_sum (fun j => min ((j : ℝ) * z.z p) 1) (by norm_num) N

noncomputable def ofWeight (z : Weight) (N : ℕ) : AtomSystem where
  atoms := weightAtoms z N
  weight a := alpha z a.1 a.2
  prime_of_mem a ha := ⟨z.isPrime a.1 (mem_product.mp ha).1, (mem_Icc.mp (mem_product.mp ha).2).1⟩
  weight_nonneg a ha := alpha_nonneg z a.1 (mem_product.mp ha).1 a.2
  perPrime_le_one p := by
    classical
    simp only [weightAtoms, sum_filter, sum_product]
    by_cases hp : p ∈ z.primes
    · rw [sum_eq_single p]
      · simp only [ite_true]
        rw [alpha_sum]
        exact min_le_right _ _
      · intro q hq hne
        apply sum_eq_zero
        intro j hj
        simp [hne]
      · exact fun h => False.elim (h hp)
    · have hh : (∑ q ∈ z.primes, ∑ j ∈ Icc 1 N, if (q,j).1 = p then alpha z (q,j).1 (q,j).2 else 0) = 0 := by
        apply sum_eq_zero
        intro q hq
        apply sum_eq_zero
        intro j hj
        have hne : q ≠ p := by intro h; exact hp (h ▸ hq)
        simp [hne]
      simpa only [hh] using (show (0 : ℝ) ≤ 1 by norm_num)

lemma ofWeight_value (z : Weight) (N k : ℕ) (hk : 0 < k) :
    S0 (ofWeight z N) k = ∑ p ∈ z.primes, min ((min N (k.factorization p) : ℕ) * z.z p) 1 := by
  classical
  simp only [S0, ofWeight, weightAtoms, sum_filter, sum_product]
  apply sum_congr rfl
  intro p hp
  exact valuation_increments p k N (z.isPrime p hp) hk
    (fun j => min ((j : ℝ) * z.z p) 1) (by norm_num)

lemma ofWeight_capped_eq (z : Weight) (N k : ℕ) (hk : k ∈ Icc 1 N) :
    S (ofWeight z N) k = capped z k := by
  have hkm := mem_Icc.mp hk
  rw [S, ofWeight_value z N k (by omega)]
  apply sum_congr rfl
  intro p hp
  rw [min_eq_right ((Nat.factorization_lt p (by omega)).le.trans hkm.2)]
  simp only [mul_comm]

lemma ofWeight_capped_le (z : Weight) (N k : ℕ) (hk : 0 < k) :
    S (ofWeight z N) k ≤ capped z k := by
  rw [S, ofWeight_value z N k hk]
  apply sum_le_sum
  intro p hp
  apply min_le_min_right
  rw [mul_comm (z.z p)]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_right N (k.factorization p)) (z.bounds p hp).1

lemma ofWeight_mean (z : Weight) (m : ℕ) : H64 (ofWeight z m) m = weightH64 z m := by
  classical
  simp only [H64, small, restrict, mean, ofWeight, weightH64, sum_filter]
  apply sum_congr rfl
  intro a ha
  split_ifs <;> rfl

noncomputable def excess (z : Weight) (k : ℕ) : ℝ :=
  ∑ p ∈ z.primes, max (z.z p * (k.factorization p : ℝ) - 1) 0

lemma excess_window (z : Weight) (m x : ℕ) :
    (∑ k ∈ Icc 1 m, excess z k) ≤ ∑ b ∈ Icc (x+1) (x+m), excess z b := by
  unfold excess
  rw [sum_comm, sum_comm (s := Icc (x+1) (x+m))]
  apply sum_le_sum
  intro p hp
  apply monotone_valuation_window p (z.isPrime p hp) (fun j => max (z.z p * (j : ℝ) - 1) 0) _ _ x m
  · intro a b hab
    apply max_le_max _ le_rfl
    apply sub_le_sub_right
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hab) (z.bounds p hp).1
  · norm_num

lemma excess_nonneg (z : Weight) (k : ℕ) : 0 ≤ excess z k :=
  sum_nonneg (fun _ _ => le_max_right _ _)

lemma peel (z : Weight) (k : ℕ) : w z k = excess z k + capped z k := by
  unfold w weightedValuation excess capped
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  by_cases h : z.z p * (k.factorization p : ℝ) ≤ 1
  · rw [max_eq_right (by linarith), min_eq_left h, zero_add]
  · rw [max_eq_left (by linarith), min_eq_right (by linarith)]
    ring

lemma small_capped_excess_zero (z : Weight) (k : ℕ) (hc : capped z k < 1) : excess z k = 0 := by
  classical
  apply sum_eq_zero
  intro p hp
  have hterm : min (z.z p * (k.factorization p : ℝ)) 1 ≤ capped z k :=
    single_le_sum (fun q hq => le_min (mul_nonneg (z.bounds q hq).1 (Nat.cast_nonneg _)) zero_le_one) hp
  have ht : z.z p * (k.factorization p : ℝ) ≤ 1 := by
    by_contra hh
    rw [min_eq_right (by linarith)] at hterm
    linarith
  exact max_eq_right (by linarith)

lemma peel_right (z : Weight) (k : ℕ) :
    max (w z k - 1) 0 = excess z k + max (capped z k - 1) 0 := by
  have hE := excess_nonneg z k
  rw [peel]
  by_cases hc : 1 ≤ capped z k
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    ring
  · rw [small_capped_excess_zero z k (lt_of_not_ge hc), zero_add, zero_add]

lemma peel_left (z : Weight) (k : ℕ) (c : ℝ) :
    max (w z k - c) 0 ≤ excess z k + max (capped z k - c) 0 := by
  rw [peel]
  apply max_le
  · have := le_max_left (capped z k - c) 0
    linarith
  · exact add_nonneg (excess_nonneg z k) (le_max_right _ _)

lemma capped_to_weight (z : Weight) (m x : ℕ)
    (hc : hingeSum (capped z) 17 0 m ≤ hingeSum (capped z) 1 x m) :
    hingeSum (w z) 17 0 m ≤ hingeSum (w z) 1 x m := by
  have hL : hingeSum (w z) 17 0 m ≤ (∑ k ∈ Icc 1 m, excess z k) + hingeSum (capped z) 17 0 m := by
    have h := sum_le_sum (s := Icc 1 m) (fun k _ => peel_left z k 17)
    rw [sum_add_distrib] at h
    simpa only [hingeSum, zero_add] using h
  have hR : hingeSum (w z) 1 x m = (∑ b ∈ Icc (x+1) (x+m), excess z b) + hingeSum (capped z) 1 x m := by
    unfold hingeSum
    simp_rw [peel_right, sum_add_distrib]
  have he := excess_window z m x
  rw [hR]
  linarith

lemma atoms_to_capped (z : Weight) (m x : ℕ)
    (ha : hingeSum (S (ofWeight z m)) 17 0 m ≤ hingeSum (S (ofWeight z m)) 1 x m) :
    hingeSum (capped z) 17 0 m ≤ hingeSum (capped z) 1 x m := by
  have hL : hingeSum (S (ofWeight z m)) 17 0 m = hingeSum (capped z) 17 0 m := by
    apply sum_congr rfl
    intro k hk
    rw [ofWeight_capped_eq z m k (by simpa using hk)]
  have hR : hingeSum (S (ofWeight z m)) 1 x m ≤ hingeSum (capped z) 1 x m := by
    apply sum_le_sum
    intro b hb
    apply max_le_max _ le_rfl
    exact sub_le_sub_right (ofWeight_capped_le z m b (by have := (mem_Icc.mp hb).1; omega)) 1
  rw [hL] at ha
  exact ha.trans hR

#print axioms capped_to_weight
#print axioms monotone_valuation_window
#print axioms ofWeight_value
#print axioms excess_window
end Erdos708H17Chain.Proofs
