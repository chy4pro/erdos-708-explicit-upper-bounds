import Erdos708.H17.ChainParts.Defs

namespace Erdos708H17Chain.Proofs
open Finset BigOperators

lemma problem_n_pos (D : Problem) : 0 < D.n := Finset.card_pos.mpr D.nonempty
lemma problem_product_pos (D : Problem) : 0 < D.product := by
  apply prod_pos
  intro a ha
  have := D.two_le a ha
  omega
lemma problem_prime (D : Problem) {p : ℕ} (hp : p ∈ D.primes) : p.Prime :=
  Nat.prime_of_mem_primeFactors hp

/-- Exact restatement of the few-primes card. The elementary tail-product estimate
replaces the paper's factorial/logarithm estimate without changing the statement. -/
theorem few_primes (D : Problem) (hm : D.m < 8 * D.n ^ 3) :
    D.primes.card < 16 * D.n := by
  classical
  have hn := problem_n_pos D
  have hupper : D.product ≤ D.m ^ D.n := by
    calc
      D.product ≤ ∏ a ∈ D.A, D.m := prod_le_prod (fun _ _ => Nat.zero_le _) (fun a ha => le_max' _ _ ha)
      _ = D.m ^ D.n := by simp [Problem.n]
  have hrad : (∏ p ∈ D.primes, p) ≤ D.product :=
    Nat.le_of_dvd (problem_product_pos D) (Nat.prod_primeFactors_dvd D.product)
  by_contra hbad
  have hc : 16 * D.n ≤ D.primes.card := by omega
  let T := D.primes \ Icc 1 (4 * D.n)
  have hcount : 4 * D.n ≤ T.card := by
    have h := card_le_card_sdiff_add_card (s := D.primes) (t := Icc 1 (4 * D.n))
    have hi : (Icc 1 (4 * D.n)).card = 4 * D.n := by simp
    rw [hi] at h
    change 4 * D.n ≤ (D.primes \ Icc 1 (4 * D.n)).card
    omega
  have htail : (4 * D.n) ^ (4 * D.n) ≤ ∏ p ∈ T, p := by
    calc
      (4 * D.n) ^ (4 * D.n) ≤ (4 * D.n) ^ T.card :=
        pow_le_pow_right₀ (by omega) hcount
      _ = ∏ _p ∈ T, 4 * D.n := by simp
      _ ≤ ∏ p ∈ T, p := by
        apply prod_le_prod (fun _ _ => Nat.zero_le _)
        intro p hp
        obtain ⟨hp, hout⟩ := mem_sdiff.mp hp
        have hpos := (problem_prime D hp).pos
        simp only [mem_Icc, not_and_or, not_le] at hout
        omega
  have hsub : (∏ p ∈ T, p) ≤ ∏ p ∈ D.primes, p := by
    apply prod_le_prod_of_subset_of_one_le sdiff_subset (fun _ _ => Nat.zero_le _)
    intro p hp _
    exact (problem_prime D hp).one_lt.le
  have hbase : 8 * D.n ^ 3 < (4 * D.n) ^ 4 := by
    have hpow : 0 < D.n ^ 3 := pow_pos hn _
    have hmul : D.n ^ 3 ≤ D.n ^ 3 * D.n := Nat.le_mul_of_pos_right _ hn
    nlinarith [show D.n ^ 3 * D.n = D.n ^ 4 by ring]
  have hstrict : D.m ^ D.n < (4 * D.n) ^ (4 * D.n) := by
    calc
      D.m ^ D.n < ((4 * D.n) ^ 4) ^ D.n := Nat.pow_lt_pow_left (hm.trans hbase) (by omega)
      _ = (4 * D.n) ^ (4 * D.n) := by rw [← pow_mul]
  exact (not_lt_of_ge (htail.trans (hsub.trans (hrad.trans hupper)))) hstrict

#print axioms few_primes
end Erdos708H17Chain.Proofs
