import Erdos708.H17.ChainParts.Proofs.FewPrimes
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Associated

open Finset BigOperators
namespace Erdos708H17Chain.Chain19
open Erdos708H17Chain.Proofs

theorem primes_card_le (D : Problem) : D.primes.card ≤ D.n +
    ((Finset.range (Nat.sqrt D.m + 1)).filter Nat.Prime).card := by
  classical
  let L := D.primes.filter (fun p => Nat.sqrt D.m < p)
  have hex : ∀ p ∈ L, ∃ a ∈ D.A, p ∣ a := by
    intro p hp
    have hprime := problem_prime D (mem_filter.mp hp).1
    exact (hprime.prime.dvd_finsetProd_iff id).mp (Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1)
  choose f hf hdiv using hex
  have hcardL : L.card ≤ D.n := by
    apply card_le_card_of_injOn (fun p => if h : p ∈ L then f p h else 0)
    · intro p hp
      change p ∈ L at hp
      dsimp only
      rw [dite_eq_left hp]
      exact hf p hp
    · intro p hp q hq heq
      change p ∈ L at hp
      change q ∈ L at hq
      dsimp only at heq
      simp only [dite_eq_left hp, dite_eq_left hq] at heq
      by_contra hne
      have hcop := (Nat.coprime_primes (problem_prime D (mem_filter.mp hp).1)
        (problem_prime D (mem_filter.mp hq).1)).mpr hne
      have hd : p*q ∣ f p hp := hcop.mul_dvd_of_dvd_of_dvd (hdiv p hp) (heq.symm ▸ hdiv q hq)
      have ha := D.two_le _ (hf p hp)
      have hle : p*q ≤ D.m := (Nat.le_of_dvd (by omega : 0 < f p hp) hd).trans (le_max' _ _ (hf p hp))
      have hpgt := (mem_filter.mp hp).2
      have hqgt := (mem_filter.mp hq).2
      have hsq : D.m < (Nat.sqrt D.m + 1) * (Nat.sqrt D.m + 1) := Nat.lt_succ_sqrt D.m
      have hmul := Nat.mul_le_mul (show Nat.sqrt D.m + 1 ≤ p by omega)
        (show Nat.sqrt D.m + 1 ≤ q by omega)
      omega
  have hsmall : (D.primes.filter (fun p => ¬ Nat.sqrt D.m < p)).card ≤
      ((range (Nat.sqrt D.m + 1)).filter Nat.Prime).card := by
    apply card_le_card
    intro p hp
    exact mem_filter.mpr ⟨mem_range.mpr (by have := (mem_filter.mp hp).2; omega),
      problem_prime D (mem_filter.mp hp).1⟩
  have hpartition := card_filter_add_card_filter_not (s := D.primes) (fun p => Nat.sqrt D.m < p)
  dsimp only [L] at hcardL
  omega

theorem pi_le (n : ℕ) : ((Finset.range (3*n+1)).filter Nat.Prime).card ≤ n + 1 := by
  classical
  by_cases hn : n = 0
  · subst n; norm_num [filter_singleton, Nat.not_prime_zero]
  let P := (range (3*n+1)).filter Nat.Prime
  have hcard : (P.erase 3).card ≤ (range n).card := by
    apply card_le_card_of_injOn (fun p => p / 3)
    · intro p hp
      obtain ⟨hne, hp⟩ := mem_erase.mp hp
      obtain ⟨hr, hprime⟩ := mem_filter.mp hp
      have hmod : p % 3 ≠ 0 := by
        intro hm
        have := (Nat.dvd_prime hprime).mp (Nat.dvd_of_mod_eq_zero hm)
        omega
      have := mem_range.mp hr
      apply mem_range.mpr
      change p / 3 < n
      omega
    · intro p hp q hq heq
      change p / 3 = q / 3 at heq
      obtain ⟨hp3, hp⟩ := mem_erase.mp hp
      obtain ⟨hq3, hq⟩ := mem_erase.mp hq
      have hpp := (mem_filter.mp hp).2
      have hqp := (mem_filter.mp hq).2
      have hp0 : p % 3 ≠ 0 := by
        intro h; have := (Nat.dvd_prime hpp).mp (Nat.dvd_of_mod_eq_zero h); omega
      have hq0 : q % 3 ≠ 0 := by
        intro h; have := (Nat.dvd_prime hqp).mp (Nat.dvd_of_mod_eq_zero h); omega
      have hp2 := hpp.mod_two_eq_one_iff_ne_two
      have hq2 := hqp.mod_two_eq_one_iff_ne_two
      have := hpp.two_le
      have := hqp.two_le
      omega
  have := card_le_card_sdiff_add_card (s := P) (t := {3})
  simpa only [card_range] using (show P.card ≤ n + 1 by
    simp only [sdiff_singleton_eq_erase, card_singleton] at this
    simp only [card_range] at hcard
    omega)

#print axioms primes_card_le
#print axioms pi_le
end Erdos708H17Chain.Chain19
