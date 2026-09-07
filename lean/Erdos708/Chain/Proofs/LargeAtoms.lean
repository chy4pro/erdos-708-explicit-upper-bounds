import Erdos708.Chain.Defs

namespace Erdos708Chain.Proofs
open Finset BigOperators

lemma s0_nonneg (A : AtomSystem) (k : ℕ) : 0 ≤ S0 A k :=
  sum_nonneg (fun a ha => A.weight_nonneg a (mem_filter.mp ha).1)

lemma s0_restrict_le (A : AtomSystem) (P : ℕ × ℕ → Prop) (k : ℕ) :
    S0 (restrict A P) k ≤ S0 A k := by
  classical
  apply sum_le_sum_of_subset_of_nonneg
  · intro a ha
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp ha).1).1, (mem_filter.mp ha).2⟩
  · intro a ha _
    exact A.weight_nonneg a (mem_filter.mp ha).1

lemma s_split (A : AtomSystem) (m k : ℕ) :
    S A k = S0 (small A m) k + S1 A m k := by
  classical
  simp only [S, S1, S0, small, large, restrict]
  simp only [sum_filter]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  split_ifs <;> simp_all

lemma active_large_same_prime (A : AtomSystem) (m k : ℕ) (hm : 4096 ≤ m)
    (hk : k ∈ Icc 1 m) (a b : ℕ × ℕ)
    (ha : a ∈ (large A m).atoms.filter (fun a => a.1 ^ a.2 ∣ k))
    (hb : b ∈ (large A m).atoms.filter (fun a => a.1 ^ a.2 ∣ k)) : a.1 = b.1 := by
  classical
  have ha' : a ∈ A.atoms ∧ m < 64 * a.1 ^ a.2 ∧ a.1 ^ a.2 ∣ k := by
    simpa [large, restrict, mem_filter, not_le, and_assoc] using ha
  have hb' : b ∈ A.atoms ∧ m < 64 * b.1 ^ b.2 ∧ b.1 ^ b.2 ∣ k := by
    simpa [large, restrict, mem_filter, not_le, and_assoc] using hb
  by_contra hab
  have hc := Nat.coprime_pow_primes a.2 b.2
    (A.prime_of_mem a ha'.1).1 (A.prime_of_mem b hb'.1).1 hab
  have hd : a.1 ^ a.2 * b.1 ^ b.2 ∣ k := hc.mul_dvd_of_dvd_of_dvd ha'.2.2 hb'.2.2
  have hle := Nat.le_of_dvd (by have := (mem_Icc.mp hk).1; omega) hd
  have hmul : m * m < (64 * a.1 ^ a.2) * (64 * b.1 ^ b.2) := by
    calc
      m * m < m * (64 * a.1 ^ a.2) := Nat.mul_lt_mul_of_pos_left ha'.2.1 (by omega)
      _ ≤ (64 * a.1 ^ a.2) * (64 * b.1 ^ b.2) := by
        nlinarith [Nat.mul_le_mul_left (64 * a.1 ^ a.2) (Nat.le_of_lt hb'.2.1)]
  have hkm := (mem_Icc.mp hk).2
  nlinarith

/-- Exact restatement of the large-atoms card. -/
theorem large_atoms (A : AtomSystem) (m : ℕ) (hm : 4096 ≤ m) :
    (∀ k ∈ Icc 1 m, S1 A m k ≤ 1) ∧
    (∀ k ∈ Icc 1 m, max (S A k - 65) 0 ≤ max (S0 (small A m) k - 64) 0) ∧
    (∀ b : ℕ, max (S0 (small A m) b - 1) 0 ≤ max (S A b - 1) 0) := by
  classical
  have hlarge : ∀ k ∈ Icc 1 m, S1 A m k ≤ 1 := by
    intro k hk
    let T := (large A m).atoms.filter (fun a => a.1 ^ a.2 ∣ k)
    by_cases hT : T.Nonempty
    · obtain ⟨a, ha⟩ := hT
      have hsub : T ⊆ A.atoms.filter (fun b => b.1 = a.1) := by
        intro b hb
        refine mem_filter.mpr ⟨?_, active_large_same_prime A m k hm hk b a hb ha⟩
        have hb' := hb
        simp only [T, large, restrict, mem_filter] at hb'
        exact hb'.1.1
      change (∑ b ∈ T, A.weight b) ≤ 1
      exact (sum_le_sum_of_subset_of_nonneg hsub
        (fun b hb _ => A.weight_nonneg b (mem_filter.mp hb).1)).trans (A.perPrime_le_one a.1)
    · have hempty : T = ∅ := not_nonempty_iff_eq_empty.mp hT
      change (∑ b ∈ T, A.weight b) ≤ 1
      simp [hempty]
  refine ⟨hlarge, ?_, ?_⟩
  · intro k hk
    apply max_le_max _ le_rfl
    rw [s_split]
    have := hlarge k hk
    linarith
  · intro b
    apply max_le_max _ le_rfl
    exact sub_le_sub_right (s0_restrict_le A _ b) 1

#print axioms large_atoms
end Erdos708Chain.Proofs
