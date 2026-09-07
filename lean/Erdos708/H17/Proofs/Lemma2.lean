import Erdos708.H17.Proofs.Moment
open Finset BigOperators
namespace Erdos708H17.Proofs
noncomputable section

lemma prime_product_lower (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime)
    (r : ℕ) (hr : r ≤ s.card) (v : Fin r → ℕ)
    (hv : ∀ i, ((range (v i)).filter Nat.Prime).card ≤ i.val) :
    (∏ i : Fin r, v i) ≤ ∏ p ∈ s, p := by
  classical
  obtain ⟨t, hts, ht⟩ := exists_subset_card_eq hr
  let g := t.orderEmbOfFin ht
  have hbound (i : Fin r) : v i ≤ g i := by
    by_contra hn
    have hlt : g i < v i := lt_of_not_ge hn
    let f : Fin (i.val+1) → ℕ := fun j => g ⟨j.val, by omega⟩
    have hf : Function.Injective f := by
      intro a b hab
      have hh := g.injective hab
      exact Fin.ext (congrArg (fun x : Fin r => x.val) hh)
    have hsub : univ.image f ⊆ (range (v i)).filter Nat.Prime := by
      intro p hp'
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hp'
      refine mem_filter.mpr ⟨mem_range.mpr ?_, hp _ (hts (t.orderEmbOfFin_mem ht _))⟩
      exact lt_of_le_of_lt (g.monotone (by change j.val ≤ i.val; omega)) hlt
    have hcard := card_le_card hsub
    rw [card_image_of_injective _ hf, card_univ, Fintype.card_fin] at hcard
    have := hv i
    omega
  calc
    _ ≤ ∏ i : Fin r, g i := prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hbound i)
    _ = ∏ p ∈ t, p := by
      conv_rhs => rw [← image_orderEmbOfFin_univ t ht, prod_image (by exact g.injective.injOn)]
    _ ≤ ∏ p ∈ s, p := prod_le_prod_of_subset_of_one_le' hts (fun p hp' _ => (hp p hp').one_lt.le)

lemma prime_card_lt_65536 (n : ℕ) (hn : 0 < n) (hsmall : n < 65536) : n.primeFactors.card ≤ 6 := by
  by_contra hh
  have hprod := prime_product_lower n.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    7 (by omega) ![2,3,5,7,11,13,17] (by decide)
  have hdiv := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  norm_num [Fin.prod_univ_succ] at hprod
  omega

lemma prime_card_lt_two48 (n : ℕ) (hn : 0 < n) (hsmall : n < 2^48) : n.primeFactors.card ≤ 12 := by
  by_contra hh
  have hprod := prime_product_lower n.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    13 (by omega) ![2,3,5,7,11,13,17,19,23,29,31,37,41] (by decide)
  have hdiv := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  norm_num [Fin.prod_univ_succ] at hprod
  norm_num at hsmall
  omega

lemma S_le_prime_card (A : AtomSystem) (k : ℕ) (hk : 0 < k) :
    S A k ≤ (k.primeFactors.card : ℝ) := by
  classical
  let T := A.atoms.filter (fun a => a.1 ^ a.2 ∣ k)
  have hmap : ∀ a ∈ T, a.1 ∈ k.primeFactors := by
    intro a ha
    have h := mem_filter.mp ha
    have hp := A.prime_of_mem a h.1
    exact hp.1.mem_primeFactors ((dvd_pow_self a.1 (by omega)).trans h.2) hk.ne'
  change (∑ a ∈ T, A.weight a) ≤ _
  rw [← sum_fiberwise_of_maps_to hmap]
  calc
    (∑ p ∈ k.primeFactors, ∑ a ∈ T.filter (fun a => a.1 = p), A.weight a) ≤
        ∑ _p ∈ k.primeFactors, (1 : ℝ) := by
      apply sum_le_sum
      intro p hp
      apply le_trans _ (A.perPrime_le_one p)
      apply sum_le_sum_of_subset_of_nonneg
      · intro a ha
        exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp ha).1).1, (mem_filter.mp ha).2⟩
      · intro a ha _
        exact A.weight_nonneg a (mem_filter.mp ha).1
    _ = k.primeFactors.card := by simp


lemma S_restrict_le (A : AtomSystem) (P : ℕ × ℕ → Prop) (k : ℕ) :
    S (restrict A P) k ≤ S A k := by
  classical
  apply sum_le_sum_of_subset_of_nonneg
  · intro a ha
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp ha).1).1, (mem_filter.mp ha).2⟩
  · intro a ha _
    exact A.weight_nonneg a (mem_filter.mp ha).1

lemma removed_atom_small_value (A : AtomSystem) (m k : ℕ) (hk : k ∈ Icc 1 m)
    (a : ℕ × ℕ) (ha : a ∈ A.atoms) (hd : a.1^a.2 ∣ k) (hl : m < 65536 * a.1^a.2) :
    S A k ≤ 7 := by
  have hk0 : 0 < k := by have := (mem_Icc.mp hk).1; omega
  have hq : 0 < a.1^a.2 := pow_pos (A.prime_of_mem a ha).1.pos _
  obtain ⟨u, hu⟩ := hd
  have hu0 : 0 < u := by
    by_contra hh
    have hz : u = 0 := by omega
    rw [hz, mul_zero] at hu
    omega
  have hul : u < 65536 := by
    have := (mem_Icc.mp hk).2
    nlinarith
  have hc := prime_card_lt_65536 u hu0 hul
  have hcard : k.primeFactors.card ≤ 7 := by
    rw [hu, Nat.primeFactors_mul (by positivity) (by omega),
      Nat.primeFactors_prime_pow (by have := (A.prime_of_mem a ha).2; omega) (A.prime_of_mem a ha).1]
    have hh := card_union_le ({a.1} : Finset ℕ) u.primeFactors
    simp only [card_singleton] at hh
    omega
  have hs := S_le_prime_card A k hk0
  have hcr : (k.primeFactors.card : ℝ) ≤ 7 := by exact_mod_cast hcard
  linarith

lemma deletion_hinge (A : AtomSystem) (m : ℕ) (c : ℝ) (hc : 7 ≤ c)
    (k : ℕ) (hk : k ∈ Icc 1 m) : max (S A k - c) 0 = max (S_0 A m k - c) 0 := by
  classical
  have hle : S_0 A m k ≤ S A k := S_restrict_le A _ k
  by_cases hbad : ∃ a ∈ A.atoms, a.1^a.2 ∣ k ∧ m < 65536 * a.1^a.2
  · obtain ⟨a, ha, hd, hl⟩ := hbad
    have hs := removed_atom_small_value A m k hk a ha hd hl
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
  · have heq : S A k = S_0 A m k := by
      unfold S_0 S small restrict
      apply sum_congr
      · ext a
        simp only [mem_filter]
        constructor
        · rintro ⟨ha, hd⟩
          exact ⟨⟨ha, by norm_num; exact le_of_not_gt (fun hl => hbad ⟨a,ha,hd,hl⟩)⟩,hd⟩
        · rintro ⟨⟨ha, _⟩, hd⟩; exact ⟨ha,hd⟩
      · intros; rfl
    rw [heq]

lemma small_m_hinge_zero (A : AtomSystem) (m : ℕ) (hm : m < 2^48) : L A m = 0 := by
  unfold L hingeSum
  apply sum_eq_zero
  intro k hk
  have hk' : k ∈ Icc 1 m := by simpa only [zero_add] using hk
  have hs := S_le_prime_card A k (by have := (mem_Icc.mp hk').1; omega)
  have hc := prime_card_lt_two48 k (by have := (mem_Icc.mp hk').1; omega)
    ((mem_Icc.mp hk').2.trans_lt hm)
  have hcr : (k.primeFactors.card : ℝ) ≤ 12 := by exact_mod_cast hc
  apply max_eq_right
  linarith

#print axioms prime_card_lt_65536
#print axioms prime_card_lt_two48
#print axioms deletion_hinge
#print axioms small_m_hinge_zero
end
end Erdos708H17.Proofs
