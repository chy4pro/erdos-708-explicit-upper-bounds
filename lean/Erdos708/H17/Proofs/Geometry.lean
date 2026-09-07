import Erdos708.H17.Proofs.Lemma4
open Finset BigOperators
open scoped NNReal
namespace Erdos708H17.Rounded
noncomputable section
attribute [local instance] Classical.propDecidable
lemma carrier_retained_prime (A : AtomSystem) (m : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) : Nat.Prime a.1 ∧ 1 ≤ a.2 :=
  A.prime_of_mem a (mem_filter.mp (mem_filter.mp ha).1).1

lemma effective_fst_injective (A : AtomSystem) (m n : ℕ) :
    Set.InjOn Prod.fst (effective A m n : Set (ℕ × ℕ)) := by
  intro a ha b hb hab
  obtain ⟨ha, had, ham⟩ := mem_filter.mp ha
  obtain ⟨hb, hbd, hbm⟩ := mem_filter.mp hb
  exact Prod.ext hab (le_antisymm (hbm a ha hab had) (ham b hb hab.symm hbd))

lemma orderKey_injective (A : AtomSystem) : Function.Injective (orderKey A) := by
  intro a b hab
  exact congrArg (fun k : Lex (ℕ × Lex (ℕ × ℕ)) => ofLex (ofLex k).2) hab

lemma list_toFinset_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (l : List α) : (l.map f).toFinset = l.toFinset.image f := by
  ext b
  simp

lemma orderedLevels_toFinset (A : AtomSystem) (s : Finset (ℕ × ℕ)) :
    (orderedLevels A s).toFinset = s := by
  simp [orderedLevels, list_toFinset_map, image_image, orderKey, Function.comp_def]

lemma orderedLevels_nodup (A : AtomSystem) (s : Finset (ℕ × ℕ)) :
    (orderedLevels A s).Nodup := by
  apply List.Nodup.map_on _ ((s.image (orderKey A)).sort_nodup _)
  intro k hk l hl hkl
  have hk' : k ∈ s.image (orderKey A) := by simpa using hk
  have hl' : l ∈ s.image (orderKey A) := by simpa using hl
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hk'
  obtain ⟨b, hb, rfl⟩ := mem_image.mp hl'
  change a = b at hkl
  rw [hkl]

lemma map_orderedLevels (A : AtomSystem) (s : Finset (ℕ × ℕ)) :
    (orderedLevels A s).map (orderKey A) = (s.image (orderKey A)).sort := by
  rw [orderedLevels, List.map_map]
  calc
    _ = List.map id ((s.image (orderKey A)).sort (· ≤ ·)) := by
      apply List.map_congr_left
      intro k hk
      have hk' : k ∈ s.image (orderKey A) := by simpa using hk
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hk'
      rfl
    _ = _ := List.map_id _

lemma orderedLevels_of_list (A : AtomSystem) (l : List (ℕ × ℕ))
    (hnd : l.Nodup) (hord : (l.map (orderKey A)).Pairwise (· ≤ ·)) :
    orderedLevels A l.toFinset = l := by
  apply (orderKey_injective A).list_map
  rw [map_orderedLevels, ← list_toFinset_map]
  exact (List.toFinset_sort (· ≤ ·) (hnd.map (orderKey_injective A))).mpr hord

lemma modulus_dvd_product_iff (A : AtomSystem) (m : ℕ) (s : Finset (ℕ × ℕ))
    (hs : s ⊆ retained A m) (hinj : Set.InjOn Prod.fst (s : Set (ℕ × ℕ)))
    (b : ℕ × ℕ) (hb : b ∈ retained A m) :
    (modulus b ∣ ∏ a ∈ s, modulus a) ↔ ∃ a ∈ s, a.1 = b.1 ∧ b.2 ≤ a.2 := by
  classical
  have hbp := carrier_retained_prime A m hb
  induction s using Finset.induction_on with
  | empty =>
    have hb1 : 1 < modulus b := hbp.1.one_lt.trans_le (by
      simpa only [modulus, pow_one] using Nat.pow_le_pow_right hbp.1.pos hbp.2)
    simp [ne_of_gt hb1]
  | @insert a s ha ih =>
    have har : a ∈ retained A m := hs (mem_insert_self _ _)
    have hs' : s ⊆ retained A m := fun c hc => hs (mem_insert_of_mem hc)
    have hinj' : Set.InjOn Prod.fst (s : Set (ℕ × ℕ)) :=
      fun c hc d hd hcd => hinj (mem_insert_of_mem hc) (mem_insert_of_mem hd) hcd
    by_cases hab : a.1 = b.1
    · have hcop : Nat.Coprime (modulus b) (∏ c ∈ s, modulus c) := by
        apply Nat.Coprime.prod_right
        intro c hc
        apply Nat.coprime_pow_primes _ _ hbp.1 (carrier_retained_prime A m (hs' hc)).1
        intro hbc
        have hac : a = c := hinj (mem_insert_self _ _) (mem_insert_of_mem hc) (hab.trans hbc)
        exact ha (hac ▸ hc)
      rw [prod_insert ha, hcop.dvd_mul_right]
      have hdvd : modulus b ∣ modulus a ↔ b.2 ≤ a.2 := by
        simpa only [modulus, hab] using Nat.pow_dvd_pow_iff_le_right hbp.1.one_lt
      rw [hdvd]
      constructor
      · intro h
        exact ⟨a, mem_insert_self _ _, hab, h⟩
      · rintro ⟨c, hc, hcb, hbc⟩
        have hca : c = a := hinj hc (mem_insert_self _ _) (hcb.trans hab.symm)
        simpa only [hca] using hbc
    · have hcop : Nat.Coprime (modulus b) (modulus a) :=
        Nat.coprime_pow_primes _ _ hbp.1 (carrier_retained_prime A m har).1 (Ne.symm hab)
      rw [prod_insert ha, hcop.dvd_mul_left]
      constructor
      · intro hdiv
        obtain ⟨c, hc, hcb, hbc⟩ := (ih hs' hinj').mp hdiv
        exact ⟨c, mem_insert_of_mem hc, hcb, hbc⟩
      · rintro ⟨c, hc, hcb, hbc⟩
        apply (ih hs' hinj').mpr
        rcases mem_insert.mp hc with rfl | hc
        · exact (hab hcb).elim
        · exact ⟨c, hc, hcb, hbc⟩

lemma effective_product (A : AtomSystem) (m : ℕ) (s : Finset (ℕ × ℕ))
    (hs : s ⊆ retained A m) (hinj : Set.InjOn Prod.fst (s : Set (ℕ × ℕ))) :
    effective A m (∏ a ∈ s, modulus a) = s := by
  ext b
  constructor
  · intro hb
    obtain ⟨hb, hbd, hbm⟩ := mem_filter.mp hb
    obtain ⟨a, ha, hab, hba⟩ := (modulus_dvd_product_iff A m s hs hinj b hb).mp hbd
    have hab' : a.2 ≤ b.2 := hbm a (hs ha) hab (dvd_prod_of_mem modulus ha)
    have hbeq : b = a := Prod.ext hab.symm (le_antisymm hba hab')
    simpa only [hbeq] using ha
  · intro hb
    apply mem_filter.mpr
    refine ⟨hs hb, dvd_prod_of_mem modulus hb, ?_⟩
    intro a ha hab had
    obtain ⟨c, hc, hca, hac⟩ := (modulus_dvd_product_iff A m s hs hinj a ha).mp had
    have hcb : c = b := hinj hc hb (hca.trans hab)
    simpa only [hcb] using hac

lemma prefix_nodup (A : AtomSystem) (m k i : ℕ) :
    (prefixLevels A m k i).Nodup := (orderedLevels_nodup A (effective A m k)).take

lemma prefix_subset_effective (A : AtomSystem) (m k i : ℕ) :
    (prefixLevels A m k i).toFinset ⊆ effective A m k := by
  intro a ha
  have hamem := List.mem_of_mem_take (List.mem_toFinset.mp ha)
  have hh := List.mem_toFinset.mpr hamem
  change a ∈ (orderedLevels A (effective A m k)).toFinset at hh
  rwa [orderedLevels_toFinset] at hh

lemma effectiveList_prefix (A : AtomSystem) (m k i : ℕ) :
    effectiveList A m (prefixProd A m k i) = prefixLevels A m k i := by
  let s := (prefixLevels A m k i).toFinset
  have hs : s ⊆ retained A m := fun a ha =>
    (mem_filter.mp (prefix_subset_effective A m k i ha)).1
  have hinj : Set.InjOn Prod.fst (s : Set (ℕ × ℕ)) := fun a ha b hb hab =>
    effective_fst_injective A m k (prefix_subset_effective A m k i ha)
      (prefix_subset_effective A m k i hb) hab
  have hprod : ∏ a ∈ s, modulus a = prefixProd A m k i := List.prod_toFinset modulus (prefix_nodup A m k i)
  have heff : effective A m (prefixProd A m k i) = s := by
    rw [← hprod]
    exact effective_product A m s hs hinj
  rw [effectiveList, heff]
  apply orderedLevels_of_list A _ (prefix_nodup A m k i)
  rw [prefixLevels, effectiveList, List.map_take, map_orderedLevels]
  exact ((effective A m k).image (orderKey A)).pairwise_sort (· ≤ ·) |>.take

lemma effective_value_eq_bp (A : AtomSystem) (m n : ℕ) (a : ℕ × ℕ)
    (ha : a ∈ effective A m n) : bp A m a.1 n = (levelValue A a : ℝ) := by
  obtain ⟨ha, had, ham⟩ := mem_filter.mp ha
  have hh : bpNN A m a.1 n = levelValue A a := by
    apply le_antisymm
    · apply Finset.sup_le
      intro b hb
      obtain ⟨hb, hbp, hbd⟩ := mem_filter.mp hb
      exact retained_value_mono A m hb ha hbp (ham b hb hbp hbd)
    · exact Finset.le_sup (mem_filter.mpr ⟨ha, rfl, had⟩)
  exact congrArg (fun z : ℝ≥0 => (z : ℝ)) hh

lemma bp_eq_effective_sum (A : AtomSystem) (m p n : ℕ) :
    bp A m p n = ∑ a ∈ (effective A m n).filter (fun a => a.1 = p), (levelValue A a : ℝ) := by
  classical
  let t := (retained A m).filter (fun a => a.1 = p ∧ modulus a ∣ n)
  by_cases ht : t.Nonempty
  · obtain ⟨a, ha, hmax⟩ := t.exists_max_image Prod.snd ht
    obtain ⟨har, hap, had⟩ := mem_filter.mp ha
    have hae : a ∈ effective A m n := by
      apply mem_filter.mpr
      refine ⟨har, had, ?_⟩
      intro b hb hbp hbd
      exact hmax b (mem_filter.mpr ⟨hb, hbp.trans hap, hbd⟩)
    have hfilter : (effective A m n).filter (fun b => b.1 = p) = {a} := by
      ext b
      constructor
      · intro hb
        exact mem_singleton.mpr (effective_fst_injective A m n (mem_filter.mp hb).1 hae
          ((mem_filter.mp hb).2.trans hap.symm))
      · intro hb
        obtain rfl := mem_singleton.mp hb
        exact mem_filter.mpr ⟨hae, hap⟩
    rw [hfilter, sum_singleton]
    simpa only [hap] using effective_value_eq_bp A m n a hae
  · have ht0 : t = ∅ := not_nonempty_iff_eq_empty.mp ht
    have he0 : (effective A m n).filter (fun a => a.1 = p) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro a ha
      obtain ⟨hae, hap⟩ := mem_filter.mp ha
      obtain ⟨har, had, ham⟩ := mem_filter.mp hae
      exact ht ⟨a, mem_filter.mpr ⟨har, hap, had⟩⟩
    rw [he0, sum_empty]
    change (t.sup (levelValue A) : ℝ≥0) = (0 : ℝ)
    rw [ht0, sup_empty]
    rfl

lemma B_eq_effectiveList_sum (A : AtomSystem) (m n : ℕ) :
    B A m n = ((effectiveList A m n).map (fun a => (levelValue A a : ℝ))).sum := by
  classical
  have hmap : ∀ a ∈ effective A m n, a.1 ∈ primes A := by
    intro a ha
    exact mem_image_of_mem Prod.fst (rounding_retained_mem_atoms A m (mem_filter.mp ha).1)
  calc
    _ = ∑ p ∈ primes A, ∑ a ∈ (effective A m n).filter (fun a => a.1 = p), (levelValue A a : ℝ) := by
      apply sum_congr rfl
      intro p hp
      exact bp_eq_effective_sum A m p n
    _ = ∑ a ∈ effective A m n, (levelValue A a : ℝ) :=
      sum_fiberwise_of_maps_to hmap (fun a => (levelValue A a : ℝ))
    _ = _ := by
      have hh := List.sum_toFinset (fun a => (levelValue A a : ℝ))
        (orderedLevels_nodup A (effective A m n))
      rw [orderedLevels_toFinset] at hh
      exact hh

lemma B_prefix_eq_partialMass (A : AtomSystem) (m k i : ℕ) :
    B A m (prefixProd A m k i) = partialMass A m k i := by
  rw [B_eq_effectiveList_sum, effectiveList_prefix]
  rfl

lemma prefix_succ (A : AtomSystem) (m k i : ℕ) (hi : i < (effectiveList A m k).length) :
    prefixLevels A m k (i + 1) = prefixLevels A m k i ++ [(effectiveList A m k)[i]] :=
  List.take_succ_eq_append_getElem hi

lemma partialMass_succ (A : AtomSystem) (m k i : ℕ) (hi : i < (effectiveList A m k).length) :
    partialMass A m k (i + 1) = partialMass A m k i + (levelValue A (effectiveList A m k)[i] : ℝ) := by
  simp only [partialMass, prefix_succ A m k i hi, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, add_zero]

lemma bp_dvd_mono (A : AtomSystem) (m p : ℕ) {n k : ℕ} (hnk : n ∣ k) :
    bp A m p n ≤ bp A m p k := by
  change (bpNN A m p n : ℝ) ≤ bpNN A m p k
  exact_mod_cast (show bpNN A m p n ≤ bpNN A m p k from
    Finset.sup_mono (fun a ha => mem_filter.mpr ⟨(mem_filter.mp ha).1,
      (mem_filter.mp ha).2.1, (mem_filter.mp ha).2.2.trans hnk⟩))

lemma B_dvd_mono (A : AtomSystem) (m : ℕ) {n k : ℕ} (hnk : n ∣ k) :
    B A m n ≤ B A m k := sum_le_sum (fun p hp => bp_dvd_mono A m p hnk)

lemma effective_prefix_subset (A : AtomSystem) (m k i : ℕ) :
    effective A m (prefixProd A m k i) ⊆ effective A m k := by
  have he := congrArg List.toFinset (effectiveList_prefix A m k i)
  rw [effectiveList, orderedLevels_toFinset] at he
  rw [he]
  exact prefix_subset_effective A m k i

lemma prefix_dvd (A : AtomSystem) (m k i : ℕ) : prefixProd A m k i ∣ k := by
  have he := congrArg List.toFinset (effectiveList_prefix A m k i)
  rw [effectiveList, orderedLevels_toFinset] at he
  have hh := List.prod_toFinset modulus (prefix_nodup A m k i)
  change (∏ a ∈ (prefixLevels A m k i).toFinset, modulus a) = prefixProd A m k i at hh
  rw [← hh]
  apply prod_dvd_of_isRelPrime
  · intro a ha b hb hab
    have hae := prefix_subset_effective A m k i ha
    have hbe := prefix_subset_effective A m k i hb
    apply Nat.coprime_iff_isRelPrime.mp
    exact Nat.coprime_pow_primes _ _
      (carrier_retained_prime A m (mem_filter.mp hae).1).1
      (carrier_retained_prime A m (mem_filter.mp hbe).1).1
      (fun hp => hab (effective_fst_injective A m k hae hbe hp))
  · intro a ha
    exact (mem_filter.mp (prefix_subset_effective A m k i ha)).2.1

lemma bp_zero_of_not_dvd (A : AtomSystem) (m p n : ℕ) (hpn : ¬ p ∣ n) :
    bp A m p n = 0 := by
  have he : (retained A m).filter (fun a => a.1 = p ∧ modulus a ∣ n) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro a ha
    obtain ⟨har, hap, han⟩ := mem_filter.mp ha
    have hj := (carrier_retained_prime A m har).2
    have hpq : p ∣ modulus a := by
      dsimp only [modulus]
      rw [hap]
      exact dvd_pow_self p (by omega : a.2 ≠ 0)
    exact hpn (hpq.trans han)
  norm_num [bp, bpNN, he]

lemma bp_remove_coprime (A : AtomSystem) (m P p j : ℕ) (hpP : ¬ p ∣ P) :
    bp A m p (P * j) = bp A m p j := by
  have he : (retained A m).filter (fun a => a.1 = p ∧ modulus a ∣ P * j) =
      (retained A m).filter (fun a => a.1 = p ∧ modulus a ∣ j) := by
    ext a
    simp only [mem_filter]
    constructor
    · rintro ⟨ha, hap, had⟩
      have hc : Nat.Coprime (modulus a) P :=
        ((carrier_retained_prime A m ha).1.coprime_iff_not_dvd.mpr (hap ▸ hpP)).pow_left _
      exact ⟨ha, hap, hc.dvd_mul_left.mp had⟩
    · rintro ⟨ha, hap, had⟩
      exact ⟨ha, hap, had.trans (dvd_mul_left j P)⟩
  simp only [bp, bpNN, he]

lemma retained_modulus_pos (A : AtomSystem) (m : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) : 0 < modulus a :=
  pow_pos (carrier_retained_prime A m ha).1.pos _

lemma retained_log_bound (A : AtomSystem) (m : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) :
    Real.log (modulus a : ℝ) ≤ (levelValue A a : ℝ) / 3 * Real.log (m : ℝ) := by
  have hcut := (mem_filter.mp ha).2
  have hqpos : (0 : ℝ) < modulus a := by exact_mod_cast retained_modulus_pos A m ha
  have hlog := Real.log_le_log (pow_pos hqpos (3 * 2 ^ levelHeight A a))
    (show (modulus a : ℝ) ^ (3 * 2 ^ levelHeight A a) ≤ m by exact_mod_cast hcut)
  rw [Real.log_pow, Nat.cast_mul, Nat.cast_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hcancel : (levelValue A a : ℝ) * (2 : ℝ) ^ levelHeight A a = 1 := by
    simp [levelValue, inv_pow]
  calc
    _ = ((levelValue A a : ℝ) / 3) *
        (3 * (2 : ℝ) ^ levelHeight A a * Real.log (modulus a : ℝ)) := by
      calc
        _ = ((levelValue A a : ℝ) * (2 : ℝ) ^ levelHeight A a) * Real.log (modulus a : ℝ) := by rw [hcancel]; ring
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)

lemma B_eq_effective_sum (A : AtomSystem) (m n : ℕ) :
    B A m n = ∑ a ∈ effective A m n, (levelValue A a : ℝ) := by
  have hh := List.sum_toFinset (fun a => (levelValue A a : ℝ))
    (orderedLevels_nodup A (effective A m n))
  rw [orderedLevels_toFinset] at hh
  exact (B_eq_effectiveList_sum A m n).trans hh.symm


#print axioms effectiveList_prefix
#print axioms B_prefix_eq_partialMass
#print axioms prefix_dvd
#print axioms retained_log_bound
end
end Erdos708H17.Rounded
