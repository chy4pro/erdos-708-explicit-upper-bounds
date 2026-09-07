import Erdos708.H17.ChainParts.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Nat.GCD.BigOperators

namespace Erdos708H17Chain.Proofs
open Finset BigOperators

lemma initial_multiples (m d : ℕ) : ((Icc 1 m).filter (d ∣ ·)).card = m / d := by
  have h : Icc 1 m = Ioc 0 m := by ext k; simp only [mem_Icc, mem_Ioc]; omega
  rw [h, Nat.Ioc_filter_dvd_card_eq_div]

lemma window_multiples (x m d : ℕ) :
    ((Icc (x+1) (x+m)).filter (d ∣ ·)).card = (x+m) / d - x / d := by
  classical
  have heq : (Icc (x+1) (x+m)).filter (d ∣ ·) =
      ((Ioc 0 (x+m)).filter (d ∣ ·)) \ ((Ioc 0 x).filter (d ∣ ·)) := by
    ext k
    simp only [mem_filter, mem_Icc, mem_sdiff, mem_Ioc]
    omega
  rw [heq, card_sdiff_of_subset]
  · rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div]
  · intro k hk
    simp only [mem_filter, mem_Ioc] at hk ⊢
    omega

lemma window_multiples_lower (x m d : ℕ) :
    m / d ≤ ((Icc (x+1) (x+m)).filter (d ∣ ·)).card := by
  rw [window_multiples]
  have := Nat.div_add_div_le_add_div (x := x) (y := m) (z := d)
  omega

lemma problem_subset_initial (D : Problem) : D.A ⊆ Icc 1 D.m := by
  intro a ha
  exact mem_Icc.mpr ⟨by have := D.two_le a ha; omega, le_max' _ _ ha⟩

lemma input_multiples_le (D : Problem) (d : ℕ) :
    (D.A.filter (d ∣ ·)).card ≤ (D.interval.filter (d ∣ ·)).card := by
  calc
    (D.A.filter (d ∣ ·)).card ≤ ((Icc 1 D.m).filter (d ∣ ·)).card :=
      card_le_card (filter_subset_filter _ (problem_subset_initial D))
    _ = D.m / d := initial_multiples _ _
    _ ≤ (D.interval.filter (d ∣ ·)).card := window_multiples_lower _ _ _

lemma whole_interval (D : Problem) : Covers D D.interval := by
  refine ⟨subset_rfl, ?_⟩
  have h1 : D.product ∣ D.m.factorial := by
    have h := prod_dvd_prod_of_subset D.A (Icc 1 D.m) id (problem_subset_initial D)
    have heq : (∏ a ∈ Icc 1 D.m, a) = D.m.factorial := by
      have heq : Icc 1 D.m = Ico 1 (D.m+1) := by ext a; simp only [mem_Icc, mem_Ico]; omega
      rw [heq, prod_Ico_id_eq_factorial]
    exact heq ▸ h
  have h2 : (∏ b ∈ D.interval, b) = (D.x + 1).ascFactorial D.m := by
    unfold Problem.interval
    have heq : Icc (D.x+1) (D.x+D.m) = Ico (D.x+1) (D.x+D.m+1) := by
      ext b; simp only [mem_Icc, mem_Ico]; omega
    rw [heq, prod_Ico_eq_prod_range]
    simp only [Nat.add_sub_add_right, Nat.add_sub_cancel_left]
    rw [Nat.ascFactorial_eq_prod_range]
  rw [h2]
  exact h1.trans (Nat.factorial_dvd_ascFactorial _ _)

/-- Primewise transport, allowing different primes to reuse interval elements. -/
lemma prime_transport (D : Problem) (p : ℕ) (hp : p.Prime) :
    ∃ f : D.A → ℕ, Function.Injective f ∧
      ∀ a : D.A, f a ∈ D.interval ∧ p ^ (a.val.factorization p) ∣ f a := by
  classical
  let t : D.A → Finset ℕ := fun a => D.interval.filter (p ^ (a.val.factorization p) ∣ ·)
  obtain ⟨f, hf, hmem⟩ := (all_card_le_biUnion_card_iff_existsInjective' t).mp (by
    intro s
    by_cases hs : s.Nonempty
    · obtain ⟨a, ha, hmin⟩ := s.exists_min_image (fun a : D.A => a.val.factorization p) hs
      let q := p ^ (a.val.factorization p)
      have hinput : s.image Subtype.val ⊆ D.A.filter (q ∣ ·) := by
        intro b hb
        obtain ⟨b', hb', rfl⟩ := mem_image.mp hb
        refine mem_filter.mpr ⟨b'.property, ?_⟩
        apply hp.pow_dvd_iff_le_factorization (by have := D.two_le b'.val b'.property; omega) |>.mpr
        exact hmin b' hb' 
      calc
        s.card = (s.image Subtype.val).card := (card_image_of_injective s Subtype.val_injective).symm
        _ ≤ (D.A.filter (q ∣ ·)).card := card_le_card hinput
        _ ≤ (D.interval.filter (q ∣ ·)).card := input_multiples_le D q
        _ ≤ (s.biUnion t).card := card_le_card (by
          intro b hb
          exact mem_biUnion.mpr ⟨a, ha, hb⟩)
    · simp [not_nonempty_iff_eq_empty.mp hs])
  refine ⟨f, hf, ?_⟩
  intro a
  exact mem_filter.mp (hmem a)

lemma coprime_prod_dvd {ι : Type*} (s : Finset ι) (q : ι → ℕ) (b : ℕ)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (q i).Coprime (q j))
    (hd : ∀ i ∈ s, q i ∣ b) : (∏ i ∈ s, q i) ∣ b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [prod_insert ha]
    have hc : (q a).Coprime (∏ i ∈ s, q i) := Nat.Coprime.prod_right (by
      intro i hi
      exact hcop a (mem_insert_self _ _) i (mem_insert_of_mem hi) (by intro h; subst i; contradiction))
    exact hc.mul_dvd_of_dvd_of_dvd (hd a (mem_insert_self _ _))
      (ih (fun i hi j hj hne => hcop i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hne)
        (fun i hi => hd i (mem_insert_of_mem hi)))

lemma fiber_product_dvd {ι : Type*} (s : Finset ι) (q f : ι → ℕ)
    (hd : ∀ i ∈ s, q i ∣ f i)
    (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i = f j → (q i).Coprime (q j)) :
    (∏ i ∈ s, q i) ∣ ∏ b ∈ s.image f, b := by
  classical
  rw [← prod_fiberwise_of_maps_to (fun i hi => mem_image_of_mem f hi) q]
  apply prod_dvd_prod_of_dvd
  intro b hb
  apply coprime_prod_dvd
  · intro i hi j hj hne
    exact hc i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hne
      ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)
  · intro i hi
    rw [← (mem_filter.mp hi).2]
    exact hd i (mem_filter.mp hi).1

/-- Distinct small demands can be placed outside an already occupied set. -/
lemma small_assignment {ι : Type*} (s : Finset ι) (q : ι → ℕ) (x m H : ℕ)
    (U : Finset ℕ) (hbudget : U.card + s.card ≤ H)
    (hq : ∀ i ∈ s, 0 < q i ∧ q i * H ≤ m) :
    ∃ f : s → ℕ, Function.Injective f ∧
      ∀ i : s, f i ∈ Icc (x+1) (x+m) ∧ f i ∉ U ∧ q i ∣ f i := by
  classical
  let t : s → Finset ℕ := fun i => ((Icc (x+1) (x+m)).filter (q i ∣ ·)) \ U
  obtain ⟨f, hf, ht⟩ := (all_card_le_biUnion_card_iff_existsInjective' t).mp (by
    intro v
    by_cases hv : v.Nonempty
    · obtain ⟨i, hi⟩ := hv
      have hc : H ≤ ((Icc (x+1) (x+m)).filter (q i ∣ ·)).card :=
        ((Nat.le_div_iff_mul_le (hq i i.property).1).mpr (by simpa [mul_comm] using (hq i i.property).2)).trans
          (window_multiples_lower x m (q i))
      have hdiff := card_le_card_sdiff_add_card
        (s := (Icc (x+1) (x+m)).filter (q i ∣ ·)) (t := U)
      have hvcard : v.card ≤ s.card := (card_le_univ v).trans_eq (Fintype.card_coe s)
      have hti : v.card ≤ (t i).card := by dsimp [t]; omega
      exact hti.trans (card_le_card (by intro b hb; exact mem_biUnion.mpr ⟨i, hi, hb⟩))
    · simp [not_nonempty_iff_eq_empty.mp hv])
  refine ⟨f, hf, ?_⟩
  intro i
  have h := mem_sdiff.mp (ht i)
  exact ⟨(mem_filter.mp h.1).1, h.2, (mem_filter.mp h.1).2⟩

/-- Assemble primewise large representatives and separate small representatives. -/
lemma assemble_demands {ι : Type*} [DecidableEq ι] (s Lg : Finset ι) (hL : Lg ⊆ s)
    (q f : ι → ℕ) (x m H : ℕ) (hbudget : s.card ≤ H)
    (hlarge : ∀ i ∈ Lg, f i ∈ Icc (x+1) (x+m) ∧ q i ∣ f i)
    (hcop : ∀ i ∈ Lg, ∀ j ∈ Lg, i ≠ j → f i = f j → (q i).Coprime (q j))
    (hsmall : ∀ i ∈ s \ Lg, 0 < q i ∧ q i * H ≤ m) :
    ∃ B ⊆ Icc (x+1) (x+m), B.card ≤ s.card ∧ (∏ i ∈ s, q i) ∣ ∏ b ∈ B, b := by
  classical
  let U := Lg.image f
  let T := s \ Lg
  have hUcard : U.card ≤ Lg.card := card_image_le
  have hTcard : T.card + Lg.card = s.card := card_sdiff_add_card_eq_card hL
  have hb : U.card + T.card ≤ H := by omega
  obtain ⟨g, hg, hgm⟩ := small_assignment T q x m H U hb hsmall
  let V := (univ : Finset T).image g
  have hVcard : V.card ≤ T.card := card_image_le.trans_eq (by simp)
  have hdisj : Disjoint U V := by
    apply disjoint_left.mpr
    intro b hbU hbV
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hbV
    exact (hgm i).2.1 hbU
  have hUdiv : (∏ i ∈ Lg, q i) ∣ ∏ b ∈ U, b :=
    fiber_product_dvd Lg q f (fun i hi => (hlarge i hi).2) hcop
  have hVdiv : (∏ i ∈ T, q i) ∣ ∏ b ∈ V, b := by
    change (∏ i ∈ T, q i) ∣ ∏ b ∈ univ.image g, b
    rw [prod_image hg.injOn, ← prod_coe_sort T q]
    exact prod_dvd_prod_of_dvd _ _ (fun i _ => (hgm i).2.2)
  refine ⟨U ∪ V, ?_, ?_, ?_⟩
  · intro b hb
    rcases mem_union.mp hb with hb | hb
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hb
      exact (hlarge i hi).1
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hb
      exact (hgm i).1
  · have h := card_union_le U V
    omega
  · rw [prod_union hdisj, ← prod_sdiff hL, mul_comm]
    exact Nat.mul_dvd_mul hUdiv hVdiv

#print axioms assemble_demands
#print axioms fiber_product_dvd
#print axioms small_assignment
#print axioms prime_transport
#print axioms window_multiples_lower
#print axioms whole_interval
end Erdos708H17Chain.Proofs
