import Erdos708.Chain.Arithmetic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

namespace Erdos708Chain.Proofs
open Finset BigOperators

/-- A dependent collection of columns has a nonzero direction preserving every row. -/
lemma kernel_direction {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : κ → ι → ℝ) (hcard : Fintype.card κ < Fintype.card ι) :
    ∃ v : ι → ℝ, (∀ p, ∑ i, M p i * v i = 0) ∧ (∃ i, v i ≠ 0) ∧ ∑ i, v i ≤ 0 := by
  classical
  have hdep : ¬ LinearIndependent ℝ (fun i p => M p i) := by
    intro h
    have hh := h.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at hh
    omega
  obtain ⟨v, hv, hne⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hrow : ∀ p, ∑ i, M p i * v i = 0 := by
    intro p
    have h := congrFun hv p
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_comm] using h
  by_cases hcost : ∑ i, v i ≤ 0
  · exact ⟨v, hrow, hne, hcost⟩
  · refine ⟨fun i => -v i, ?_, ?_, ?_⟩
    · intro p
      simp only [mul_neg, sum_neg_distrib, hrow, neg_zero]
    · obtain ⟨i, hi⟩ := hne
      exact ⟨i, neg_ne_zero.mpr hi⟩
    · rw [sum_neg_distrib]
      linarith

/-- Move inside a finite cube until a coordinate reaches its boundary. -/
lemma cube_step {ι : Type*} [Fintype ι] (y v : ι → ℝ)
    (hy : ∀ i, 0 < y i ∧ y i < 1) (hv : ∃ i, v i ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, 0 ≤ y i + t * v i ∧ y i + t * v i ≤ 1) ∧
      ∃ i, y i + t * v i = 0 ∨ y i + t * v i = 1 := by
  classical
  let s : Finset ι := univ.filter (fun i => v i ≠ 0)
  let bound : ι → ℝ := fun i => if 0 < v i then (1-y i) / v i else -y i / v i
  have hs : s.Nonempty := by obtain ⟨i, hi⟩ := hv; exact ⟨i, by simp [s, hi]⟩
  have hbpos : ∀ i ∈ s, 0 < bound i := by
    intro i hi
    have hvi : v i ≠ 0 := (mem_filter.mp hi).2
    dsimp [bound]
    split_ifs with h
    · exact div_pos (by have := (hy i).2; linarith) h
    · exact div_pos_of_neg_of_neg (by have := (hy i).1; linarith) (lt_of_le_of_ne (le_of_not_gt h) hvi)
  obtain ⟨j, hj, hmin⟩ := s.exists_min_image bound hs
  refine ⟨bound j, hbpos j hj, ?_, j, ?_⟩
  · intro i
    by_cases hi : v i = 0
    · simp only [hi, mul_zero, add_zero]
      exact ⟨(hy i).1.le, (hy i).2.le⟩
    have hji := hmin i (by simp [s, hi])
    have ht := (hbpos j hj).le
    by_cases hvi : 0 < v i
    · have hbound : bound j * v i ≤ 1-y i := (le_div_iff₀ hvi).mp (by simpa [bound, hvi] using hji)
      constructor
      · nlinarith [(hy i).1, mul_nonneg ht hvi.le]
      · linarith
    · have hneg : v i < 0 := lt_of_le_of_ne (le_of_not_gt hvi) hi
      have hbound : -y i ≤ bound j * v i := (le_div_iff_of_neg hneg).mp (by simpa [bound, hvi] using hji)
      constructor
      · linarith
      · nlinarith [(hy i).2, mul_nonpos_of_nonneg_of_nonpos ht hneg.le]
  · have hjv : v j ≠ 0 := (mem_filter.mp hj).2
    dsimp [bound]
    split_ifs with h
    · right
      rw [div_mul_cancel₀ _ hjv]
      ring
    · left
      rw [div_mul_cancel₀ _ hjv]
      ring

noncomputable def fractionalIndices {ι : Type*} [Fintype ι] (y : ι → ℝ) : Finset ι :=
  @Finset.filter ι (fun i => 0 < y i ∧ y i < 1) (Classical.decPred _) univ

lemma cube_reduce {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : κ → ι → ℝ) (y : ι → ℝ) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1)
    (hcard : Fintype.card κ < (fractionalIndices y).card) :
    ∃ z : ι → ℝ, (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧
      (∀ p, ∑ i, M p i * z i = ∑ i, M p i * y i) ∧
      (∑ i, z i) ≤ ∑ i, y i ∧ (fractionalIndices z).card < (fractionalIndices y).card := by
  classical
  let F := fractionalIndices y
  have hF (i : ι) : i ∈ F ↔ 0 < y i ∧ y i < 1 := by simp [F, fractionalIndices]
  obtain ⟨v, hvrow, hvne, hvcost⟩ := kernel_direction (fun p (i : F) => M p i.val)
    (by simpa only [Fintype.card_coe] using hcard)
  obtain ⟨t, ht, hcube, j, hj⟩ := cube_step (fun i : F => y i.val) v
    (fun i => (hF i.val).mp i.property) hvne
  let v₀ : ι → ℝ := fun i => if h : i ∈ F then v ⟨i,h⟩ else 0
  let z : ι → ℝ := fun i => y i + t * v₀ i
  have hsum (c : ι → ℝ) : (∑ i, c i * v₀ i) = ∑ i : F, c i.val * v i := by
    simp only [v₀, mul_dite, mul_zero]
    exact (sum_attach_eq_sum_dite F (fun i => c i.val * v i)).symm
  have hrow : ∀ p, ∑ i, M p i * v₀ i = 0 := fun p => (hsum (M p)).trans (hvrow p)
  have hcost : ∑ i, v₀ i ≤ 0 := by
    have hh := hsum (fun _ => 1)
    simp only [one_mul] at hh
    exact hh ▸ hvcost
  have hzcube : ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
    intro i
    by_cases hi : i ∈ F
    · simpa only [z, v₀, dif_pos hi] using hcube ⟨i,hi⟩
    · simpa only [z, v₀, dif_neg hi, mul_zero, add_zero] using hy i
  have hsub : fractionalIndices z ⊆ F := by
    intro i hi
    by_contra hn
    have hz : z i = y i := by simp [z, v₀, hn]
    have hzi : 0 < z i ∧ z i < 1 := by simpa [fractionalIndices] using hi
    exact hn ((hF i).mpr (hz ▸ hzi))
  have hjnot : j.val ∉ fractionalIndices z := by
    intro hjmem
    have hzj : 0 < y j.val + t * v j ∧ y j.val + t * v j < 1 := by
      simpa [fractionalIndices, z, v₀, j.property] using hjmem
    rcases hj with hj | hj <;> linarith
  refine ⟨z, hzcube, ?_, ?_, ?_⟩
  · intro p
    calc
      (∑ i, M p i * z i) = (∑ i, M p i * y i) + t * ∑ i, M p i * v₀ i := by
        simp only [z, mul_add, sum_add_distrib, mul_sum]
        congr 1
        apply sum_congr rfl
        intro i hi
        ring
      _ = ∑ i, M p i * y i := by rw [hrow, mul_zero, add_zero]
  · dsimp only [z]
    rw [sum_add_distrib, ← mul_sum]
    nlinarith
  · apply card_lt_card
    exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hjnot (h.symm ▸ j.property)⟩

lemma cube_round {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : κ → ι → ℝ) (y : ι → ℝ) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) :
    ∃ z : ι → ℝ, (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧
      (∀ p, ∑ i, M p i * z i = ∑ i, M p i * y i) ∧
      (∑ i, z i) ≤ ∑ i, y i ∧ (fractionalIndices z).card ≤ Fintype.card κ := by
  classical
  generalize hn : (fractionalIndices y).card = n
  induction n using Nat.strong_induction_on generalizing y with
  | h n ih =>
    by_cases hsmall : (fractionalIndices y).card ≤ Fintype.card κ
    · exact ⟨y, hy, fun _ => rfl, le_rfl, hsmall⟩
    · obtain ⟨z, hz, hrow, hcost, hlt⟩ := cube_reduce M y hy (lt_of_not_ge hsmall)
      obtain ⟨w, hw, hwrow, hwcost, hwcard⟩ := ih (fractionalIndices z).card (by omega) z hz rfl
      exact ⟨w, hw, fun p => (hwrow p).trans (hrow p), hwcost.trans hcost, hwcard⟩

lemma cover_divisibility (D : Problem) (B : Finset ℕ) (hB : B ⊆ D.interval)
    (hval : ∀ p ∈ D.primes, demand D p ≤ ∑ b ∈ B, (b.factorization p : ℝ)) : Covers D B := by
  refine ⟨hB, ?_⟩
  have hA0 : ∀ a ∈ D.A, a ≠ 0 := by intro a ha; have := D.two_le a ha; omega
  have hB0 : ∀ b ∈ B, b ≠ 0 := by
    intro b hb
    have h := (mem_Icc.mp (hB hb)).1
    omega
  apply (Nat.factorization_le_iff_dvd (prod_ne_zero_iff.mpr hA0) (prod_ne_zero_iff.mpr hB0)).mp
  intro p
  by_cases hp : p ∈ D.primes
  · have h := hval p hp
    unfold demand at h
    rw [Nat.factorization_prod_apply hA0, Nat.factorization_prod_apply hB0]
    exact_mod_cast h
  · have hzero : D.product.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    change D.product.factorization p ≤ _
    rw [hzero]
    exact Nat.zero_le _

lemma round_cover (D : Problem) (y : ℕ → ℝ) (hy : FractionalCover D y) :
    Covers D (roundedSet D y) := by
  classical
  apply cover_divisibility D _ (filter_subset _ _)
  intro p hp
  apply (hy.2 p hp).trans
  rw [sum_filter]
  apply sum_le_sum
  intro b hb
  by_cases hpos : 0 < y b
  · simp only [if_pos hpos]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) (hy.1 b hb).2
  · simp only [if_neg hpos]
    have hy0 : y b = 0 := le_antisymm (le_of_not_gt hpos) (hy.1 b hb).1
    rw [hy0, mul_zero]

lemma rounded_card_bound (D : Problem) (y : ℕ → ℝ) (hy : FractionalCover D y) :
    ((roundedSet D y).card : ℝ) ≤ coverCost D y + fractionalCount D y := by
  classical
  unfold roundedSet fractionalCount coverCost
  simp only [← sum_boole, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro b hb
  have hh := hy.1 b hb
  split_ifs <;> simp_all <;> linarith

lemma ones_cover (D : Problem) : FractionalCover D (fun _ => 1) := by
  refine ⟨fun _ _ => ⟨by norm_num, le_rfl⟩, ?_⟩
  intro p hp
  have hA0 : ∀ a ∈ D.A, a ≠ 0 := by intro a ha; have := D.two_le a ha; omega
  have hI0 : ∀ b ∈ D.interval, b ≠ 0 := by intro b hb; have := (mem_Icc.mp hb).1; omega
  have hd := (Nat.factorization_le_iff_dvd (prod_ne_zero_iff.mpr hA0) (prod_ne_zero_iff.mpr hI0)).mpr
    (whole_interval D).2 p
  rw [Nat.factorization_prod_apply hA0, Nat.factorization_prod_apply hI0] at hd
  simp only [demand, mul_one]
  exact_mod_cast hd

lemma cover_rounding (D : Problem) (y : ℕ → ℝ) (hy : FractionalCover D y) :
    ∃ B : Finset ℕ, Covers D B ∧ (B.card : ℝ) ≤ coverCost D y + D.primes.card := by
  classical
  obtain ⟨z, hz, hrow, hcost, hcount⟩ := cube_round
    (fun (p : D.primes) (b : D.interval) => (b.val.factorization p.val : ℝ))
    (fun b : D.interval => y b.val) (fun b => hy.1 b.val b.property)
  let z₀ : ℕ → ℝ := fun b => if h : b ∈ D.interval then z ⟨b,h⟩ else 0
  have hz₀ (b : D.interval) : z₀ b.val = z b := by simp [z₀, b.property]
  have hfeas : FractionalCover D z₀ := by
    refine ⟨?_, ?_⟩
    · intro b hb
      simpa only [z₀, dite_eq_left hb] using hz ⟨b,hb⟩
    · intro p hp
      have hh := hrow ⟨p,hp⟩
      have heq : (∑ b ∈ D.interval, (b.factorization p : ℝ) * z₀ b) =
          ∑ b ∈ D.interval, (b.factorization p : ℝ) * y b := by
        rw [← sum_coe_sort D.interval (fun b => (b.factorization p : ℝ) * z₀ b),
          ← sum_coe_sort D.interval (fun b => (b.factorization p : ℝ) * y b)]
        simpa only [hz₀] using hh
      rw [heq]
      exact hy.2 p hp
  have hcost₀ : coverCost D z₀ ≤ coverCost D y := by
    unfold coverCost
    rw [← sum_coe_sort D.interval z₀, ← sum_coe_sort D.interval y]
    simpa only [hz₀] using hcost
  have hcount₀ : fractionalCount D z₀ ≤ D.primes.card := by
    have heq : fractionalCount D z₀ = (fractionalIndices z).card := by
      have himage : (fractionalIndices z).image Subtype.val =
          D.interval.filter (fun b => 0 < z₀ b ∧ z₀ b < 1) := by
        ext b
        simp only [mem_image, fractionalIndices, mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨i, hi, rfl⟩
          exact ⟨i.property, by simpa only [hz₀] using hi⟩
        · rintro ⟨hb, hfrac⟩
          exact ⟨⟨b,hb⟩, by simpa only [z₀, dite_eq_left hb] using hfrac, rfl⟩
      unfold fractionalCount
      rw [← himage, card_image_of_injective _ Subtype.val_injective]
    simpa only [heq, Fintype.card_coe] using hcount
  refine ⟨roundedSet D z₀, round_cover D z₀ hfeas, ?_⟩
  have h := rounded_card_bound D z₀ hfeas
  have hn : (fractionalCount D z₀ : ℝ) ≤ D.primes.card := by exact_mod_cast hcount₀
  linarith

/-- Exact restatement of the rounding card. -/
theorem rounding (D : Problem) :
    ∃ B : Finset ℕ, Covers D B ∧ (B.card : ℝ) ≤ fractionalValue D + D.primes.card := by
  classical
  let candidates := D.interval.powerset.filter (fun B => D.product ∣ ∏ b ∈ B, b)
  have hcand : ∀ B, B ∈ candidates ↔ Covers D B := by
    intro B
    simp [candidates, Covers]
  have hne : candidates.Nonempty := ⟨D.interval, (hcand _).mpr (whole_interval D)⟩
  obtain ⟨B, hB, hmin⟩ := candidates.exists_min_image Finset.card hne
  refine ⟨B, (hcand B).mp hB, ?_⟩
  have hlow : (B.card : ℝ) - D.primes.card ≤ fractionalValue D := by
    apply le_csInf
    · exact ⟨coverCost D (fun _ => 1), ⟨fun _ => 1, ones_cover D, rfl⟩⟩
    · intro t ht
      obtain ⟨y, hy, rfl⟩ := ht
      obtain ⟨C, hC, hbound⟩ := cover_rounding D y hy
      have hcard : B.card ≤ C.card := hmin C ((hcand C).mpr hC)
      have hcardR : (B.card : ℝ) ≤ C.card := by exact_mod_cast hcard
      linarith
  linarith

#print axioms kernel_direction
#print axioms cube_step
#print axioms cube_reduce
#print axioms cube_round
#print axioms cover_rounding
#print axioms rounding
end Erdos708Chain.Proofs
