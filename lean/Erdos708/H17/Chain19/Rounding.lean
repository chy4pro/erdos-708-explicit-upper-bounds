import Erdos708.H17.ChainParts.Proofs.Dual
import Erdos708.H17.Chain19.Primes

open Finset BigOperators
namespace Erdos708H17Chain.Chain19
open Erdos708H17Chain.Proofs

lemma fractional_min (D : Problem) :
    ∃ y : ℕ → ℝ, FractionalCover D y ∧ coverCost D y = fractionalValue D := by
  classical
  let K : Set (D.interval → ℝ) := Set.Icc 0 1 ∩
    {y | ∀ p : D.primes, demand D p.val ≤ ∑ b, (b.val.factorization p.val : ℝ) * y b}
  have hclosed : IsClosed {y : D.interval → ℝ | ∀ p : D.primes,
      demand D p.val ≤ ∑ b, (b.val.factorization p.val : ℝ) * y b} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro p
    exact isClosed_le continuous_const (by fun_prop)
  have hcompact : IsCompact K := isCompact_Icc.inter_right hclosed
  have hne : K.Nonempty := by
    refine ⟨fun _ => 1, ⟨fun _ => zero_le_one, fun _ => le_rfl⟩, ?_⟩
    intro p
    rw [sum_coe_sort D.interval (fun b => (b.factorization p.val : ℝ) * 1)]
    exact (ones_cover D).2 p.val p.property
  have hcont : Continuous (fun y : D.interval → ℝ => ∑ b, y b) := by fun_prop
  obtain ⟨y, hy, hmin⟩ := hcompact.exists_isMinOn hne hcont.continuousOn
  let y₀ : ℕ → ℝ := fun b => if h : b ∈ D.interval then y ⟨b,h⟩ else 0
  have heval (b : D.interval) : y₀ b.val = y b := by simp [y₀, b.property]
  have hfeas : FractionalCover D y₀ := by
    refine ⟨fun b hb => ?_, fun p hp => ?_⟩
    · simpa only [y₀, dite_eq_left hb, Pi.zero_apply, Pi.one_apply] using And.intro (hy.1.1 ⟨b,hb⟩) (hy.1.2 ⟨b,hb⟩)
    · rw [← sum_coe_sort D.interval (fun b => (b.factorization p : ℝ) * y₀ b)]
      simpa only [heval] using hy.2 ⟨p,hp⟩
  have hcost : coverCost D y₀ = ∑ b, y b := by
    unfold coverCost
    rw [← sum_coe_sort D.interval y₀]
    simp only [heval]
  refine ⟨y₀, hfeas, le_antisymm ?_ ?_⟩
  · apply le_csInf (show ∃ t, ∃ v : ℕ → ℝ, FractionalCover D v ∧ coverCost D v = t from
      ⟨coverCost D y₀, y₀, hfeas, rfl⟩)
    rintro t ⟨v, hv, rfl⟩
    have hvK : (fun b : D.interval => v b.val) ∈ K := by
      refine ⟨⟨fun b => (hv.1 b.val b.property).1, fun b => (hv.1 b.val b.property).2⟩, ?_⟩
      intro p
      rw [sum_coe_sort D.interval (fun b => (b.factorization p.val : ℝ) * v b)]
      exact hv.2 p.val p.property
    rw [hcost]
    exact (hmin hvK).trans_eq (sum_coe_sort D.interval v)
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro t ⟨v,hv,rfl⟩
      exact sum_nonneg (fun b hb => (hv.1 b hb).1)
    · exact ⟨y₀,hfeas,rfl⟩

lemma primes_card_pos (D : Problem) : 0 < D.primes.card := by
  obtain ⟨a,ha⟩ := D.nonempty
  obtain ⟨p,hp,hpa⟩ := Nat.exists_prime_and_dvd (by have := D.two_le a ha; omega : a ≠ 1)
  apply card_pos.mpr
  refine ⟨p, Nat.mem_primeFactors.mpr ⟨hp, ?_, (problem_product_pos D).ne'⟩⟩
  exact hpa.trans (dvd_prod_of_mem id ha)

lemma rounded_card_strict (D : Problem) (y : ℕ → ℝ) (hy : FractionalCover D y)
    (hc : fractionalCount D y ≤ D.primes.card) :
    ((roundedSet D y).card : ℝ) < coverCost D y + D.primes.card := by
  classical
  by_cases hF : (D.interval.filter (fun b => 0 < y b ∧ y b < 1)).Nonempty
  · have hstrict : ((roundedSet D y).card : ℝ) < coverCost D y + fractionalCount D y := by
      unfold roundedSet fractionalCount coverCost
      simp only [← sum_boole]
      rw [← sum_add_distrib]
      apply sum_lt_sum
      · intro b hb
        have hh := hy.1 b hb
        split_ifs <;> simp_all
      · obtain ⟨b,hb⟩ := hF
        obtain ⟨hb,hpos,hlt⟩ := mem_filter.mp hb
        refine ⟨b,hb,?_⟩
        simp only [ite_eq_left hpos, ite_eq_left (And.intro hpos hlt)]
        linarith
    have hcR : (fractionalCount D y : ℝ) ≤ D.primes.card := by exact_mod_cast hc
    linarith
  · have hz : fractionalCount D y = 0 := by
      exact card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hF)
    have h := rounded_card_bound D y hy
    have hp : (0 : ℝ) < D.primes.card := by exact_mod_cast primes_card_pos D
    rw [hz, Nat.cast_zero, add_zero] at h
    linarith

lemma cover_strict_rounding (D : Problem) (y : ℕ → ℝ) (hy : FractionalCover D y) :
    ∃ B : Finset ℕ, Covers D B ∧ (B.card : ℝ) < coverCost D y + D.primes.card := by
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
  have h := rounded_card_strict D z₀ hfeas hcount₀
  linarith

theorem strict_rounding (D : Problem) :
    ∃ B, Covers D B ∧ (B.card : ℝ) < fractionalValue D + D.primes.card := by
  obtain ⟨y,hy,hcost⟩ := fractional_min D
  obtain ⟨B,hB,hc⟩ := cover_strict_rounding D y hy
  exact ⟨B,hB,by simpa only [hcost] using hc⟩

#print axioms fractional_min
#print axioms strict_rounding
end Erdos708H17Chain.Chain19
