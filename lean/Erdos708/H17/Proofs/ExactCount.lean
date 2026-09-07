import Erdos708.H17.Proofs.Certificate
import Mathlib.Algebra.Polynomial.BigOperators
open Finset BigOperators Polynomial
open scoped NNReal
namespace Erdos708H17
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Rounded
lemma carrier_height_injective (A : AtomSystem) (m p : ℕ) :
    Set.InjOn (levelHeight A) {a | a ∈ retained A m ∧ a.1 = p} := by
  intro a ha b hb hab
  have ha' := (mem_filter.mp (mem_filter.mp ha.1).1).2
  have hb' := (mem_filter.mp (mem_filter.mp hb.1).1).2
  apply Prod.ext (ha.2.trans hb.2.symm)
  exact le_antisymm
    (ha'.2 b (rounding_retained_mem_atoms A m hb.1) (hb.2.trans ha.2.symm) hb'.1 hab.symm)
    (hb'.2 a (rounding_retained_mem_atoms A m ha.1) (ha.2.trans hb.2.symm) ha'.1 hab)

lemma dyadic_ratio (h k : ℕ) (hkh : k ≤ h) :
    (2 : ℝ)⁻¹ ^ k / (2 : ℝ)⁻¹ ^ h = (2 : ℝ) ^ (h - k) := by
  rw [inv_pow, inv_pow, div_inv_eq_mul, mul_comm]
  exact (pow_sub₀ (2 : ℝ) (by norm_num) hkh).symm


end Rounded
namespace Proofs
def selectedAt (s : Finset (ℕ × ℕ)) (p : ℕ) : Option (ℕ × ℕ) :=
  if (s.filter (fun a => a.1 = p)).Nonempty then
    some (p, (s.filter (fun a => a.1 = p)).sup Prod.snd) else none

lemma selectedAt_some_iff (s : Finset (ℕ × ℕ))
    (hinj : Set.InjOn Prod.fst (s : Set (ℕ × ℕ))) (p : ℕ) (b : ℕ × ℕ) :
    selectedAt s p = some b ↔ b ∈ s ∧ b.1 = p := by
  classical
  by_cases ht : (s.filter (fun a => a.1 = p)).Nonempty
  · obtain ⟨a, ha⟩ := ht
    have hap := (mem_filter.mp ha).2
    have has := (mem_filter.mp ha).1
    have hf : s.filter (fun a => a.1 = p) = {a} := by
      ext c
      constructor
      · intro hc
        exact mem_singleton.mpr (hinj (mem_filter.mp hc).1 has ((mem_filter.mp hc).2.trans hap.symm))
      · intro hc
        obtain rfl := mem_singleton.mp hc
        exact ha
    have hsel : selectedAt s p = some a := by
      rw [selectedAt, hf]
      simp only [singleton_nonempty, if_pos, sup_singleton]
      rw [← hap]
    constructor
    · intro hb
      have hab : a = b := Option.some.inj (hsel.symm.trans hb)
      simpa only [hab] using And.intro has hap
    · rintro ⟨hb, hbp⟩
      have hba : b = a := hinj hb has (hbp.trans hap.symm)
      simpa only [hba] using hsel
  · rw [selectedAt, if_neg ht]
    constructor
    · intro h
      cases h
    · rintro ⟨hb, hbp⟩
      exact (ht ⟨b, mem_filter.mpr ⟨hb, hbp⟩⟩).elim

lemma selectedAt_sum (P : Finset ℕ) (s : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℕ)
    (hinj : Set.InjOn Prod.fst (s : Set (ℕ × ℕ))) (hs : ∀ a ∈ s, a.1 ∈ P) :
    (∑ p ∈ P, (selectedAt s p).elim 0 w) = ∑ a ∈ s, w a := by
  classical
  rw [← sum_fiberwise_of_maps_to hs w]
  apply sum_congr rfl
  intro p hp
  by_cases ht : (s.filter (fun a => a.1 = p)).Nonempty
  · obtain ⟨a, ha⟩ := ht
    have has := (mem_filter.mp ha).1
    have hap := (mem_filter.mp ha).2
    have hf : s.filter (fun a => a.1 = p) = {a} := by
      ext b
      constructor
      · intro hb
        exact mem_singleton.mpr (hinj (mem_filter.mp hb).1 has ((mem_filter.mp hb).2.trans hap.symm))
      · intro hb
        obtain rfl := mem_singleton.mp hb
        exact ha
    rw [(selectedAt_some_iff s hinj p a).mpr ⟨has, hap⟩, hf]
    simp
  · have hf := not_nonempty_iff_eq_empty.mp ht
    rw [selectedAt, if_neg ht, hf]
    simp


def levelChoices (h : ℕ) : Finset (Option ℕ) := insert none ((range (h+1)).image some)
def choiceDegree (o : Option ℕ) : ℕ := o.elim 0 (fun j => 2^j)

lemma choice_polynomial (h : ℕ) :
    (∑ o ∈ levelChoices h, (X : Polynomial ℕ)^(choiceDegree o)) = countingPolynomial h := by
  rw [levelChoices, sum_insert (by simp), sum_image]
  · simp [choiceDegree, countingPolynomial]
  · intro a ha b hb hab
    exact Option.some.inj hab

lemma family_count {δ : Type*} [DecidableEq δ] (D : Finset δ) (Q : Finset ℕ) (h : ℕ)
    (enc : δ → ∀ p ∈ Q, Option ℕ)
    (hinj : Set.InjOn enc (D : Set δ))
    (henc : ∀ d ∈ D, enc d ∈ Q.pi (fun _ => levelChoices h))
    (hdegree : ∀ d ∈ D, (∑ p ∈ Q.attach, choiceDegree (enc d p.val p.property)) = 2^h+1) :
    D.card ≤ carrierCount h Q.card := by
  classical
  let w := fun f : ∀ p ∈ Q, Option ℕ =>
    ((∏ p ∈ Q.attach, (X : Polynomial ℕ)^choiceDegree (f p.val p.property)).coeff (2^h+1))
  have hw (d : δ) (hd : d ∈ D) : w (enc d) = 1 := by
    dsimp only [w]
    rw [prod_pow_eq_pow_sum, hdegree d hd]
    simp
  have hpoly : (∑ f ∈ Q.pi (fun _ => levelChoices h),
      ∏ p ∈ Q.attach, (X : Polynomial ℕ)^choiceDegree (f p.val p.property)) =
      (countingPolynomial h)^Q.card := by
    have hp := prod_sum Q (fun _ => levelChoices h) (fun (_ : ℕ) o => (X : Polynomial ℕ)^choiceDegree o)
    calc
      _ = ∏ p ∈ Q, ∑ o ∈ levelChoices h, (X : Polynomial ℕ)^choiceDegree o := by
        convert hp.symm using 1
      _ = _ := by simp_rw [choice_polynomial]; exact prod_const _
  calc
    _ = ∑ d ∈ D, w (enc d) := by
      calc
        _ = ∑ _d ∈ D, (1:ℕ) := by simp
        _ = _ := sum_congr rfl (fun d hd => (hw d hd).symm)
    _ = ∑ f ∈ D.image enc, w f := (sum_image hinj).symm
    _ ≤ ∑ f ∈ Q.pi (fun _ => levelChoices h), w f :=
      sum_le_sum_of_subset_of_nonneg (image_subset_iff.mpr henc) (fun _ _ _ => Nat.zero_le _)
    _ = _ := by
      change (∑ f ∈ Q.pi (fun _ => levelChoices h),
        (∏ p ∈ Q.attach, (X : Polynomial ℕ)^choiceDegree (f p.val p.property)).coeff (2^h+1)) = _
      rw [← finset_sum_coeff, hpoly]
      rfl

#print axioms family_count
end Proofs
end
end Erdos708H17
