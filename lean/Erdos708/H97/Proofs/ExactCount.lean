import Erdos708.H97.Proofs.ScaleGeometry
import Erdos708.H17.Proofs.ExactCount
open Finset BigOperators Polynomial
namespace Erdos708H97.Proofs
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
export Erdos708H17.Proofs (selectedAt selectedAt_some_iff selectedAt_sum)

lemma assignment_polynomial (Q E : Finset ℕ) (hE : 0 ∉ E) :
    (∑ f ∈ Q.pi (fun _ => insert 0 E),
      ∏ p ∈ Q.attach, (X : Polynomial ℕ)^(f p.val p.property)) =
      (1+∑ e ∈ E, (X : Polynomial ℕ)^e)^Q.card := by
  have hp := prod_sum Q (fun _ => insert 0 E) (fun (_ : ℕ) e => (X : Polynomial ℕ)^e)
  calc
    _ = ∏ p ∈ Q, ∑ e ∈ insert 0 E, (X : Polynomial ℕ)^e := by convert hp.symm using 1
    _ = _ := by simp only [sum_insert hE,pow_zero]; exact prod_const _

lemma family_count {δ : Type*} [DecidableEq δ] (D : Finset δ) (Q : Finset ℕ) (j L d : ℕ)
    (hj : 0 < j) (enc : δ → ∀ p ∈ Q, ℕ)
    (hinj : Set.InjOn enc (D : Set δ))
    (henc : ∀ c ∈ D, enc c ∈ Q.pi (fun _ => insert 0 (exponents j L)))
    (hdegree : ∀ c ∈ D, (∑ p ∈ Q.attach, enc c p.val p.property) = L+d)
    (huses : ∀ c ∈ D, ∃ p, ∃ hp : p ∈ Q, enc c p hp = j) :
    D.card ≤ carrierCount j L d Q.card := by
  classical
  let all := Q.pi (fun _ => insert 0 (exponents j L))
  let omitted := Q.pi (fun _ => insert 0 ((exponents j L).erase j))
  let w := fun f : ∀ p ∈ Q, ℕ =>
    ((∏ p ∈ Q.attach, (X : Polynomial ℕ)^(f p.val p.property)).coeff (L+d))
  have hsub : omitted ⊆ all := by
    intro f hf
    apply mem_pi.mpr
    intro p hp
    have hh := mem_pi.mp hf p hp
    rcases mem_insert.mp hh with hz | he
    · exact mem_insert.mpr (Or.inl hz)
    · exact mem_insert_of_mem (mem_erase.mp he).2
  have hmap : ∀ c ∈ D, enc c ∈ all \ omitted := by
    intro c hc
    refine mem_sdiff.mpr ⟨henc c hc,?_⟩
    intro ho
    obtain ⟨p,hp,he⟩ := huses c hc
    have hh := mem_pi.mp ho p hp
    rw [he] at hh
    simp only [mem_insert,mem_erase,ne_eq,not_true_eq_false,false_and,or_false] at hh
    omega
  have hw : ∀ c ∈ D, w (enc c) = 1 := by
    intro c hc
    dsimp only [w]
    rw [prod_pow_eq_pow_sum,hdegree c hc]
    simp
  have hE : 0 ∉ exponents j L := by
    intro h
    simp only [exponents,mem_filter] at h
    have hh := (mem_Icc.mp h.1).1
    omega
  have hall : (∑ f ∈ all, w f) = ((countingPolynomial j L)^Q.card).coeff (L+d) := by
    rw [← finset_sum_coeff,assignment_polynomial Q (exponents j L) hE]
    rfl
  have homit : (∑ f ∈ omitted, w f) = ((omittedPolynomial j L)^Q.card).coeff (L+d) := by
    rw [← finset_sum_coeff,assignment_polynomial Q ((exponents j L).erase j) (fun h => hE (mem_erase.mp h).2)]
    rfl
  calc
    _ = ∑ c ∈ D, w (enc c) := by
      rw [sum_congr rfl hw]
      simp
    _ = ∑ f ∈ D.image enc, w f := (sum_image hinj).symm
    _ ≤ ∑ f ∈ all \ omitted, w f := sum_le_sum_of_subset_of_nonneg (image_subset_iff.mpr hmap) (fun _ _ _ => Nat.zero_le _)
    _ = _ := by
      have hh := sum_sdiff (f := w) hsub
      rw [hall,homit] at hh
      unfold carrierCount
      omega

#print axioms family_count
end
end Erdos708H97.Proofs
