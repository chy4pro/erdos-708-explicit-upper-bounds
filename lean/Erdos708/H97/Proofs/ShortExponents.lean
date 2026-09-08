import Erdos708.H97.Proofs.CoefficientRecurrence
open Finset
namespace Erdos708H97.Proofs

def exponentsShort (j L H : ℕ) : Finset ℕ :=
  ((range (H+1)).biUnion (fun h => (Icc 4 7).image (fun a => a*2^h))).filter (fun e => j≤e ∧ e≤L)

lemma exponentsExec_eq_short (j L H : ℕ) (hH : H≤L) (hL : L<2^(H+1)) :
    exponentsExec j L = exponentsShort j L H := by
  ext e
  simp only [exponentsExec,exponentsShort,mem_filter,mem_biUnion,mem_image,mem_range,mem_Icc]
  constructor
  · rintro ⟨⟨h,hh,a,ha,he⟩,hje,heL⟩
    have heh : h<H+1 := by
      by_contra hnot
      have hpow := Nat.pow_le_pow_right Nat.zero_lt_two (show H+1≤h by omega)
      have hmul : 2^h ≤ a*2^h := by have := Nat.mul_le_mul_right (2^h) (show 1≤a by omega); simpa using this
      omega
    exact ⟨⟨h,heh,a,ha,he⟩,hje,heL⟩
  · rintro ⟨⟨h,hh,a,ha,he⟩,hje,heL⟩
    exact ⟨⟨h,by omega,a,ha,he⟩,hje,heL⟩

#print axioms exponentsExec_eq_short
end Erdos708H97.Proofs
