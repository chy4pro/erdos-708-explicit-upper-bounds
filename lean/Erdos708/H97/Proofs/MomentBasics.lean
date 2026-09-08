import Erdos708.H97.Defs
import Erdos708.H17.Proofs.Moment
import Erdos708.H17.Proofs.Lemma1
open Finset BigOperators
namespace Erdos708H97.Proofs
noncomputable section
export Erdos708H17.Proofs (atom_moment component_nonneg component_eq_zero_of_not_mem
  esymm_nonneg hinge_le_esymm average_divisor_sum)
lemma mean_mono (A G : AtomSystem) (h : ∀ n, S A n ≤ S G n) : mean A ≤ mean G := by
  classical
  let Q := ∏ a ∈ A.atoms ∪ G.atoms, a.1^a.2
  have hQ : 0 < Q := by
    apply prod_pos
    intro a ha
    rcases mem_union.mp ha with ha | ha
    · exact pow_pos (A.prime_of_mem a ha).1.pos _
    · exact pow_pos (G.prime_of_mem a ha).1.pos _
  have hdivA : ∀ a ∈ A.atoms, a.1^a.2 ∣ Q := fun a ha => dvd_prod_of_mem _ (mem_union_left _ ha)
  have hdivG : ∀ a ∈ G.atoms, a.1^a.2 ∣ Q := fun a ha => dvd_prod_of_mem _ (mem_union_right _ ha)
  have hs : (∑ n ∈ Icc 1 Q, S A n) ≤ ∑ n ∈ Icc 1 Q, S G n :=
    sum_le_sum (fun n hn => h n)
  unfold S at hs
  rw [average_divisor_sum _ _ _ Q hQ hdivA, average_divisor_sum _ _ _ Q hQ hdivG] at hs
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hh := (_root_.mul_le_mul_iff_right₀ hQr).mp hs
  simpa only [mean, Nat.cast_pow] using hh

#print axioms mean_mono
end
end Erdos708H97.Proofs
