import Erdos708.H97.Proofs.Rounding
open Finset BigOperators
namespace Erdos708H97
noncomputable section

theorem lemma3 (A : AtomSystem) (m : ℕ) (hm : 2 ≤ m) :
    (∀ n, B A m n ≤ S_0 A m n) ∧ HB A m ≤ H A m ∧
    (∀ p n, 0 ≤ bp A m p n ∧ bp A m p n ≤ 1) ∧
    (∀ k ∈ Icc 1 m, S_0 A m k ≤ rho*B A m k+D0) ∧
    hingeSum (S_0 A m) (97/10) 0 m ≤ rho*LB A m ∧
    (∀ a ∈ Rounded.retained (small A m) m, Rounded.modulus a^3 ≤ m) := by
  refine ⟨Rounded.B_le_S (small A m) m, Rounded.HB_le_mean (small A m) m,
    fun p n => ⟨Rounded.bp_nonneg (small A m) m p n, Rounded.bp_le_one (small A m) m p n⟩,
    ?_, ?_, Rounded.retained_cube_le (small A m) m⟩
  · intro k hk
    exact Rounded.S_le_rounded (small A m) m k hm (mem_Icc.mp hk).1 (mem_Icc.mp hk).2
  · simpa only [rho, LB, hingeSum, B, Rounded.LB, S_0, zero_add] using
      Rounded.hinge_rounding (small A m) m hm
#print axioms lemma3
end
end Erdos708H97
