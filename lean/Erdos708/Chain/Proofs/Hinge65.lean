import Erdos708.Chain.Proofs.Dense

namespace Erdos708Chain.Proofs
open Finset BigOperators

lemma atom_hinge_of_sparse_core (hsc : sparse_core_hyp) (A : AtomSystem)
    (m : ℕ) (hm : 1 ≤ m) (x : ℕ) :
    hingeSum (S A) 65 0 m ≤ hingeSum (S A) 1 x m := by
  by_cases hsmallm : m ≤ 4096
  · exact atom_hinge_small A m hsmallm x
  by_cases hdense : 17 / 16 ≤ H64 A m
  · exact dense_atoms A m hm hdense x
  have hcore := hsc (small A m) m (by omega) (lt_of_not_ge hdense) x
  have hLnon : 0 ≤ L (small A m) m := sum_nonneg (fun _ _ => le_max_right _ _)
  have hLR : L (small A m) m ≤ R (small A m) x m := by nlinarith
  have hlarge := large_atoms A m (by omega)
  have hleft : hingeSum (S A) 65 0 m ≤ L (small A m) m := by
    simp only [hingeSum, L, zero_add]
    exact sum_le_sum hlarge.2.1
  have hright : R (small A m) x m ≤ hingeSum (S A) 1 x m := by
    unfold R hingeSum
    exact sum_le_sum (fun b _ => hlarge.2.2 b)
  exact hleft.trans (hLR.trans hright)

/-- Exact restatement of the sparse-core reduction card. -/
theorem hinge_65_of_sparse_core (hsc : sparse_core_hyp) : Hinge65 := by
  intro z m hm x
  apply capped_to_weight
  apply atoms_to_capped
  exact atom_hinge_of_sparse_core hsc (ofWeight z m) m hm x

#print axioms atom_hinge_of_sparse_core
#print axioms hinge_65_of_sparse_core
end Erdos708Chain.Proofs
