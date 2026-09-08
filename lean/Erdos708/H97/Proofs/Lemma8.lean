import Erdos708.H97.Proofs.TailSum
namespace Erdos708H97
 theorem lemma8 :
    (∀ (A : AtomSystem) (m : ℕ), H A m < Hstar →
      ∀ P ∈ carriers A m, coefficient A m P ≤ tailEpsilon (theta A m P)) ∧
    Summable tailTerm ∧ (∑' r, tailTerm r) ≤ tailBound ∧ tailBound < 3/1000 :=
  ⟨Proofs.coefficient_tail_bound,Proofs.tail_summable_and_bound.1,
    Proofs.tail_summable_and_bound.2,Proofs.tail_scalar_bound⟩
#print axioms lemma8
end Erdos708H97
