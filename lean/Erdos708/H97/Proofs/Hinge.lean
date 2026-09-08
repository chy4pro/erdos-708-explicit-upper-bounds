import Erdos708.H97.Proofs.Closing
import Erdos708.H97.Proofs.Lemma7
import Erdos708.H97.Proofs.Lemma8
namespace Erdos708H97
 theorem hinge97 : ∀ (A : AtomSystem) (m x : ℕ),
    hingeSum (S A) (97/10) 0 m ≤ hingeSum (S A) 1 x m :=
  Proofs.hinge97_of_bounds Proofs.finite_total_bound
    Proofs.tail_summable_and_bound.1
    (Proofs.tail_summable_and_bound.2.trans_lt Proofs.tail_scalar_bound)
#print axioms hinge97
end Erdos708H97
