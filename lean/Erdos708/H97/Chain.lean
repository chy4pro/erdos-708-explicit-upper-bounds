import Erdos708.H97.Proofs.Hinge
import Erdos708.H97.Proofs.WeightTransfer
import Erdos708.H17.Chain19.Results
open Finset BigOperators
namespace Erdos708H97

lemma weighted_hinge97
    (hh : ∀ (A : AtomSystem) (m x : ℕ),
      hingeSum (S A) (97/10) 0 m ≤ hingeSum (S A) 1 x m) :
    ∀ (z : Erdos708H17Chain.Weight) (m : ℕ), 1 ≤ m → ∀ x : ℕ,
      Erdos708H17Chain.hingeSum (Erdos708H17Chain.w z) (97/10) 0 m ≤
      Erdos708H17Chain.hingeSum (Erdos708H17Chain.w z) 1 x m := by
  intro z m hm x
  apply Erdos708H97.Proofs.capped_to_weight
  apply Erdos708H97.Proofs.atoms_to_capped
  have ha := hh (Erdos708H17.toCore (Erdos708H17Chain.Proofs.ofWeight z m)) m x
  simpa only [hingeSum,Erdos708H17.toCore_value,Erdos708H17Chain.hingeSum] using ha

theorem g_le_12n :
    ∀ (n : ℕ) (hn : 1 ≤ n), ∀ (A : Finset ℕ) (hA : A.card = n)
      (h2 : ∀ a ∈ A, 2 ≤ a) (x : ℕ),
      ∃ B ⊆ Finset.Icc (x+1) (x + A.max' (Finset.card_pos.mp (by omega))),
        B.card ≤ 12*n ∧ (∏ a ∈ A, a) ∣ (∏ b ∈ B, b) :=
  Erdos708H17Chain.Chain19.g_le_12n_of_hinge (weighted_hinge97 hinge97)

#print axioms hinge97
#print axioms weighted_hinge97
#print axioms g_le_12n
end Erdos708H97
