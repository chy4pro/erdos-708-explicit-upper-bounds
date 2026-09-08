import Erdos708.H97.Proofs.ScalarHinge
open Finset BigOperators
namespace Erdos708H97
noncomputable section

theorem lemma1 :
    (∀ (A : AtomSystem) (N r : ℕ),
      (∑ n ∈ Icc 1 N, esymm (Rounded.primes A) (fun p => component A p n) r) ≤
        (N : ℝ)*mean A^r/(Nat.factorial r : ℝ)) ∧
    (∀ A G : AtomSystem, (∀ n : ℕ, S A n ≤ S G n) → mean A ≤ mean G) ∧
    (∀ (s : Finset ℕ) (u : ℕ → ℝ) (a : ℝ) (r : ℕ),
      (∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1) → 2 ≤ r → (r : ℝ)-1 ≤ a →
      max (∑ i ∈ s, u i-a) 0 ≤ hingeMajorant a r * esymm s u r) := by
  exact ⟨Proofs.atom_moment,Proofs.mean_mono,fun s u a r hu hr ha => Proofs.optimized_hinge s u hu a r hr ha⟩
#print axioms lemma1
end
end Erdos708H97
