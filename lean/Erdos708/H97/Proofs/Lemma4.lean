import Erdos708.H97.Proofs.Certificate
open Finset BigOperators
namespace Erdos708H97
noncomputable section

theorem lemma4 (A : AtomSystem) (m : ℕ) :
    (∀ P ∈ carriers A m, 0 < P ∧ 1 < mu A m P ∧
      mu A m P ≤ 1+theta A m P ∧ 0 < theta A m P ∧ theta A m P ≤ 1 ∧
      P^3 ≤ m^2 ∧ 210 ≤ nu m P ∧
      (m : ℝ)/((P : ℝ)*(nu m P : ℝ)) < gamma) ∧
    (∑ P ∈ carriers A m, M A m P) = LB A m ∧
    (∀ P ∈ carriers A m, ∀ a ∈ Rounded.retained (small A m) m,
      P*Rounded.modulus a ≤ m) := by
  refine ⟨?_,Proofs.total_carried_mass A m,Proofs.negative_modulus_le A m⟩
  intro P hP
  exact ⟨Proofs.carrier_pos A m P hP,Proofs.carrier_mu_gt_one A m P hP,
    Proofs.carrier_mu_upper A m P hP,Proofs.theta_pos A m P,Proofs.theta_le_one A m P,
    Proofs.carrier_cube A m P hP,Proofs.carrier_nu_ge_210 A m P hP,
    Proofs.carrier_floor_ratio_strict A m P hP⟩
#print axioms lemma4
end
end Erdos708H97
