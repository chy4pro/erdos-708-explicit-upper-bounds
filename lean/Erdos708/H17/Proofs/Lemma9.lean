import Erdos708.H17.Defs
open Finset BigOperators
namespace Erdos708H17.Proofs

lemma completion (A : AtomSystem) (m x : ℕ)
    (hleft : L A m ≤ 2 * LB A m) (hdom : RB A m x ≤ R A x m)
    (hpoint : ∀ n, F A m n ≤ (4/5 : ℝ) * max (B A m n - 1) 0)
    (hwindow : (62248/30583 : ℝ) * LB A m ≤ ∑ n ∈ Icc (x+1) (x+m), F A m n) :
    L A m ≤ (30583/38905 : ℝ) * RB A m x ∧ L A m ≤ R A x m := by
  have hsum : (∑ n ∈ Icc (x+1) (x+m), F A m n) ≤ (4/5:ℝ)*RB A m x := by
    unfold RB hingeSum
    rw [mul_sum]
    exact sum_le_sum (fun n _ => hpoint n)
  have hRB : 0 ≤ RB A m x := by unfold RB hingeSum; exact sum_nonneg (fun _ _ => le_max_right _ _)
  constructor <;> nlinarith

#print axioms completion
end Erdos708H17.Proofs
