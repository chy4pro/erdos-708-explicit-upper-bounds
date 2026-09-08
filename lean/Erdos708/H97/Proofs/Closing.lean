import Erdos708.H97.Proofs.Lemma2
import Erdos708.H97.Proofs.Lemma3
import Erdos708.H97.Proofs.Lemma9
import Erdos708.H97.Proofs.Aggregation
import Erdos708.H97.Proofs.Chernoff
open Finset BigOperators
namespace Erdos708H97.Proofs
noncomputable section

lemma pointwise_feasible (hf : finiteTotal < (187/1000:ℝ))
    (hs : Summable tailTerm) (ht : (∑' r, tailTerm r) < (3/1000:ℝ))
    (A : AtomSystem) (m : ℕ) (hH : H A m < Hstar) (n : ℕ) :
    F A m n ≤ max (S A n-1) 0 := by
  have hh := counting_reduction A m hH (coefficient_tail_bound A m hH) hs n
  have hconst : lambda*(finiteTotal+∑' r, tailTerm r) ≤ (969/1000:ℝ) := by
    norm_num [lambda]
    linarith
  have hB : B A m n ≤ S A n :=
    (Rounded.B_le_S (small A m) m n).trans (S_small_le A m n)
  calc
    _ ≤ (969/1000:ℝ)*max (B A m n-1) 0 :=
      hh.trans (mul_le_mul_of_nonneg_right hconst (le_max_right _ _))
    _ ≤ max (B A m n-1) 0 := mul_le_of_le_one_left (le_max_right _ _) (by norm_num)
    _ ≤ _ := max_le_max (sub_le_sub_right hB 1) le_rfl

lemma hinge97_of_bounds (hf : finiteTotal < (187/1000:ℝ))
    (hs : Summable tailTerm) (ht : (∑' r, tailTerm r) < (3/1000:ℝ)) :
    ∀ (A : AtomSystem) (m x : ℕ),
      hingeSum (S A) (97/10) 0 m ≤ hingeSum (S A) 1 x m := by
  intro A m x
  change L A m ≤ R A x m
  by_cases hm : m ≤ 1
  · rw [tiny_hinge_zero A m hm]
    unfold R hingeSum
    exact sum_nonneg (fun n hn => le_max_right _ _)
  have hm2 : 2 ≤ m := by omega
  by_cases hH : Hstar ≤ H A m
  · exact dense_branch A m (by omega) hH x
  have hH' := lt_of_not_ge hH
  have hdel : L A m = hingeSum (S_0 A m) (97/10) 0 m := by
    simp only [L,hingeSum,zero_add]
    apply sum_congr rfl
    intro k hk
    exact deletion_hinge A m (97/10) (by norm_num) k (by simpa only [zero_add] using hk)
  have hround := (lemma3 A m hm2).2.2.2.2.1
  have hwin := lemma9 A m hH' x
  have hLB : 0 ≤ LB A m := by
    unfold LB hingeSum
    exact sum_nonneg (fun k hk => le_max_right _ _)
  calc
    L A m = hingeSum (S_0 A m) (97/10) 0 m := hdel
    _ ≤ rho*LB A m := hround
    _ ≤ (718539/573440:ℝ)*LB A m :=
      mul_le_mul_of_nonneg_right window_margin.2.2.le hLB
    _ ≤ ∑ n ∈ Icc (x+1) (x+m), F A m n := hwin
    _ ≤ R A x m := sum_le_sum (fun n hn => pointwise_feasible hf hs ht A m hH' n)

#print axioms hinge97_of_bounds
end
end Erdos708H97.Proofs
