import Erdos708.H97.Proofs.ScaleEstimates
import Erdos708.H97.Proofs.Certificate
open Finset BigOperators
namespace Erdos708H97.Proofs
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

def globalTerm (h : ℕ) : ℝ := if h < 29 then AScale (Rounded.scaleJ h) (Rounded.scaleL h)
  else tailAScale (Rounded.scaleJ h) (Rounded.scaleL h)
lemma globalTerm_nonneg (h : ℕ) : 0 ≤ globalTerm h := by
  unfold globalTerm
  split_ifs
  · exact AScale_nonneg _ _ (by have := (Rounded.scaleJ_bounds h).1; omega) (Rounded.scaleL_pos h)
  · exact tailAScale_nonneg _ _
lemma tailTerm_nonneg (r : ℕ) : 0 ≤ tailTerm r := sum_nonneg (fun _ _ => tailAScale_nonneg _ _)

lemma finite_prefix : (∑ h ∈ range 29, globalTerm h) = finiteTotal := by
  norm_num [globalTerm,finiteTotal,finiteGroup,sum_range_succ,sum_Icc_succ_top,
    Rounded.scaleJ,Rounded.scaleL,Rounded.scaleH]
  ring

lemma globalTerm_band (r i : ℕ) (hi : i < 4) :
    globalTerm (29+4*r+i) = tailAScale (7-i) (1024*2^r) := by
  have hn : 29+4*r+i ≠ 0 := by omega
  have hh : ¬29+4*r+i < 29 := by omega
  have hmod : (29+4*r+i-1)%4 = i := by omega
  have hdiv : (29+4*r+i-1)/4 = r+7 := by omega
  simp only [globalTerm,if_neg hh,Rounded.scaleJ,Rounded.scaleL,Rounded.scaleH,if_neg hn,hmod,hdiv]
  rw [show r+7+3 = r+10 by omega,pow_add]
  simp only [show (2 : ℕ)^10 = 1024 by norm_num,Nat.mul_comm]

lemma tail_band (r : ℕ) : (∑ i ∈ range 4, globalTerm (29+4*r+i)) = tailTerm r := by
  rw [sum_congr rfl (fun i hi => globalTerm_band r i (mem_range.mp hi))]
  norm_num [tailTerm,sum_range_succ,sum_Icc_succ_top]
  ring

lemma global_prefix (b : ℕ) : (∑ h ∈ range (29+4*b), globalTerm h) =
    finiteTotal+∑ r ∈ range b, tailTerm r := by
  induction b with
  | zero => simpa using finite_prefix
  | succ b ih =>
    rw [show 29+4*(b+1) = (29+4*b)+4 by omega,sum_range_add,tail_band,ih,sum_range_succ]
    ring

lemma finite_global_sum (s : Finset ℕ) (hs : Summable tailTerm) :
    (∑ h ∈ s, globalTerm h) ≤ finiteTotal+∑' r, tailTerm r := by
  let b := s.sup id+1
  have hsub : s ⊆ range (29+4*b) := by
    intro h hh
    have hb : h ≤ s.sup id := le_sup (f := id) hh
    apply mem_range.mpr
    dsimp only [b]
    omega
  calc
    _ ≤ ∑ h ∈ range (29+4*b), globalTerm h :=
      sum_le_sum_of_subset_of_nonneg hsub (fun h _ _ => globalTerm_nonneg h)
    _ = finiteTotal+∑ r ∈ range b, tailTerm r := global_prefix b
    _ ≤ _ := add_le_add_right (hs.sum_le_tsum _ (fun r _ => tailTerm_nonneg r)) _

lemma counting_reduction (A : AtomSystem) (m : ℕ) (hH : H A m < Hstar)
    (heps : ∀ P ∈ carriers A m, coefficient A m P ≤ tailEpsilon (theta A m P))
    (hs : Summable tailTerm) (n : ℕ) :
    F A m n ≤ lambda*(finiteTotal+∑' r, tailTerm r)*max (B A m n-1) 0 := by
  classical
  let D := (carriers A m).filter (fun P => P ∣ n)
  let heights := D.image (carrierHeight A m)
  have hsplit : F A m n = lambda*∑ h ∈ heights,
      ∑ P ∈ heightCarriers A m n h, coefficient A m P*(1-U A m P n/K) := by
    unfold F
    rw [← sum_filter]
    congr 1
    rw [← sum_fiberwise_of_maps_to (fun P hP => mem_image_of_mem (carrierHeight A m) hP)]
    apply sum_congr rfl
    intro h hh
    apply sum_congr
    · ext P
      simp only [D,heightCarriers,mem_filter]
      tauto
    · intros; rfl
  have hbound (h : ℕ) : (∑ P ∈ heightCarriers A m n h, coefficient A m P*(1-U A m P n/K)) ≤
      globalTerm h*max (B A m n-1) 0 := by
    unfold globalTerm
    split_ifs
    · exact finite_height_bound A m hH n h
    · exact tail_height_bound A m n h heps
  have hlam : 0 ≤ lambda := by norm_num [lambda]
  rw [hsplit]
  calc
    _ ≤ lambda*∑ h ∈ heights, globalTerm h*max (B A m n-1) 0 :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun h _ => hbound h)) hlam
    _ = lambda*(∑ h ∈ heights, globalTerm h)*max (B A m n-1) 0 := by rw [← sum_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (finite_global_sum heights hs) hlam) (le_max_right _ _)

#print axioms counting_reduction
end
end Erdos708H97.Proofs

namespace Erdos708H97
noncomputable section
 theorem lemma6 (A : AtomSystem) (m : ℕ) (hH : H A m < Hstar) :
    (∀ n, F A m n = ∑ D ∈ certificateSupport A m,
      signedCoefficient A m D*(if D ∣ n then 1 else 0)) ∧
    (∀ D ∈ certificateSupport A m, signedCoefficient A m D < 0 → D ≤ m) ∧
    ((∀ P ∈ carriers A m, coefficient A m P ≤ tailEpsilon (theta A m P)) →
      Summable tailTerm → ∀ n, F A m n ≤
        lambda*(finiteTotal+∑' r, tailTerm r)*max (B A m n-1) 0) := by
  exact ⟨Proofs.F_signed_expansion A m,fun D _ hD => Proofs.negative_support_le A m D hD,
    Proofs.counting_reduction A m hH⟩
#print axioms lemma6
end
end Erdos708H97
