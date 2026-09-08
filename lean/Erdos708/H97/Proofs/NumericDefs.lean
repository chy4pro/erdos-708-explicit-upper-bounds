import Erdos708.H97.Proofs.CoefficientRecurrence
import Erdos708.H97.Proofs.CountBounds
open Finset BigOperators
namespace Erdos708H97.Proofs
noncomputable section

def ratioQ (j L d N : ℕ) : ℚ :=
  max (1-max 0 ((N:ℚ)*j/L-1-(d:ℚ)/L)/(8/3)) 0 /
    max ((d:ℚ)/L) ((N:ℚ)*j/L-1)
lemma ratioQ_cast (j L d N : ℕ) : (ratioQ j L d N : ℝ) = countRatio j L d N := by
  norm_num [ratioQ,countRatio,K,Rat.cast_max]

def rowValueQ (j L N : ℕ) (counts : List ℕ) (ep : List ℚ) : ℚ :=
  ∑ d ∈ Icc 1 j, (counts[d-1]?.getD 0:ℚ)*(ep[d-1]?.getD 0)*ratioQ j L d N

lemma numeric_scale_bound (j L : ℕ) (b : ℚ) (counts : ℕ → List ℕ) (ep : List ℚ)
    (hc : ∀ N ∈ range (countLimit j L+1), ∀ d ∈ Icc 1 j,
      (counts N)[d-1]?.getD 0 = carrierCount j L d N)
    (he : ∀ d ∈ Icc 1 j, epsilon ((j:ℝ)/L) (1+(d:ℝ)/L) ≤ (ep[d-1]?.getD 0 : ℚ))
    (hb : ∀ N ∈ range (countLimit j L+1), rowValueQ j L N (counts N) ep ≤ b) :
    AScale j L ≤ (b:ℝ) := by
  apply sup'_le
  intro N hN
  calc
    scaleValue j L N ≤ ∑ d ∈ Icc 1 j,
        (carrierCount j L d N:ℝ)*(ep[d-1]?.getD 0 : ℚ)*countRatio j L d N := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (he d hd) (Nat.cast_nonneg _)) (countRatio_nonneg j L d N)
    _ = (rowValueQ j L N (counts N) ep : ℝ) := by
      simp only [rowValueQ,Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast,ratioQ_cast]
      apply sum_congr rfl
      intro d hd
      rw [hc N hN d hd]
    _ ≤ _ := by exact_mod_cast hb N hN

def countsFromRows (j L N : ℕ) (fullRows omitRows : List (List ℕ)) : List ℕ :=
  (List.range j).map (fun i => (fullRows[N]?.getD [])[L+(i+1)]?.getD 0-
    (omitRows[N]?.getD [])[L+(i+1)]?.getD 0)

lemma countsFromRows_correct (j L lim : ℕ) (fullRows omitRows : List (List ℕ))
    (hf0 : fullRows[0]?.getD [] = rowBase (L+j))
    (hf : ∀ n ∈ range lim, fullRows[n+1]?.getD [] = rowStep (exponentsExec j L) (L+j) (fullRows[n]?.getD []))
    (ho0 : omitRows[0]?.getD [] = rowBase (L+j))
    (ho : ∀ n ∈ range lim, omitRows[n+1]?.getD [] = rowStep ((exponentsExec j L).erase j) (L+j) (omitRows[n]?.getD [])) :
    ∀ N ∈ range (lim+1), ∀ d ∈ Icc 1 j,
      (countsFromRows j L N fullRows omitRows)[d-1]?.getD 0 = carrierCount j L d N := by
  intro N hN d hd
  have hd' := mem_Icc.mp hd
  have hdi : d-1 < j := by omega
  simp only [countsFromRows,List.getElem?_map,List.getElem?_range hdi,Option.map_some,Option.getD_some]
  rw [show d-1+1=d by omega]
  exact count_from_certificates j L d N lim fullRows omitRows (by simpa using hN) hd'.2 hf0 hf ho0 ho

#print axioms numeric_scale_bound
end
end Erdos708H97.Proofs
