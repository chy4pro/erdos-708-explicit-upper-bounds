import Erdos708.H17.Proofs.ExactCount
open Finset BigOperators Polynomial
namespace Erdos708H17.Proofs

/-- Truncated coefficient row; convolution is the multiplication-by-f recurrence. -/
def rowBase (h : ℕ) : List ℕ := (List.range (2^h+2)).map (fun s => if s=0 then 1 else 0)
def rowStep (h : ℕ) (row : List ℕ) : List ℕ :=
  (List.range (2^h+2)).map (fun s => row[s]?.getD 0 +
    ∑ j ∈ range (h+1), if 2^j ≤ s then row[s-2^j]?.getD 0 else 0)

lemma rowBase_get (h s : ℕ) (hs : s < 2^h+2) :
    (rowBase h)[s]?.getD 0 = if s=0 then 1 else 0 := by
  simp [rowBase, List.getElem?_eq_getElem, hs]
lemma rowStep_get (h s : ℕ) (hs : s < 2^h+2) (row : List ℕ) :
    (rowStep h row)[s]?.getD 0 = row[s]?.getD 0 +
      ∑ j ∈ range (h+1), if 2^j ≤ s then row[s-2^j]?.getD 0 else 0 := by
  simp [rowStep, List.getElem?_eq_getElem, hs]

lemma coefficient_recurrence (h N s : ℕ) :
    ((countingPolynomial h)^(N+1)).coeff s = ((countingPolynomial h)^N).coeff s +
      ∑ j ∈ range (h+1), if 2^j ≤ s then ((countingPolynomial h)^N).coeff (s-2^j) else 0 := by
  classical
  rw [pow_succ]
  nth_rw 2 [countingPolynomial]
  rw [mul_add,mul_one,mul_sum,coeff_add,finsetSum_coeff]
  simp_rw [coeff_mul_X_pow']

lemma row_certificate_correct (h lim : ℕ) (rows : List (List ℕ))
    (hb : rows[0]?.getD [] = rowBase h)
    (hstep : ∀ N ∈ range lim, rows[N+1]?.getD [] = rowStep h (rows[N]?.getD [])) :
    ∀ N, N ≤ lim → ∀ s, s < 2^h+2 →
      (rows[N]?.getD [])[s]?.getD 0 = ((countingPolynomial h)^N).coeff s := by
  intro N hN
  induction N with
  | zero =>
    intro s hs
    rw [hb,rowBase_get h s hs,pow_zero]
    simp only [coeff_one,eq_comm]
  | succ N ih =>
    intro s hs
    rw [hstep N (mem_range.mpr (by omega)), rowStep_get h s hs,coefficient_recurrence,
      ih (by omega) s hs]
    congr 1
    apply sum_congr rfl
    intro j hj
    split_ifs with hj
    · exact ih (by omega) _ ((Nat.sub_le s (2^j)).trans_lt hs)
    · rfl

#print axioms row_certificate_correct
end Erdos708H17.Proofs
