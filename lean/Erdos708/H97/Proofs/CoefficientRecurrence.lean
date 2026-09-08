import Erdos708.H97.Defs
import Mathlib.Algebra.Polynomial.BigOperators
open Finset BigOperators Polynomial
namespace Erdos708H97.Proofs

def exponentsExec (j L : ℕ) : Finset ℕ :=
  ((range (L+1)).biUnion (fun h => (Icc 4 7).image (fun a => a*2^h))).filter (fun e => j ≤ e ∧ e ≤ L)

lemma exponents_eq_exec (j L : ℕ) : exponents j L = exponentsExec j L := by
  classical
  ext e
  simp only [exponents,exponentsExec,mem_filter,mem_Icc,mem_biUnion,mem_image]
  constructor
  · rintro ⟨⟨hlo,hhi⟩,a,ha,h,hh,he⟩
    exact ⟨⟨h,hh,a,ha,he.symm⟩,hlo,hhi⟩
  · rintro ⟨⟨h,hh,a,ha,he⟩,hlo,hhi⟩
    exact ⟨⟨hlo,hhi⟩,a,ha,h,hh,he.symm⟩

noncomputable def polyFrom (E : Finset ℕ) : Polynomial ℕ := 1+∑ e ∈ E, X^e
def rowBase (cap : ℕ) : List ℕ := (List.range (cap+1)).map (fun s => if s=0 then 1 else 0)
def rowStep (E : Finset ℕ) (cap : ℕ) (row : List ℕ) : List ℕ :=
  (List.range (cap+1)).map (fun s => row[s]?.getD 0+
    ∑ e ∈ E, if e ≤ s then row[s-e]?.getD 0 else 0)

lemma rowBase_get (cap s : ℕ) (hs : s ≤ cap) :
    (rowBase cap)[s]?.getD 0 = if s=0 then 1 else 0 := by
  simp [rowBase,List.getElem?_eq_getElem,show s < cap+1 by omega]
lemma rowStep_get (E : Finset ℕ) (cap s : ℕ) (hs : s ≤ cap) (row : List ℕ) :
    (rowStep E cap row)[s]?.getD 0 = row[s]?.getD 0+
      ∑ e ∈ E, if e ≤ s then row[s-e]?.getD 0 else 0 := by
  simp [rowStep,List.getElem?_eq_getElem,show s < cap+1 by omega]

lemma coefficient_recurrence (E : Finset ℕ) (N s : ℕ) :
    ((polyFrom E)^(N+1)).coeff s = ((polyFrom E)^N).coeff s+
      ∑ e ∈ E, if e ≤ s then ((polyFrom E)^N).coeff (s-e) else 0 := by
  classical
  rw [pow_succ]
  nth_rw 2 [polyFrom]
  rw [mul_add,mul_one,mul_sum,coeff_add,finsetSum_coeff]
  simp_rw [coeff_mul_X_pow']

lemma row_certificate_correct (E : Finset ℕ) (cap lim : ℕ) (rows : List (List ℕ))
    (hb : rows[0]?.getD [] = rowBase cap)
    (hstep : ∀ N ∈ range lim, rows[N+1]?.getD [] = rowStep E cap (rows[N]?.getD [])) :
    ∀ N, N ≤ lim → ∀ s, s ≤ cap →
      (rows[N]?.getD [])[s]?.getD 0 = ((polyFrom E)^N).coeff s := by
  intro N hN
  induction N with
  | zero =>
    intro s hs
    rw [hb,rowBase_get cap s hs,pow_zero]
    simp only [coeff_one,eq_comm]
  | succ N ih =>
    intro s hs
    rw [hstep N (mem_range.mpr (by omega)),rowStep_get E cap s hs,coefficient_recurrence,
      ih (by omega) s hs]
    congr 1
    apply sum_congr rfl
    intro e he
    split_ifs
    · exact ih (by omega) _ ((Nat.sub_le s e).trans hs)
    · rfl

lemma count_from_certificates (j L d N lim : ℕ) (fullRows omitRows : List (List ℕ))
    (hN : N ≤ lim) (hd : d ≤ j)
    (hf0 : fullRows[0]?.getD [] = rowBase (L+j))
    (hf : ∀ n ∈ range lim, fullRows[n+1]?.getD [] = rowStep (exponentsExec j L) (L+j) (fullRows[n]?.getD []))
    (ho0 : omitRows[0]?.getD [] = rowBase (L+j))
    (ho : ∀ n ∈ range lim, omitRows[n+1]?.getD [] = rowStep ((exponentsExec j L).erase j) (L+j) (omitRows[n]?.getD [])) :
    (fullRows[N]?.getD [])[L+d]?.getD 0-(omitRows[N]?.getD [])[L+d]?.getD 0 = carrierCount j L d N := by
  rw [row_certificate_correct _ _ _ fullRows hf0 hf N hN _ (by omega),
    row_certificate_correct _ _ _ omitRows ho0 ho N hN _ (by omega)]
  simp only [carrierCount,countingPolynomial,omittedPolynomial,polyFrom,exponents_eq_exec]

#print axioms row_certificate_correct
#print axioms count_from_certificates
end Erdos708H97.Proofs
