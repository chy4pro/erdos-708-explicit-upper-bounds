import Erdos708.H97.Proofs.CoefficientRecurrence
open Finset BigOperators
namespace Erdos708H97.Proofs

def rowStepFastList : List ℕ → List ℕ → List ℕ
  | [], row => row
  | e::es, row => List.zipWith (·+·) (rowStepFastList es row) ((List.replicate e 0++row).take row.length)

lemma rowStepFastList_length (es row : List ℕ) : (rowStepFastList es row).length = row.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [rowStepFastList,ih]

lemma shifted_get (row : List ℕ) (e s : ℕ) (hs : s<row.length) :
    (((List.replicate e 0++row).take row.length)[s]?.getD 0) =
      if e≤s then row[s-e]?.getD 0 else 0 := by
  rw [List.getElem?_take_of_lt hs]
  by_cases he : e≤s
  · rw [if_pos he,List.getElem?_append_right (by simpa using he),List.length_replicate]
  · rw [if_neg he,List.getElem?_append_left (by simpa using (lt_of_not_ge he)),List.getElem?_replicate]
    simp [show s<e by omega]

lemma zip_get (a b : List ℕ) (s : ℕ) (ha : s<a.length) (hb : s<b.length) :
    (List.zipWith (·+·) a b)[s]?.getD 0 = a[s]?.getD 0+b[s]?.getD 0 := by
  simp [List.getElem?_eq_getElem,ha,hb,show s<min a.length b.length by omega]

lemma rowStepFastList_get (es row : List ℕ) (s : ℕ) (hs : s<row.length) :
    (rowStepFastList es row)[s]?.getD 0 = row[s]?.getD 0+
      (es.map (fun e => if e≤s then row[s-e]?.getD 0 else 0)).sum := by
  induction es with
  | nil => simp [rowStepFastList]
  | cons e es ih =>
    rw [rowStepFastList,zip_get _ _ _ (by simpa [rowStepFastList_length] using hs) (by simpa using hs),
      ih,shifted_get row e s hs]
    simp only [List.map_cons,List.sum_cons]
    omega

lemma rowStepFastList_eq (es : List ℕ) (E : Finset ℕ) (cap : ℕ) (row : List ℕ)
    (hnd : es.Nodup) (hE : es.toFinset=E) (hlen : row.length=cap+1) :
    rowStepFastList es row = rowStep E cap row := by
  apply List.ext_getElem?
  intro s
  by_cases hs : s<row.length
  · have hcap : s≤cap := by omega
    have hget := rowStepFastList_get es row s hs
    rw [← List.sum_toFinset _ hnd,hE] at hget
    change (rowStepFastList es row)[s]?.getD 0 = _ at hget
    have he := rowStep_get E cap s hcap row
    have hfast : s<(rowStepFastList es row).length := by simpa [rowStepFastList_length] using hs
    have hslow : s<(rowStep E cap row).length := by simpa [rowStep,hlen] using hs
    rw [List.getElem?_eq_getElem hfast,List.getElem?_eq_getElem hslow]
    apply congrArg some
    simpa only [List.getElem?_eq_getElem hfast,List.getElem?_eq_getElem hslow,Option.getD_some] using hget.trans he.symm
  · rw [List.getElem?_eq_none (by simpa [rowStepFastList_length] using (le_of_not_gt hs)),
      List.getElem?_eq_none (by simpa [rowStep,hlen] using (le_of_not_gt hs))]

#print axioms rowStepFastList_eq
end Erdos708H97.Proofs
