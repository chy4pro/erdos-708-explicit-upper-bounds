import Erdos708.H97.Proofs.FastRecurrence
import Mathlib.Data.Nat.Digits.Defs
open Finset BigOperators
namespace Erdos708H97.Proofs
set_option maxHeartbeats 2000000

lemma pack_zip (b : ℕ) (xs ys : List ℕ) (hl : xs.length=ys.length) :
    Nat.ofDigits b (List.zipWith (·+·) xs ys) = Nat.ofDigits b xs+Nat.ofDigits b ys := by
  induction xs generalizing ys with
  | nil => have hy : ys=[] := List.length_eq_zero_iff.mp (by simpa using hl.symm); simp [hy]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at hl
      simp only [List.zipWith_cons_cons,Nat.ofDigits_cons,ih ys hl]
      ring

lemma pack_take_mod (b k : ℕ) (xs : List ℕ) :
    Nat.ofDigits b (xs.take k) % b^k = Nat.ofDigits b xs % b^k := by
  by_cases hk : k≤xs.length
  · have hh := Nat.ofDigits_append (b:=b) (l1:=xs.take k) (l2:=xs.drop k)
    rw [List.take_append_drop,List.length_take,min_eq_left hk] at hh
    rw [hh,Nat.add_mod,Nat.mul_mod_right,Nat.add_zero,Nat.mod_mod]
  · rw [List.take_of_length_le (by omega)]

lemma pack_fast_mod (b : ℕ) (es row : List ℕ) :
    Nat.ofDigits b (rowStepFastList es row) % b^row.length =
      (Nat.ofDigits b row*(1+(es.map (fun e => b^e)).sum)) % b^row.length := by
  induction es with
  | nil => simp [rowStepFastList]
  | cons e es ih =>
    rw [rowStepFastList,pack_zip _ _ _ (by simp [rowStepFastList_length]),Nat.add_mod,ih,pack_take_mod,
      Nat.ofDigits_append,Nat.ofDigits_replicate_zero,List.length_replicate,zero_add]
    rw [← Nat.add_mod]
    congr 1
    simp only [List.map_cons,List.sum_cons]
    ring

lemma row_get_le (row : List ℕ) (R s : ℕ) (hr : ∀ v∈row, v≤R) : row[s]?.getD 0 ≤ R := by
  by_cases hs : s<row.length
  · simpa [List.getElem?_eq_getElem hs] using hr row[s] (List.getElem_mem hs)
  · simp [List.getElem?_eq_none (by omega : row.length≤s)]

lemma fast_digit_bound (es row : List ℕ) (R : ℕ) (hr : ∀ v∈row, v≤R) :
    ∀ v∈rowStepFastList es row, v≤(es.length+1)*R := by
  intro v hv
  obtain ⟨s,hs,rfl⟩ := List.mem_iff_getElem.mp hv
  have hs' : s<row.length := by simpa [rowStepFastList_length] using hs
  have he := rowStepFastList_get es row s hs'
  rw [List.getElem?_eq_getElem hs,Option.getD_some] at he
  rw [he]
  have hsum : (es.map (fun e => if e≤s then row[s-e]?.getD 0 else 0)).sum ≤ es.length*R := by
    clear hs hv he
    induction es with
    | nil => simp
    | cons e es ih =>
      have hh : (if e≤s then row[s-e]?.getD 0 else 0) ≤ R := by split_ifs; exact row_get_le row R _ hr; omega
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  have hh := row_get_le row R s hr
  nlinarith

/-- Exact radix packing checks a whole convolution with one integer multiplication.
The explicit digit bound prevents carries between coefficients. -/
lemma packed_row_certificate (es : List ℕ) (E : Finset ℕ) (cap b R code : ℕ)
    (row next : List ℕ) (hnd : es.Nodup) (hE : es.toFinset=E)
    (hb : 1<b) (hsmall : (es.length+1)*R<b)
    (hr : ∀ v∈row, v≤R) (hn : ∀ v∈next, v<b)
    (hlen : row.length=cap+1) (hnlen : next.length=cap+1)
    (hc : code=1+(es.map (fun e=>b^e)).sum)
    (hp : Nat.ofDigits b next = (Nat.ofDigits b row*code) % b^(cap+1)) :
    next = rowStep E cap row := by
  have hfast : ∀ v∈rowStepFastList es row, v<b := fun v hv => (fast_digit_bound es row R hr v hv).trans_lt hsmall
  have hfastcode := Nat.ofDigits_lt_base_pow_length hb hfast
  have he := pack_fast_mod b es row
  rw [rowStepFastList_length,hlen] at hfastcode
  rw [hlen,← hc,Nat.mod_eq_of_lt hfastcode] at he
  have heq : next=rowStepFastList es row := Nat.ofDigits_inj_of_len_eq hb
    (by simp [rowStepFastList_length,hlen,hnlen]) hn hfast (hp.trans he.symm)
  exact heq.trans (rowStepFastList_eq es E cap row hnd hE hlen)

#print axioms packed_row_certificate
end Erdos708H97.Proofs
