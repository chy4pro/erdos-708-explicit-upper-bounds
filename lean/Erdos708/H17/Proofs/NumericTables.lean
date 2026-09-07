import Erdos708.H17.Proofs.NumericBounds0
import Erdos708.H17.Proofs.NumericBounds1
import Erdos708.H17.Proofs.NumericBounds2
import Erdos708.H17.Proofs.NumericBounds3
import Erdos708.H17.Proofs.NumericBounds4
import Erdos708.H17.Proofs.NumericBounds5
import Erdos708.H17.Proofs.NumericBounds6
open Finset BigOperators
namespace Erdos708H17.Proofs

def numericRows (h : ℕ) : List (List ℕ) :=
  match h with
  | 0 => rows0
  | 1 => rows1
  | 2 => rows2
  | 3 => rows3
  | 4 => rows4
  | 5 => rows5
  | _ => rows6

theorem numericRows_valid (h : ℕ) (hh : h < 7) :
    (numericRows h)[0]?.getD [] = rowBase h ∧
      ∀ N ∈ range (countLimit h), (numericRows h)[N+1]?.getD [] = rowStep h ((numericRows h)[N]?.getD []) := by
  interval_cases h
  all_goals first | exact rows0_valid | exact rows1_valid | exact rows2_valid | exact rows3_valid | exact rows4_valid | exact rows5_valid | exact rows6_valid

theorem numericRows_bound (h : ℕ) (hh : h < 7) : ∀ N ∈ range (countLimit h+1),
    24*epsilonQ h*ratioQ h N (((numericRows h)[N]?.getD [])[2^h+1]?.getD 0) < capQ h := by
  interval_cases h
  all_goals first | exact rows0_bound | exact rows1_bound | exact rows2_bound | exact rows3_bound | exact rows4_bound | exact rows5_bound | exact rows6_bound
#print axioms numericRows_valid
#print axioms numericRows_bound
end Erdos708H17.Proofs
