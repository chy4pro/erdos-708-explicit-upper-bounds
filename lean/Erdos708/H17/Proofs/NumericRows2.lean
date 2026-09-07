import Erdos708.H17.Proofs.NumericDefs
open Finset BigOperators
namespace Erdos708H17.Proofs
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024

def rows2 : List (List ℕ) := [
[1,0,0,0,0,0],
[1,1,1,0,1,0],
[1,2,3,2,3,2],
[1,3,6,7,9,9],
[1,4,10,16,23,28],
[1,5,15,30,50,71],
[1,6,21,50,96,156],
[1,7,28,77,168,308],
[1,8,36,112,274,560],
[1,9,45,156,423,954],
[1,10,55,210,625,1542],
[1,11,66,275,891,2387],
[1,12,78,352,1233,3564],
[1,13,91,442,1664,5161]
]

theorem rows2_valid :
    rows2[0]?.getD [] = rowBase 2 ∧
      ∀ N ∈ range (countLimit 2), rows2[N+1]?.getD [] = rowStep 2 (rows2[N]?.getD []) := by decide
#print axioms rows2_valid
end Erdos708H17.Proofs
