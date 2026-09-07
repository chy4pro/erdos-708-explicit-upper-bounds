import Erdos708.H17.Proofs.CoefficientRecurrence
open Finset BigOperators
namespace Erdos708H17.Proofs
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024

def epsilonQ (h : ℕ) : ℚ :=
  if h=0 then (65536/65535:ℚ)*(1025/1024:ℚ)^4/(2*Nat.factorial 4)
  else (65536/65535:ℚ)*(2^h:ℚ)^(momentOrder h-1)*(1025/1024:ℚ)^(momentOrder h)/Nat.factorial (momentOrder h)
def ratioQ (h N c : ℕ) : ℚ :=
  (c:ℚ)*max (1-max 0 (((N:ℚ)-2^h-1)/2^h)/(35/16)) 0 /
    max (1/2^h) (((N:ℚ)-2^h)/2^h)
def capQ (h : ℕ) : ℚ :=
  match h with
  | 0 => 51/100
  | 1 => 6/25
  | 2 => 3/100
  | 3 => 1/250
  | 4 => 1/2000
  | 5 => 1/16000
  | _ => 1/100000
end Erdos708H17.Proofs
