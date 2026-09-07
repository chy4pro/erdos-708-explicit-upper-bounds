import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic
open Finset BigOperators
open scoped NNReal
namespace Erdos708H17
noncomputable section
attribute [local instance] Classical.propDecidable
structure AtomSystem where
  atoms : Finset (ℕ × ℕ)
  weight : ℕ × ℕ → ℝ
  prime_of_mem : ∀ a ∈ atoms, Nat.Prime a.1 ∧ 1 ≤ a.2
  weight_nonneg : ∀ a ∈ atoms, 0 ≤ weight a
  perPrime_le_one : ∀ p : ℕ, ∑ a ∈ atoms.filter (fun a => a.1 = p), weight a ≤ 1

/-- `S₀(n) = Σ_{(p,j) ∈ atoms, p^j ∣ n} α(p,j)`. -/
noncomputable def S (A : AtomSystem) (n : ℕ) : ℝ :=
  ∑ a ∈ A.atoms.filter (fun a => a.1 ^ a.2 ∣ n), A.weight a

/-- The mean `H = Σ α(p,j) / p^j` of `S₀` over the integers. -/
noncomputable def mean (A : AtomSystem) : ℝ :=
  ∑ a ∈ A.atoms, A.weight a / ((a.1 : ℝ) ^ a.2)


def restrict (A : AtomSystem) (P : ℕ × ℕ → Prop) : AtomSystem := by
  classical
  exact {
    atoms := A.atoms.filter P
    weight := A.weight
    prime_of_mem := fun a ha => A.prime_of_mem a (mem_filter.mp ha).1
    weight_nonneg := fun a ha => A.weight_nonneg a (mem_filter.mp ha).1
    perPrime_le_one := fun p => le_trans (sum_le_sum_of_subset_of_nonneg
      (by intro a ha; simp_all only [mem_filter]; tauto)
      (by intro a ha _; exact A.weight_nonneg a (mem_filter.mp ha).1)) (A.perPrime_le_one p) }
def small (A : AtomSystem) (m : ℕ) : AtomSystem := restrict A (fun a => 2^16 * a.1^a.2 ≤ m)
def S_0 (A : AtomSystem) (m n : ℕ) : ℝ := S (small A m) n
def H (A : AtomSystem) (m : ℕ) : ℝ := mean (small A m)
def Hstar : ℝ := 1025 / 1024
def gamma : ℝ := 65536 / 65535
def K : ℝ := 35 / 16
def hingeSum (f : ℕ → ℝ) (c : ℝ) (x m : ℕ) : ℝ :=
  ∑ k ∈ Icc (x+1) (x+m), max (f k - c) 0
def L (A : AtomSystem) (m : ℕ) : ℝ := hingeSum (S A) 17 0 m
def R (A : AtomSystem) (x m : ℕ) : ℝ := hingeSum (S A) 1 x m
def Hinge17 : Prop := ∀ (A : AtomSystem) (m x : ℕ), L A m ≤ R A x m

namespace Rounded
/-- The finitely many primes occurring in the original atom support. -/
def primes (A : AtomSystem) : Finset ℕ := A.atoms.image Prod.fst

/-- Cumulative original weight through exponent `j` at prime `p`. -/
def cumulative (A : AtomSystem) (p j : ℕ) : ℝ :=
  ∑ a ∈ A.atoms.filter (fun a => a.1 = p ∧ a.2 ≤ j), A.weight a

/-- Least `h` with `2⁻ʰ ≤ u`. The default matters only when no such `h` exists;
first rounded levels below are restricted to positive cumulative weight. -/
def dyadicHeight (u : ℝ) : ℕ := by
  classical
  exact if h : ∃ h : ℕ, (2 : ℝ)⁻¹ ^ h ≤ u then Nat.find h else 0

def levelHeight (A : AtomSystem) (a : ℕ × ℕ) : ℕ :=
  dyadicHeight (cumulative A a.1 a.2)

/-- Nonnegative-real dyadic value, enabling finite suprema with bottom zero. -/
def levelValue (A : AtomSystem) (a : ℕ × ℕ) : ℝ≥0 :=
  (2 : ℝ≥0)⁻¹ ^ levelHeight A a

def modulus (a : ℕ × ℕ) : ℕ := a.1 ^ a.2

/-- First exponent in the original support at which a positive rounded value occurs. -/
def roundedLevels (A : AtomSystem) : Finset (ℕ × ℕ) := by
  classical
  exact A.atoms.filter (fun a => 0 < cumulative A a.1 a.2 ∧
    ∀ b ∈ A.atoms, b.1 = a.1 → 0 < cumulative A b.1 b.2 →
      levelHeight A b = levelHeight A a → a.2 ≤ b.2)

/-- The modulus-cost cutoff, with the exact integer exponent `3 / t`. -/
def retained (A : AtomSystem) (m : ℕ) : Finset (ℕ × ℕ) :=
  (roundedLevels A).filter (fun a => modulus a ^ (3 * 2 ^ levelHeight A a) ≤ m)

/-- Largest retained cumulative value at one prime that divides `n`. -/
def bpNN (A : AtomSystem) (m p n : ℕ) : ℝ≥0 :=
  ((retained A m).filter (fun a => a.1 = p ∧ modulus a ∣ n)).sup (levelValue A)

def bp (A : AtomSystem) (m p n : ℕ) : ℝ := bpNN A m p n

def B (A : AtomSystem) (m n : ℕ) : ℝ := ∑ p ∈ primes A, bp A m p n

/-- Previous retained value at the same prime (zero if there is no previous level). -/
def previousValue (A : AtomSystem) (m : ℕ) (a : ℕ × ℕ) : ℝ≥0 :=
  ((retained A m).filter (fun b => b.1 = a.1 ∧ b.2 < a.2)).sup (levelValue A)

def increment (A : AtomSystem) (m : ℕ) (a : ℕ × ℕ) : ℝ :=
  (levelValue A a : ℝ) - previousValue A m a

def HB (A : AtomSystem) (m : ℕ) : ℝ :=
  ∑ a ∈ retained A m, increment A m a / (modulus a : ℝ)

def LB (A : AtomSystem) (m : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 m, max (B A m k - 11 / 2) 0

def RB (A : AtomSystem) (m x : ℕ) : ℝ :=
  ∑ n ∈ Icc (x + 1) (x + m), max (B A m n - 1) 0

/-- Increasing height is decreasing dyadic value; ties are broken by `(p,j)`. -/
def orderKey (A : AtomSystem) (a : ℕ × ℕ) : Lex (ℕ × Lex (ℕ × ℕ)) :=
  toLex (levelHeight A a, toLex a)

def orderedLevels (A : AtomSystem) (s : Finset (ℕ × ℕ)) : List (ℕ × ℕ) :=
  ((s.image (orderKey A)).sort).map (fun k => ofLex (ofLex k).2)

/-- At each prime, the largest retained exponent whose modulus divides `n`. -/
def effective (A : AtomSystem) (m n : ℕ) : Finset (ℕ × ℕ) :=
  (retained A m).filter (fun a => modulus a ∣ n ∧
    ∀ b ∈ retained A m, b.1 = a.1 → modulus b ∣ n → b.2 ≤ a.2)

def effectiveList (A : AtomSystem) (m n : ℕ) : List (ℕ × ℕ) :=
  orderedLevels A (effective A m n)

def hot (A : AtomSystem) (m : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 m).filter (fun k => 11 / 2 < B A m k)

def prefixLevels (A : AtomSystem) (m k i : ℕ) : List (ℕ × ℕ) :=
  (effectiveList A m k).take i

def prefixProd (A : AtomSystem) (m k i : ℕ) : ℕ :=
  ((prefixLevels A m k i).map modulus).prod

def partialMass (A : AtomSystem) (m k i : ℕ) : ℝ :=
  ((prefixLevels A m k i).map (fun a => (levelValue A a : ℝ))).sum


end Rounded

def bp (A : AtomSystem) (m p n : ℕ) : ℝ := Rounded.bp (small A m) m p n
def B (A : AtomSystem) (m n : ℕ) : ℝ := Rounded.B (small A m) m n
def HB (A : AtomSystem) (m : ℕ) : ℝ := Rounded.HB (small A m) m
def LB (A : AtomSystem) (m : ℕ) : ℝ := hingeSum (B A m) (11/2) 0 m
def RB (A : AtomSystem) (m x : ℕ) : ℝ := hingeSum (B A m) 1 x m
/-- Least prefix length whose mass exceeds one; zero only if no such prefix exists. -/
def carrierLength (A : AtomSystem) (m k : ℕ) : ℕ :=
  if h : ∃ i, 1 < Rounded.partialMass (small A m) m k i then Nat.find h else 0
def carrierAt (A : AtomSystem) (m k : ℕ) : ℕ :=
  Rounded.prefixProd (small A m) m k (carrierLength A m k)
def hot (A : AtomSystem) (m : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 m).filter (fun k => 11/2 < B A m k)
def carriers (A : AtomSystem) (m : ℕ) : Finset ℕ := (hot A m).image (carrierAt A m)
def lastLevel (A : AtomSystem) (m P : ℕ) : ℕ × ℕ :=
  (Rounded.effectiveList (small A m) m P).getLast?.getD (0,0)
def theta (A : AtomSystem) (m P : ℕ) : ℝ := Rounded.levelValue (small A m) (lastLevel A m P)
def mu (A : AtomSystem) (m P : ℕ) : ℝ := B A m P
def nu (m P : ℕ) : ℕ := m / P
def M (A : AtomSystem) (m P : ℕ) : ℝ :=
  ∑ k ∈ (hot A m).filter (fun k => carrierAt A m k = P), (B A m k - 11/2)
def coefficient (A : AtomSystem) (m P : ℕ) : ℝ := M A m P / (nu m P : ℝ)
def U (A : AtomSystem) (m P n : ℕ) : ℝ :=
  ∑ p ∈ (Rounded.primes (small A m)).filter (fun p => ¬ p ∣ P), min (bp A m p n) (theta A m P)
def F (A : AtomSystem) (m n : ℕ) : ℝ :=
  24 * ∑ P ∈ carriers A m, if P ∣ n then coefficient A m P * (1 - U A m P n / K) else 0
def delta (A : AtomSystem) (m : ℕ) (θ : ℝ) (a : ℕ × ℕ) : ℝ :=
  min (Rounded.levelValue (small A m) a : ℝ) θ -
    min (Rounded.previousValue (small A m) m a : ℝ) θ
def certificateSupport (A : AtomSystem) (m : ℕ) : Finset ℕ :=
  carriers A m ∪ (carriers A m).biUnion (fun P =>
    ((Rounded.retained (small A m) m).filter (fun a => ¬ a.1 ∣ P)).image
      (fun a => P * Rounded.modulus a))
def signedCoefficient (A : AtomSystem) (m D : ℕ) : ℝ :=
  (∑ P ∈ carriers A m, if P = D then 24 * coefficient A m P else 0) -
    (24 / K) * ∑ P ∈ carriers A m, coefficient A m P *
      ∑ a ∈ (Rounded.retained (small A m) m).filter (fun a => ¬ a.1 ∣ P),
        if P * Rounded.modulus a = D then delta A m (theta A m P) a else 0
/-- Scale h represents ell = 2^h, including the exceptional ell=1 fourth moment. -/
def momentOrder (h : ℕ) : ℕ := if h = 0 then 4 else 9 * 2^(h-1)
def epsilon (h : ℕ) : ℝ :=
  if h = 0 then gamma * Hstar^4 / (2 * Nat.factorial 4)
  else gamma * (2^h : ℝ)^(momentOrder h - 1) * Hstar^(momentOrder h) /
    (Nat.factorial (momentOrder h) : ℝ)
/-- 1 + X + X² + X⁴ + ... + X^(2^h), with no repeated monomial. -/
def countingPolynomial (h : ℕ) : Polynomial ℕ :=
  1 + ∑ j ∈ range (h+1), Polynomial.X^(2^j)
def carrierCount (h N : ℕ) : ℕ := ((countingPolynomial h)^N).coeff (2^h+1)
def countLimit (h : ℕ) : ℕ := (51 * 2^h) / 16 + 1
def countRatio (h N : ℕ) : ℝ :=
  (carrierCount h N : ℝ) * max (1 - max 0 (((N : ℝ)-2^h-1)/2^h) / K) 0 /
    max (1/2^h) (((N : ℝ)-2^h)/2^h)
def Rscale (h : ℕ) : ℝ :=
  (range (countLimit h + 1)).sup' (by simp) (countRatio h)
def numericTerm (h : ℕ) : ℝ := 24 * epsilon h * Rscale h

def component (A : AtomSystem) (p n : ℕ) : ℝ :=
  ∑ a ∈ A.atoms.filter (fun a => a.1 = p ∧ a.1^a.2 ∣ n), A.weight a
def esymm {ι : Type*} (s : Finset ι) (u : ι → ℝ) (r : ℕ) : ℝ :=
  ∑ t ∈ s.powersetCard r, ∏ i ∈ t, u i
end
end Erdos708H17
