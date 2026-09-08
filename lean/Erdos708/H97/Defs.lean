import Erdos708.H17.Defs
open Finset BigOperators
open scoped NNReal
namespace Erdos708H97
noncomputable section
attribute [local instance] Classical.propDecidable
export Erdos708H17 (AtomSystem S mean restrict small S_0 H Hstar hingeSum component esymm)
def Q : ℕ := 2^16
def gamma : ℝ := 211/210
def K : ℝ := 8/3
def lambda : ℝ := 51/10
def rho : ℝ := 5/4
def D0 : ℝ := 47/16
def T : ℝ := 541/100
def eta (t : ℝ) : ℝ := if 1/2 < t then 1/3 else 4*t/9
def L (A : AtomSystem) (m : ℕ) : ℝ := hingeSum (S A) (97/10) 0 m
def R (A : AtomSystem) (x m : ℕ) : ℝ := hingeSum (S A) 1 x m
def Hinge97 : Prop := ∀ (A : AtomSystem) (m x : ℕ), L A m ≤ R A x m
namespace Rounded
/-- The finitely many primes occurring in the original atom support. -/
def primes (A : AtomSystem) : Finset ℕ := A.atoms.image Prod.fst

/-- Cumulative original weight through exponent `j` at prime `p`. -/
def cumulative (A : AtomSystem) (p j : ℕ) : ℝ :=
  ∑ a ∈ A.atoms.filter (fun a => a.1 = p ∧ a.2 ≤ j), A.weight a

/-- Descending enumeration: 1, 7/8, 6/8, 5/8, 4/8, 7/16, ... . -/
def level (i : ℕ) : ℝ≥0 :=
  if i = 0 then 1 else ((7 - (i-1)%4 : ℕ) : ℝ≥0) / 2^((i-1)/4+3)
def roundIndex (u : ℝ) : ℕ :=
  if h : ∃ i : ℕ, (level i : ℝ) ≤ u then Nat.find h else 0

def levelHeight (A : AtomSystem) (a : ℕ × ℕ) : ℕ :=
  roundIndex (cumulative A a.1 a.2)

/-- Nonnegative-real four-mantissa value, enabling finite suprema with bottom zero. -/
def levelValue (A : AtomSystem) (a : ℕ × ℕ) : ℝ≥0 :=
  level (levelHeight A a)

def modulus (a : ℕ × ℕ) : ℕ := a.1 ^ a.2

/-- First exponent in the original support at which a positive rounded value occurs. -/
def roundedLevels (A : AtomSystem) : Finset (ℕ × ℕ) := by
  classical
  exact A.atoms.filter (fun a => 0 < cumulative A a.1 a.2 ∧
    ∀ b ∈ A.atoms, b.1 = a.1 → 0 < cumulative A b.1 b.2 →
      levelHeight A b = levelHeight A a → a.2 ≤ b.2)

/-- The retention cutoff q <= m^eta(t), with the manuscript's piecewise exponent. -/
def retained (A : AtomSystem) (m : ℕ) : Finset (ℕ × ℕ) :=
  (roundedLevels A).filter (fun a => (modulus a : ℝ) ≤ (m : ℝ) ^ eta (levelValue A a))

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
  ∑ k ∈ Icc 1 m, max (B A m k - T) 0

def RB (A : AtomSystem) (m x : ℕ) : ℝ :=
  ∑ n ∈ Icc (x + 1) (x + m), max (B A m n - 1) 0

/-- Increasing level index is decreasing level value; ties are broken by `(p,j)`. -/
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
  exact (Icc 1 m).filter (fun k => T < B A m k)

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
def LB (A : AtomSystem) (m : ℕ) : ℝ := hingeSum (B A m) (T) 0 m
def RB (A : AtomSystem) (m x : ℕ) : ℝ := hingeSum (B A m) 1 x m
/-- Least prefix length whose mass exceeds one; zero only if no such prefix exists. -/
def carrierLength (A : AtomSystem) (m k : ℕ) : ℕ :=
  if h : ∃ i, 1 < Rounded.partialMass (small A m) m k i then Nat.find h else 0
def carrierAt (A : AtomSystem) (m k : ℕ) : ℕ :=
  Rounded.prefixProd (small A m) m k (carrierLength A m k)
def hot (A : AtomSystem) (m : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 m).filter (fun k => T < B A m k)
def carriers (A : AtomSystem) (m : ℕ) : Finset ℕ := (hot A m).image (carrierAt A m)
def lastLevel (A : AtomSystem) (m P : ℕ) : ℕ × ℕ :=
  (Rounded.effectiveList (small A m) m P).getLast?.getD (0,0)
def theta (A : AtomSystem) (m P : ℕ) : ℝ := Rounded.levelValue (small A m) (lastLevel A m P)
def mu (A : AtomSystem) (m P : ℕ) : ℝ := B A m P
def nu (m P : ℕ) : ℕ := m / P
def M (A : AtomSystem) (m P : ℕ) : ℝ :=
  ∑ k ∈ (hot A m).filter (fun k => carrierAt A m k = P), (B A m k - T)
def coefficient (A : AtomSystem) (m P : ℕ) : ℝ := M A m P / (nu m P : ℝ)
def U (A : AtomSystem) (m P n : ℕ) : ℝ :=
  ∑ p ∈ (Rounded.primes (small A m)).filter (fun p => ¬ p ∣ P), min (bp A m p n) (theta A m P)
def F (A : AtomSystem) (m n : ℕ) : ℝ :=
  lambda * ∑ P ∈ carriers A m, if P ∣ n then coefficient A m P * (1 - U A m P n / K) else 0
def delta (A : AtomSystem) (m : ℕ) (θ : ℝ) (a : ℕ × ℕ) : ℝ :=
  min (Rounded.levelValue (small A m) a : ℝ) θ -
    min (Rounded.previousValue (small A m) m a : ℝ) θ
def certificateSupport (A : AtomSystem) (m : ℕ) : Finset ℕ :=
  carriers A m ∪ (carriers A m).biUnion (fun P =>
    ((Rounded.retained (small A m) m).filter (fun a => ¬ a.1 ∣ P)).image
      (fun a => P * Rounded.modulus a))
def signedCoefficient (A : AtomSystem) (m D : ℕ) : ℝ :=
  (∑ P ∈ carriers A m, if P = D then lambda * coefficient A m P else 0) -
    (lambda / K) * ∑ P ∈ carriers A m, coefficient A m P *
      ∑ a ∈ (Rounded.retained (small A m) m).filter (fun a => ¬ a.1 ∣ P),
        if P * Rounded.modulus a = D then delta A m (theta A m P) a else 0

/-- The full manuscript level set; retained maxima use only first crossing atoms. -/
def levels : Set ℝ := {t | t = 1 ∨ ∃ (h : ℕ), 3 ≤ h ∧ ∃ (j : ℕ), j ∈ Icc 4 7 ∧ t = (j : ℝ)/2^h}
def maximizingVertex (a : ℝ) (r : ℕ) : ℕ := ⌊(r : ℝ)*a/(r-1)⌋₊
def hingeMajorant (a : ℝ) (r : ℕ) : ℝ :=
  ((maximizingVertex a r : ℝ)-a)/(Nat.choose (maximizingVertex a r) r : ℝ)
def momentBound (θ s : ℝ) (r : ℕ) : ℝ :=
  θ * hingeMajorant ((T-s)/θ) r * (Hstar/θ)^r / (Nat.factorial r : ℝ)
def momentRange (θ s : ℝ) : Finset ℕ := Icc 2 (⌊(T-s)/θ⌋₊+1)
def epsilon (θ s : ℝ) : ℝ :=
  if h : (momentRange θ s).Nonempty then (momentRange θ s).inf' h (momentBound θ s) else 0
/-- Integer degrees of levels at least j/L, with the level-1 degree L included. -/
def exponents (j L : ℕ) : Finset ℕ :=
  (Icc j L).filter (fun e => ∃ a ∈ Icc 4 7, ∃ h ∈ range (L+1), e = a*2^h)
def countingPolynomial (j L : ℕ) : Polynomial ℕ :=
  1 + ∑ e ∈ exponents j L, Polynomial.X^e
def omittedPolynomial (j L : ℕ) : Polynomial ℕ :=
  1 + ∑ e ∈ (exponents j L).erase j, Polynomial.X^e
def carrierCount (j L d N : ℕ) : ℕ :=
  ((countingPolynomial j L)^N).coeff (L+d) - ((omittedPolynomial j L)^N).coeff (L+d)
def countLimit (j L : ℕ) : ℕ := (11*L)/(3*j)+1
def countRatio (j L d N : ℕ) : ℝ :=
  max (1-max 0 ((N : ℝ)*j/L-1-d/L)/K) 0 / max ((d : ℝ)/L) ((N : ℝ)*j/L-1)
def scaleValue (j L N : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 j, (carrierCount j L d N : ℝ) * epsilon ((j : ℝ)/L) (1+(d : ℝ)/L) * countRatio j L d N
def AScale (j L : ℕ) : ℝ := (range (countLimit j L+1)).sup' (by simp) (scaleValue j L)
def finiteGroup (h : ℕ) : ℝ := if h=2 then AScale 4 4 else ∑ j ∈ Icc 4 7, AScale j (2^h)
def finiteTotal : ℝ := ∑ h ∈ Icc 2 9, finiteGroup h
def a0 : ℝ := 4377/100000
def tailEpsilon (θ : ℝ) : ℝ := 9*θ/8 * a0^(1/θ)
def tailScaleValue (j L N : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 j, (carrierCount j L d N : ℝ) * tailEpsilon ((j : ℝ)/L) * countRatio j L d N
def tailAScale (j L : ℕ) : ℝ :=
  (range (countLimit j L+1)).sup' (by simp) (tailScaleValue j L)
def tailTerm (r : ℕ) : ℝ := ∑ j ∈ Icc 4 7, tailAScale j (1024*2^r)
def tailX (j : ℕ) : ℝ := match j with
  | 4 => 583/1000 | 5 => 321/500 | 6 => 69/100 | _ => 73/100
def tailF (j : ℕ) : ℝ := match j with
  | 4 => 632591/500000 | 5 => 159089/125000 | 6 => 1278827/1000000 | _ => 639137/500000
def tailD (j : ℕ) : ℝ := ∑ d ∈ Icc 1 j, (tailX j)⁻¹^d
def generatingSeries (j : ℕ) (x : ℝ) : ℝ :=
  1 + ∑ a ∈ Icc j 7, x^a + ∑' r : ℕ, ∑ a ∈ Icc 4 7, x^(a*2^(r+1))
def tailBound : ℝ :=
  (9/8)*(∑ j ∈ Icc (4 : ℕ) 7, (j : ℝ)*tailD j)*(3/4)^146/(1-(3/4)^146) +
  (2187/4096)*(4/(3*1024^2))*(∑ j ∈ Icc (4 : ℕ) 7, (j : ℝ)^2*tailF j*tailD j)
end
end Erdos708H97
