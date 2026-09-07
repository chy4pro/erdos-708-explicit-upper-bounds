import Mathlib

open Finset BigOperators
open scoped NNReal

namespace Erdos708SparseCore

structure AtomSystem where
  atoms : Finset (ℕ × ℕ)
  weight : ℕ × ℕ → ℝ
  prime_of_mem : ∀ a ∈ atoms, Nat.Prime a.1 ∧ 1 ≤ a.2
  weight_nonneg : ∀ a ∈ atoms, 0 ≤ weight a
  perPrime_le_one : ∀ p : ℕ, ∑ a ∈ atoms.filter (fun a => a.1 = p), weight a ≤ 1

/-- `S₀(n) = Σ_{(p,j) ∈ atoms, p^j ∣ n} α(p,j)`. -/
noncomputable def S0 (A : AtomSystem) (n : ℕ) : ℝ :=
  ∑ a ∈ A.atoms.filter (fun a => a.1 ^ a.2 ∣ n), A.weight a

/-- The mean `H = Σ α(p,j) / p^j` of `S₀` over the integers. -/
noncomputable def mean (A : AtomSystem) : ℝ :=
  ∑ a ∈ A.atoms, A.weight a / ((a.1 : ℝ) ^ a.2)

/-- Left hinge sum `L = Σ_{k=1}^{m} (S₀(k) − 64)⁺`. -/
noncomputable def L (A : AtomSystem) (m : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 m, max (S0 A k - 64) 0

/-- Right hinge sum `R = Σ_{b=x+1}^{x+m} (S₀(b) − 1)⁺` over the window of `m` consecutive
integers starting after `x`. -/
noncomputable def R (A : AtomSystem) (x m : ℕ) : ℝ :=
  ∑ b ∈ Icc (x + 1) (x + m), max (S0 A b - 1) 0

/-! Concrete finite constructions from Section 14. The base atom system and
`S0`, `mean`, `L`, `R` above are copied verbatim from the original statement card. -/

noncomputable section

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

/-- The modulus-cost cutoff, with the exact integer exponent `16 / t`. -/
def retained (A : AtomSystem) (m : ℕ) : Finset (ℕ × ℕ) :=
  (roundedLevels A).filter (fun a => modulus a ^ (16 * 2 ^ levelHeight A a) ≤ m)

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
  ∑ k ∈ Icc 1 m, max (B A m k - 16) 0

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
  exact (Icc 1 m).filter (fun k => 16 < B A m k)

def prefixLevels (A : AtomSystem) (m k i : ℕ) : List (ℕ × ℕ) :=
  (effectiveList A m k).take i

def prefixProd (A : AtomSystem) (m k i : ℕ) : ℕ :=
  ((prefixLevels A m k i).map modulus).prod

def partialMass (A : AtomSystem) (m k i : ℕ) : ℝ :=
  ((prefixLevels A m k i).map (fun a => (levelValue A a : ℝ))).sum

/-- Length of `[s_{i-1},s_i) ∩ (2,3]`; endpoint conventions do not change length. -/
def prefixWeight (A : AtomSystem) (m k i : ℕ) : ℝ :=
  max (min (partialMass A m k i) 3 - max (partialMass A m k (i - 1)) 2) 0

/-- Exactly the hot prefix occurrences with strictly positive weight. -/
def occurrences (A : AtomSystem) (m : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (hot A m).biUnion (fun k =>
    ((Icc 1 (effectiveList A m k).length).filter
      (fun i => 0 < prefixWeight A m k i)).image (fun i => (k, i)))

def carriers (A : AtomSystem) (m : ℕ) : Finset ℕ :=
  (occurrences A m).image (fun ki => prefixProd A m ki.1 ki.2)

/-- Carrier levels can be recovered from the modulus itself. -/
def lastLevel (A : AtomSystem) (m P : ℕ) : ℕ × ℕ :=
  (effectiveList A m P).getLast?.getD (0, 0)

def mu (A : AtomSystem) (m P : ℕ) : ℝ := B A m P

def theta (A : AtomSystem) (m P : ℕ) : ℝ := levelValue A (lastLevel A m P)

def M (A : AtomSystem) (m P : ℕ) : ℝ :=
  ∑ ki ∈ (occurrences A m).filter (fun ki => prefixProd A m ki.1 ki.2 = P),
    (B A m ki.1 - 16) * prefixWeight A m ki.1 ki.2

def K (m P : ℕ) : ℕ := m / P

def coefficient (A : AtomSystem) (m P : ℕ) : ℝ := M A m P / (K m P : ℝ)

/-- For `θ=2⁻ʰ`, the integer moment order is `12/θ+1`. -/
def momentOrder (h : ℕ) : ℕ := 12 * 2 ^ h + 1

def epsilon (H : ℝ) (h : ℕ) : ℝ :=
  ((2 : ℝ)⁻¹ ^ h) ^ (2 - (momentOrder h : ℤ)) *
    H ^ momentOrder h / (Nat.factorial (momentOrder h) : ℝ)

def G (H : ℝ) (h : ℕ) : ℝ :=
  epsilon H h / ((2 : ℝ)⁻¹ ^ h) * 2 ^ (23 * 2 ^ h)

def Ttheta (A : AtomSystem) (m n : ℕ) (θ : ℝ) : ℝ :=
  ∑ p ∈ primes A, min (bp A m p n) θ

def Ntheta (A : AtomSystem) (m n : ℕ) (θ : ℝ) : ℕ := by
  classical
  exact #((primes A).filter (fun p => θ ≤ bp A m p n))

def U (A : AtomSystem) (m P n : ℕ) : ℝ :=
  ∑ p ∈ (primes A).filter (fun p => ¬ p ∣ P), min (bp A m p n) (theta A m P)

def F (A : AtomSystem) (m n : ℕ) : ℝ :=
  3 * ∑ P ∈ carriers A m, if P ∣ n then coefficient A m P * (1 - U A m P n / 16) else 0

/-- Clipped increments used to expand the negative part of the certificate. -/
def beta (A : AtomSystem) (m : ℕ) (θ : ℝ) (a : ℕ × ℕ) : ℝ :=
  min (levelValue A a : ℝ) θ - min (previousValue A m a : ℝ) θ

def certificateSupport (A : AtomSystem) (m : ℕ) : Finset ℕ :=
  carriers A m ∪ (carriers A m).biUnion (fun P =>
    ((retained A m).filter (fun a => ¬ a.1 ∣ P)).image (fun a => P * modulus a))

/-- Combined coefficients; the definition has no window parameter. -/
def signedCoefficient (A : AtomSystem) (m D : ℕ) : ℝ :=
  (∑ P ∈ carriers A m, if P = D then 3 * coefficient A m P else 0) -
    (3 / 16 : ℝ) * ∑ P ∈ carriers A m, coefficient A m P *
      ∑ a ∈ (retained A m).filter (fun a => ¬ a.1 ∣ P),
        if P * modulus a = D then beta A m (theta A m P) a else 0

 theorem numerical_bound (t : ℕ) (ht : 1 ≤ t) (H : ℝ) (hH0 : 0 ≤ H) (hH : H ≤ 17 / 16) :
    (t : ℝ) ^ (12 * t) * H ^ (12 * t + 1) * 2 ^ (23 * t) / (Nat.factorial (12 * t + 1) : ℝ)
      ≤ 17 / 416 := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hnR : (1 : ℝ) ≤ (12 * t : ℕ) := by push_cast; linarith
  have he : Real.exp 1 ≤ (11 : ℝ) / 4 := by linarith [Real.exp_one_lt_d9]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (12 * t : ℕ)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [Real.pi_gt_three]
  have hb : (t : ℝ) * 48 / 11 ≤ (12 * t : ℕ) / Real.exp 1 := by
    apply (le_div_iff₀ (Real.exp_pos 1)).2
    push_cast
    nlinarith
  have hfac : ((t : ℝ) * 48 / 11) ^ (12 * t) ≤ (Nat.factorial (12 * t) : ℝ) := by
    calc
      _ ≤ ((12 * t : ℕ) / Real.exp 1 : ℝ) ^ (12 * t) :=
        pow_le_pow_left₀ (by positivity) hb _
      _ ≤ Real.sqrt (2 * Real.pi * (12 * t : ℕ)) *
          ((12 * t : ℕ) / Real.exp 1 : ℝ) ^ (12 * t) := by
        exact le_mul_of_one_le_left (by positivity) hsqrt
      _ ≤ _ := Stirling.le_factorial_stirling (12 * t)
  let b : ℝ := (187 / 768 : ℝ) ^ 12 * 2 ^ 23
  have hb0 : 0 ≤ b := by norm_num [b]
  have hbhalf : b ≤ (1 : ℝ) / 2 := by norm_num [b]
  have hbt : b ^ t ≤ (1 : ℝ) / 2 := by
    calc
      b ^ t ≤ b ^ 1 := pow_le_pow_of_le_one hb0 (hbhalf.trans (by norm_num)) ht
      _ ≤ _ := by simpa using hbhalf
  have hid : (t : ℝ) ^ (12 * t) * (17 / 16 : ℝ) ^ (12 * t) * 2 ^ (23 * t) =
      ((t : ℝ) * 48 / 11) ^ (12 * t) * b ^ t := by
    simp only [pow_mul, ← mul_pow]
    congr 1
    dsimp [b]
    ring
  have hnum : (t : ℝ) ^ (12 * t) * H ^ (12 * t + 1) * 2 ^ (23 * t) ≤
      (17 / 32 : ℝ) * (Nat.factorial (12 * t) : ℝ) := by
    calc
      _ ≤ (t : ℝ) ^ (12 * t) * (17 / 16 : ℝ) ^ (12 * t + 1) * 2 ^ (23 * t) := by
        gcongr
      _ = ((t : ℝ) * 48 / 11) ^ (12 * t) * b ^ t * (17 / 16 : ℝ) := by
        rw [pow_succ]
        nlinarith [hid]
      _ ≤ (Nat.factorial (12 * t) : ℝ) * (1 / 2 : ℝ) * (17 / 16 : ℝ) := by
        gcongr
      _ = _ := by ring
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < Nat.factorial (12 * t + 1))).2
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_mul]
  norm_num only [Nat.cast_ofNat, Nat.cast_one]
  have hf0 : (0 : ℝ) ≤ Nat.factorial (12 * t) := by positivity
  nlinarith

theorem uniform_numerical (H : ℝ) (hH0 : 0 ≤ H) (hH : H ≤ 17 / 16) (h : ℕ) :
    G H h ≤ 17 / 416 := by
  let t : ℕ := 2 ^ h
  have ht : 1 ≤ t := Nat.one_le_pow _ _ (by norm_num)
  have he : (2 : ℤ) - (momentOrder h : ℤ) = 1 - ((12 * t : ℕ) : ℤ) := by
    dsimp [momentOrder, t]
    push_cast
    ring
  have hθ : (2 : ℝ)⁻¹ ^ h = (t : ℝ)⁻¹ := by simp [t, inv_pow]
  have hG : G H h = (t : ℝ) ^ (12 * t) * H ^ (12 * t + 1) * 2 ^ (23 * t) /
      (Nat.factorial (12 * t + 1) : ℝ) := by
    unfold G epsilon
    rw [he, zpow_sub₀ (by positivity), zpow_one, zpow_natCast, hθ]
    simp only [inv_pow, inv_inv]
    change ((t : ℝ)⁻¹ / ((t : ℝ) ^ (12 * t))⁻¹ * H ^ (12 * t + 1) /
      (Nat.factorial (12 * t + 1) : ℝ)) / (t : ℝ)⁻¹ * 2 ^ (23 * t) = _
    have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
    field_simp
  rw [hG]
  exact numerical_bound t ht H hH0 hH

#print axioms uniform_numerical

end
end Erdos708SparseCore
