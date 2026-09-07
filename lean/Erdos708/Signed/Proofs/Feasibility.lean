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

private lemma rounding_retained_mem_atoms (A : AtomSystem) (m : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) : a ∈ A.atoms :=
  (mem_filter.mp (mem_filter.mp ha).1).1

private lemma retained_cumulative_pos (A : AtomSystem) (m : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) : 0 < cumulative A a.1 a.2 :=
  (mem_filter.mp (mem_filter.mp ha).1).2.1

private lemma cumulative_nonneg (A : AtomSystem) (p j : ℕ) : 0 ≤ cumulative A p j :=
  sum_nonneg (fun a ha => A.weight_nonneg a (mem_filter.mp ha).1)

private lemma cumulative_le_one (A : AtomSystem) (p j : ℕ) : cumulative A p j ≤ 1 := by
  apply le_trans _ (A.perPrime_le_one p)
  apply sum_le_sum_of_subset_of_nonneg
  · intro a ha
    exact mem_filter.mpr ⟨(mem_filter.mp ha).1, (mem_filter.mp ha).2.1⟩
  · intro a ha _
    exact A.weight_nonneg a (mem_filter.mp ha).1

private lemma cumulative_mono (A : AtomSystem) (p : ℕ) {i j : ℕ} (hij : i ≤ j) :
    cumulative A p i ≤ cumulative A p j := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro a ha
    exact mem_filter.mpr ⟨(mem_filter.mp ha).1, (mem_filter.mp ha).2.1,
      (mem_filter.mp ha).2.2.trans hij⟩
  · intro a ha _
    exact A.weight_nonneg a (mem_filter.mp ha).1

private lemma exists_dyadic_le {u : ℝ} (hu : 0 < u) : ∃ h : ℕ, (2 : ℝ)⁻¹ ^ h ≤ u := by
  obtain ⟨h, hh⟩ := exists_pow_lt_of_lt_one hu (by norm_num : (2 : ℝ)⁻¹ < 1)
  exact ⟨h, hh.le⟩

private lemma dyadic_le {u : ℝ} (hu : 0 < u) : (2 : ℝ)⁻¹ ^ dyadicHeight u ≤ u := by
  rw [dyadicHeight, dif_pos (exists_dyadic_le hu)]
  exact Nat.find_spec (exists_dyadic_le hu)

private lemma lt_twice_dyadic {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    u < 2 * (2 : ℝ)⁻¹ ^ dyadicHeight u := by
  rw [dyadicHeight, dif_pos (exists_dyadic_le hu)]
  generalize heq : Nat.find (exists_dyadic_le hu) = h
  cases h with
  | zero => norm_num; linarith
  | succ h =>
    have hlt : u < (2 : ℝ)⁻¹ ^ h :=
      lt_of_not_ge (Nat.find_min (exists_dyadic_le hu) (by omega))
    convert hlt using 1 <;> ring

private lemma dyadicHeight_antitone {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    dyadicHeight v ≤ dyadicHeight u := by
  rw [dyadicHeight, dif_pos (exists_dyadic_le (hu.trans_le huv)),
    dyadicHeight, dif_pos (exists_dyadic_le hu)]
  exact Nat.find_min' _ ((Nat.find_spec (exists_dyadic_le hu)).trans huv)

private lemma retained_value_le_cumulative (A : AtomSystem) (m : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) : (levelValue A a : ℝ) ≤ cumulative A a.1 a.2 := by
  simpa [levelValue, levelHeight] using dyadic_le (retained_cumulative_pos A m ha)

private lemma retained_value_mono (A : AtomSystem) (m : ℕ) {a b : ℕ × ℕ}
    (ha : a ∈ retained A m) (hb : b ∈ retained A m) (hp : a.1 = b.1) (hj : a.2 ≤ b.2) :
    levelValue A a ≤ levelValue A b := by
  apply pow_le_pow_of_le_one (by positivity) (by norm_num : (2 : ℝ≥0)⁻¹ ≤ 1)
  apply dyadicHeight_antitone (retained_cumulative_pos A m ha)
  simpa only [hp] using cumulative_mono A b.1 hj

private def ap (A : AtomSystem) (p n : ℕ) : ℝ :=
  ∑ a ∈ A.atoms.filter (fun a => a.1 = p ∧ modulus a ∣ n), A.weight a

private lemma ap_nonneg (A : AtomSystem) (p n : ℕ) : 0 ≤ ap A p n :=
  sum_nonneg (fun a ha => A.weight_nonneg a (mem_filter.mp ha).1)

private lemma bp_le_ap (A : AtomSystem) (m p n : ℕ) : bp A m p n ≤ ap A p n := by
  have hsup : bpNN A m p n ≤ ⟨ap A p n, ap_nonneg A p n⟩ := by
    apply Finset.sup_le
    intro a ha
    obtain ⟨ha, hap, han⟩ := mem_filter.mp ha
    change (levelValue A a : ℝ) ≤ ap A p n
    apply le_trans (retained_value_le_cumulative A m ha)
    apply sum_le_sum_of_subset_of_nonneg
    · intro b hb
      obtain ⟨hb, hbp, hbj⟩ := mem_filter.mp hb
      refine mem_filter.mpr ⟨hb, hbp.trans hap, ?_⟩
      simpa only [modulus, hbp] using (Nat.pow_dvd_pow a.1 hbj).trans han
    · intro b hb _
      exact A.weight_nonneg b (mem_filter.mp hb).1
  exact_mod_cast hsup

private lemma B_le_S0 (A : AtomSystem) (m n : ℕ) : B A m n ≤ S0 A n := by
  calc
    _ ≤ ∑ p ∈ primes A, ap A p n := sum_le_sum (fun p hp => bp_le_ap A m p n)
    _ = _ := by
      have hmap : ∀ a ∈ A.atoms.filter (fun a => modulus a ∣ n), a.1 ∈ primes A := by
        intro a ha
        exact mem_image_of_mem Prod.fst (mem_filter.mp ha).1
      dsimp only [ap, S0]
      change _ = ∑ a ∈ A.atoms.filter (fun a => modulus a ∣ n), A.weight a
      rw [← sum_fiberwise_of_maps_to hmap A.weight]
      apply sum_congr rfl
      intro p hp
      apply sum_congr
      · ext a
        constructor
        · intro ha
          obtain ⟨ha, hap, had⟩ := mem_filter.mp ha
          exact mem_filter.mpr ⟨mem_filter.mpr ⟨ha, had⟩, hap⟩
        · intro ha
          obtain ⟨ha, hap⟩ := mem_filter.mp ha
          exact mem_filter.mpr ⟨(mem_filter.mp ha).1, hap, (mem_filter.mp ha).2⟩
      · intro a ha
        rfl

private lemma RB_le_R (A : AtomSystem) (m x : ℕ) : RB A m x ≤ R A x m := by
  apply sum_le_sum
  intro n hn
  exact max_le_max (sub_le_sub_right (B_le_S0 A m n) 1) le_rfl

private lemma sum_jumps_eq_sup {ι : Type*} (s : Finset ι) (key : ι → ℕ) (v : ι → ℝ≥0)
    (hinj : Set.InjOn key (s : Set ι))
    (hmono : ∀ a ∈ s, ∀ b ∈ s, key a ≤ key b → v a ≤ v b) :
    (∑ a ∈ s, ((v a : ℝ) - ((s.filter (fun b => key b < key a)).sup v : ℝ≥0))) =
      (s.sup v : ℝ≥0) := by
  classical
  induction s using Finset.induction_on_max_value key with
  | empty => simp
  | insert a s ha hmax ih =>
    have hinj' : Set.InjOn key (s : Set ι) :=
      fun b hb c hc hbc => hinj (mem_insert_of_mem hb) (mem_insert_of_mem hc) hbc
    have hmono' : ∀ b ∈ s, ∀ c ∈ s, key b ≤ key c → v b ≤ v c :=
      fun b hb c hc hbc => hmono b (mem_insert_of_mem hb) c (mem_insert_of_mem hc) hbc
    have hlt (b : ι) (hb : b ∈ s) : key b < key a := by
      refine lt_of_le_of_ne (hmax b hb) ?_
      intro heq
      have hba := hinj (mem_insert_of_mem hb) (mem_insert_self a s) heq
      exact ha (hba ▸ hb)
    have hfa : (insert a s).filter (fun b => key b < key a) = s := by
      rw [filter_insert, if_neg (lt_irrefl _)]
      exact filter_eq_self.mpr hlt
    have hfb (b : ι) (hb : b ∈ s) :
        (insert a s).filter (fun c => key c < key b) = s.filter (fun c => key c < key b) := by
      rw [filter_insert, if_neg (not_lt.mpr (hmax b hb))]
    have hsum : (∑ b ∈ s, ((v b : ℝ) -
        ((insert a s).filter (fun c => key c < key b)).sup v)) =
        ∑ b ∈ s, ((v b : ℝ) - (s.filter (fun c => key c < key b)).sup v) := by
      apply sum_congr rfl
      intro b hb
      rw [hfb b hb]
    have hsup : s.sup v ≤ v a :=
      Finset.sup_le (fun b hb => hmono b (mem_insert_of_mem hb) a (mem_insert_self a s) (hmax b hb))
    rw [sum_insert ha, hfa, hsum, ih hinj' hmono', sup_insert, sup_of_le_left hsup]
    ring

private lemma increment_nonneg (A : AtomSystem) (m : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) : 0 ≤ increment A m a := by
  apply sub_nonneg.mpr
  have hh : previousValue A m a ≤ levelValue A a := by
    apply Finset.sup_le
    intro b hb
    obtain ⟨hb, hbp, hbj⟩ := mem_filter.mp hb
    exact retained_value_mono A m hb ha hbp hbj.le
  exact_mod_cast hh

private lemma increments_telescope (A : AtomSystem) (m p n : ℕ) :
    (∑ a ∈ (retained A m).filter (fun a => a.1 = p ∧ modulus a ∣ n), increment A m a) =
      bp A m p n := by
  classical
  let s := (retained A m).filter (fun a => a.1 = p ∧ modulus a ∣ n)
  have hinj : Set.InjOn Prod.snd (s : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    exact Prod.ext ((mem_filter.mp ha).2.1.trans (mem_filter.mp hb).2.1.symm) hab
  have hmono : ∀ a ∈ s, ∀ b ∈ s, a.2 ≤ b.2 → levelValue A a ≤ levelValue A b := by
    intro a ha b hb hab
    exact retained_value_mono A m (mem_filter.mp ha).1 (mem_filter.mp hb).1
      ((mem_filter.mp ha).2.1.trans (mem_filter.mp hb).2.1.symm) hab
  have hprev (a : ℕ × ℕ) (ha : a ∈ s) :
      previousValue A m a = (s.filter (fun b => b.2 < a.2)).sup (levelValue A) := by
    apply congrArg (fun t : Finset (ℕ × ℕ) => t.sup (levelValue A))
    ext b
    constructor
    · intro hb
      obtain ⟨hb, hbp, hbj⟩ := mem_filter.mp hb
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨hb, hbp.trans (mem_filter.mp ha).2.1, ?_⟩, hbj⟩
      simpa only [modulus, hbp] using
        (Nat.pow_dvd_pow a.1 hbj.le).trans (mem_filter.mp ha).2.2
    · intro hb
      obtain ⟨hb, hbj⟩ := mem_filter.mp hb
      exact mem_filter.mpr ⟨(mem_filter.mp hb).1,
        (mem_filter.mp hb).2.1.trans (mem_filter.mp ha).2.1.symm, hbj⟩
  calc
    _ = ∑ a ∈ s, ((levelValue A a : ℝ) -
        ((s.filter (fun b => b.2 < a.2)).sup (levelValue A) : ℝ≥0)) := by
      apply sum_congr rfl
      intro a ha
      rw [increment, hprev a ha]
    _ = (s.sup (levelValue A) : ℝ≥0) := sum_jumps_eq_sup s Prod.snd (levelValue A) hinj hmono
    _ = _ := rfl

private lemma B_eq_increment_sum (A : AtomSystem) (m n : ℕ) :
    B A m n = ∑ a ∈ (retained A m).filter (fun a => modulus a ∣ n), increment A m a := by
  classical
  calc
    _ = ∑ p ∈ primes A, ∑ a ∈ (retained A m).filter
        (fun a => a.1 = p ∧ modulus a ∣ n), increment A m a := by
      apply sum_congr rfl
      intro p hp
      exact (increments_telescope A m p n).symm
    _ = _ := by
      have hmap : ∀ a ∈ (retained A m).filter (fun a => modulus a ∣ n), a.1 ∈ primes A := by
        intro a ha
        exact mem_image_of_mem Prod.fst (rounding_retained_mem_atoms A m (mem_filter.mp ha).1)
      rw [← sum_fiberwise_of_maps_to hmap (increment A m)]
      apply sum_congr rfl
      intro p hp
      apply sum_congr
      · ext a
        simp only [mem_filter]
        tauto
      · intro a ha
        rfl

private lemma average_divisor_sum {ι : Type*} (s : Finset ι) (q : ι → ℕ) (w : ι → ℝ)
    (Q : ℕ) (hQ : 0 < Q) (hdiv : ∀ a ∈ s, q a ∣ Q) :
    (∑ n ∈ Icc 1 Q, ∑ a ∈ s.filter (fun a => q a ∣ n), w a) =
      (Q : ℝ) * ∑ a ∈ s, w a / (q a : ℝ) := by
  classical
  simp_rw [sum_filter]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro a ha
  have hq : 0 < q a := Nat.pos_of_dvd_of_pos (hdiv a ha) hQ
  have hc : #((Icc 1 Q).filter (fun n => q a ∣ n)) = Q / q a := by
    have heq : (Icc 1 Q).filter (fun n => q a ∣ n) =
        (range Q.succ).filter (fun n => n ≠ 0 ∧ q a ∣ n) := by
      ext n
      simp only [mem_filter, mem_Icc, mem_range]
      omega
    rw [heq, Nat.card_multiples']
  rw [← sum_filter, sum_const, nsmul_eq_mul, hc, Nat.cast_div (hdiv a ha) (by positivity)]
  ring

private lemma HB_le_mean (A : AtomSystem) (m : ℕ) : HB A m ≤ mean A := by
  let Q := ∏ a ∈ A.atoms, modulus a
  have hQ : 0 < Q := prod_pos (fun a ha => pow_pos (A.prime_of_mem a ha).1.pos _)
  have hdiv : ∀ a ∈ A.atoms, modulus a ∣ Q := fun a ha => dvd_prod_of_mem modulus ha
  have hdivB : ∀ a ∈ retained A m, modulus a ∣ Q :=
    fun a ha => hdiv a (rounding_retained_mem_atoms A m ha)
  have hle : (∑ n ∈ Icc 1 Q, B A m n) ≤ ∑ n ∈ Icc 1 Q, S0 A n :=
    sum_le_sum (fun n hn => B_le_S0 A m n)
  simp_rw [B_eq_increment_sum] at hle
  change (∑ n ∈ Icc 1 Q, ∑ a ∈ (retained A m).filter (fun a => modulus a ∣ n), increment A m a) ≤
    (∑ n ∈ Icc 1 Q, ∑ a ∈ A.atoms.filter (fun a => modulus a ∣ n), A.weight a) at hle
  rw [average_divisor_sum _ _ _ Q hQ hdivB, average_divisor_sum _ _ _ Q hQ hdiv] at hle
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hh := (_root_.mul_le_mul_iff_right₀ hQreal).mp hle
  simpa only [HB, mean, modulus, Nat.cast_pow] using hh

private lemma rounded_current_level (A : AtomSystem) (p n : ℕ) (hp : 0 < ap A p n) :
    ∃ a ∈ roundedLevels A, a.1 = p ∧ modulus a ∣ n ∧ ap A p n < 2 * (levelValue A a : ℝ) := by
  classical
  let s := A.atoms.filter (fun a => a.1 = p ∧ modulus a ∣ n)
  have hs : s.Nonempty := by
    by_contra h
    have hz : s = ∅ := not_nonempty_iff_eq_empty.mp h
    have : ap A p n = 0 := by change ∑ a ∈ s, A.weight a = 0; rw [hz]; simp
    linarith
  obtain ⟨a, ha, hmax⟩ := s.exists_max_image Prod.snd hs
  have hap : a.1 = p := (mem_filter.mp ha).2.1
  have han : modulus a ∣ n := (mem_filter.mp ha).2.2
  have hcum : cumulative A p a.2 = ap A p n := by
    apply sum_congr
    · ext b
      constructor
      · intro hb
        obtain ⟨hb, hbp, hbj⟩ := mem_filter.mp hb
        refine mem_filter.mpr ⟨hb, hbp, ?_⟩
        simpa only [modulus, hbp, hap] using (Nat.pow_dvd_pow a.1 hbj).trans han
      · intro hb
        exact mem_filter.mpr ⟨(mem_filter.mp hb).1, (mem_filter.mp hb).2.1, hmax b hb⟩
    · intro b hb
      rfl
  have hcpos : 0 < cumulative A a.1 a.2 := by simpa only [hap, hcum] using hp
  let t := A.atoms.filter (fun b => b.1 = p ∧ 0 < cumulative A b.1 b.2 ∧
    levelHeight A b = levelHeight A a)
  have hat : a ∈ t := mem_filter.mpr ⟨(mem_filter.mp ha).1, hap, hcpos, rfl⟩
  obtain ⟨b, hb, hmin⟩ := t.exists_min_image Prod.snd ⟨a, hat⟩
  obtain ⟨hbat, hbp, hbc, hbh⟩ := mem_filter.mp hb
  have hbfirst : b ∈ roundedLevels A := by
    apply mem_filter.mpr
    refine ⟨hbat, hbc, ?_⟩
    intro c hc hcp hcc hch
    exact hmin c (mem_filter.mpr ⟨hc, hcp.trans hbp, hcc, hch.trans hbh⟩)
  refine ⟨b, hbfirst, hbp, ?_, ?_⟩
  · simpa only [modulus, hbp, hap] using (Nat.pow_dvd_pow a.1 (hmin a hat)).trans han
  · have hval : levelValue A b = levelValue A a := by
      dsimp only [levelValue]
      rw [hbh]
    rw [hval]
    have hh := lt_twice_dyadic hcpos (cumulative_le_one A a.1 a.2)
    simpa [levelValue, levelHeight, hap, hcum] using hh

private lemma sum_ap_eq_S0 (A : AtomSystem) (n : ℕ) :
    (∑ p ∈ primes A, ap A p n) = S0 A n := by
  classical
  have hmap : ∀ a ∈ A.atoms.filter (fun a => modulus a ∣ n), a.1 ∈ primes A := by
    intro a ha
    exact mem_image_of_mem Prod.fst (mem_filter.mp ha).1
  change (∑ p ∈ primes A, ∑ a ∈ A.atoms.filter (fun a => a.1 = p ∧ modulus a ∣ n), A.weight a) =
    ∑ a ∈ A.atoms.filter (fun a => modulus a ∣ n), A.weight a
  rw [← sum_fiberwise_of_maps_to hmap A.weight]
  apply sum_congr rfl
  intro p hp
  apply sum_congr
  · ext a
    simp only [mem_filter]
    tauto
  · intro a ha
    rfl

private lemma local_rounding_cost (A : AtomSystem) (m p k : ℕ) (hm : 4096 < m)
    (a : ℕ × ℕ) (ha : a ∈ roundedLevels A) (hap : a.1 = p) (hak : modulus a ∣ k)
    (hnear : ap A p k < 2 * (levelValue A a : ℝ)) :
    ap A p k ≤ 2 * bp A m p k + 32 * Real.log (modulus a) / Real.log m := by
  have hmlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have ht0 : (0 : ℝ) ≤ levelValue A a := (levelValue A a).coe_nonneg
  have hb0 : 0 ≤ bp A m p k := (bpNN A m p k).coe_nonneg
  have hqlog : 0 ≤ Real.log (modulus a : ℝ) := Real.log_natCast_nonneg _
  by_cases hret : modulus a ^ (16 * 2 ^ levelHeight A a) ≤ m
  · have ham : a ∈ retained A m := mem_filter.mpr ⟨ha, hret⟩
    have hb : (levelValue A a : ℝ) ≤ bp A m p k := by
      have hmem : a ∈ (retained A m).filter (fun b => b.1 = p ∧ modulus b ∣ k) :=
        mem_filter.mpr ⟨ham, hap, hak⟩
      have hsup : levelValue A a ≤ bpNN A m p k := Finset.le_sup hmem
      exact_mod_cast hsup
    have hc0 : 0 ≤ 32 * Real.log (modulus a : ℝ) / Real.log (m : ℝ) := by positivity
    linarith
  · have hlarge : m < modulus a ^ (16 * 2 ^ levelHeight A a) := lt_of_not_ge hret
    have hlog := Real.log_lt_log (by exact_mod_cast (by omega : 0 < m))
      (show (m : ℝ) < (modulus a ^ (16 * 2 ^ levelHeight A a) : ℕ) by exact_mod_cast hlarge)
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_pow] at hlog
    norm_num only [Nat.cast_ofNat] at hlog
    have hcancel : (levelValue A a : ℝ) * (2 : ℝ) ^ levelHeight A a = 1 := by
      simp [levelValue, inv_pow]
    have hcost : (levelValue A a : ℝ) * Real.log m ≤ 16 * Real.log (modulus a : ℝ) := by
      calc
        _ ≤ (levelValue A a : ℝ) * (16 * (2 : ℝ) ^ levelHeight A a * Real.log (modulus a : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog.le ht0
        _ = 16 * Real.log (modulus a : ℝ) := by
          calc
            _ = 16 * Real.log (modulus a : ℝ) *
                ((levelValue A a : ℝ) * (2 : ℝ) ^ levelHeight A a) := by ring
            _ = _ := by rw [hcancel]; ring
    have hnearlog := mul_le_mul_of_nonneg_right hnear.le hmlog.le
    have hc : ap A p k ≤ 32 * Real.log (modulus a : ℝ) / Real.log (m : ℝ) := by
      apply (le_div_iff₀ hmlog).2
      nlinarith
    linarith

private lemma S0_le_two_B_add32 (A : AtomSystem) (m k : ℕ) (hm : 4096 < m)
    (hk : 0 < k) (hkm : k ≤ m) : S0 A k ≤ 2 * B A m k + 32 := by
  classical
  have hex (p : ℕ) : ∃ e : ℕ, p ^ e ∣ k ∧
      ap A p k ≤ 2 * bp A m p k + 32 * Real.log (p ^ e : ℕ) / Real.log m := by
    by_cases hp : 0 < ap A p k
    · obtain ⟨a, ha, hap, hak, hnear⟩ := rounded_current_level A p k hp
      refine ⟨a.2, ?_, ?_⟩
      · simpa only [modulus, hap] using hak
      · simpa only [modulus, hap] using local_rounding_cost A m p k hm a ha hap hak hnear
    · refine ⟨0, by simp, ?_⟩
      simp only [pow_zero, Nat.cast_one, Real.log_one, mul_zero, zero_div, add_zero]
      exact (le_of_not_gt hp).trans (mul_nonneg (by norm_num) (bpNN A m p k).coe_nonneg)
  choose e he using hex
  have hprime (p : ℕ) (hp : p ∈ primes A) : Nat.Prime p := by
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hp
    exact (A.prime_of_mem a ha).1
  have hprod : (∏ p ∈ primes A, p ^ e p) ∣ k := by
    apply prod_dvd_of_isRelPrime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp
        (Nat.coprime_pow_primes (e p) (e q) (hprime p hp) (hprime q hq) hpq)
    · intro p hp
      exact (he p).1
  have hprodpos : 0 < ∏ p ∈ primes A, p ^ e p := Nat.pos_of_dvd_of_pos hprod hk
  have hprodle : (∏ p ∈ primes A, p ^ e p) ≤ k := Nat.le_of_dvd hk hprod
  have hlogs : (∑ p ∈ primes A, Real.log (p ^ e p : ℕ)) ≤ Real.log (m : ℝ) := by
    calc
      _ = Real.log (∏ p ∈ primes A, ((p ^ e p : ℕ) : ℝ)) := by
        symm
        apply Real.log_prod
        intro p hp
        exact_mod_cast (pow_pos (hprime p hp).pos (e p)).ne'
      _ = Real.log ((∏ p ∈ primes A, p ^ e p : ℕ) : ℝ) := by rw [Nat.cast_prod]
      _ ≤ Real.log (k : ℝ) :=
        Real.log_le_log (by exact_mod_cast hprodpos) (by exact_mod_cast hprodle)
      _ ≤ Real.log (m : ℝ) := Real.log_le_log (by exact_mod_cast hk) (by exact_mod_cast hkm)
  have hsum := sum_le_sum (s := primes A) (fun p hp => (he p).2)
  have hform : (∑ p ∈ primes A,
      (2 * bp A m p k + 32 * Real.log (p ^ e p : ℕ) / Real.log m)) =
      2 * B A m k + 32 * (∑ p ∈ primes A, Real.log (p ^ e p : ℕ)) / Real.log m := by
    rw [sum_add_distrib, ← mul_sum, ← sum_div, ← mul_sum]
    rfl
  rw [sum_ap_eq_S0, hform] at hsum
  have hmlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hratio : 32 * (∑ p ∈ primes A, Real.log (p ^ e p : ℕ)) / Real.log m ≤ 32 := by
    apply (div_le_iff₀ hmlog).2
    linarith
  linarith

private lemma L_le_two_LB (A : AtomSystem) (m : ℕ) (hm : 4096 < m) : L A m ≤ 2 * LB A m := by
  rw [L, LB, mul_sum]
  apply sum_le_sum
  intro k hk
  have hpoint := S0_le_two_B_add32 A m k hm (by have := (mem_Icc.mp hk).1; omega) (mem_Icc.mp hk).2
  apply max_le
  · have hh := le_max_left (B A m k - 16) 0
    linarith
  · exact mul_nonneg (by norm_num) (le_max_right _ _)

theorem rounding (A : AtomSystem) (m : ℕ) (hm : 4096 < m) (x : ℕ) :
    HB A m ≤ mean A ∧ RB A m x ≤ R A x m ∧ L A m ≤ 2 * LB A m := by
  exact ⟨HB_le_mean A m, RB_le_R A m x, L_le_two_LB A m hm⟩

private lemma carrier_retained_prime (A : AtomSystem) (m : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) : Nat.Prime a.1 ∧ 1 ≤ a.2 :=
  A.prime_of_mem a (mem_filter.mp (mem_filter.mp ha).1).1

private lemma effective_fst_injective (A : AtomSystem) (m n : ℕ) :
    Set.InjOn Prod.fst (effective A m n : Set (ℕ × ℕ)) := by
  intro a ha b hb hab
  obtain ⟨ha, had, ham⟩ := mem_filter.mp ha
  obtain ⟨hb, hbd, hbm⟩ := mem_filter.mp hb
  exact Prod.ext hab (le_antisymm (hbm a ha hab had) (ham b hb hab.symm hbd))

private lemma orderKey_injective (A : AtomSystem) : Function.Injective (orderKey A) := by
  intro a b hab
  exact congrArg (fun k : Lex (ℕ × Lex (ℕ × ℕ)) => ofLex (ofLex k).2) hab

private lemma list_toFinset_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (l : List α) : (l.map f).toFinset = l.toFinset.image f := by
  ext b
  simp

private lemma orderedLevels_toFinset (A : AtomSystem) (s : Finset (ℕ × ℕ)) :
    (orderedLevels A s).toFinset = s := by
  simp [orderedLevels, list_toFinset_map, image_image, orderKey, Function.comp_def]

private lemma orderedLevels_nodup (A : AtomSystem) (s : Finset (ℕ × ℕ)) :
    (orderedLevels A s).Nodup := by
  apply List.Nodup.map_on _ ((s.image (orderKey A)).sort_nodup _)
  intro k hk l hl hkl
  have hk' : k ∈ s.image (orderKey A) := by simpa using hk
  have hl' : l ∈ s.image (orderKey A) := by simpa using hl
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hk'
  obtain ⟨b, hb, rfl⟩ := mem_image.mp hl'
  change a = b at hkl
  rw [hkl]

private lemma map_orderedLevels (A : AtomSystem) (s : Finset (ℕ × ℕ)) :
    (orderedLevels A s).map (orderKey A) = (s.image (orderKey A)).sort := by
  rw [orderedLevels, List.map_map]
  calc
    _ = List.map id ((s.image (orderKey A)).sort (· ≤ ·)) := by
      apply List.map_congr_left
      intro k hk
      have hk' : k ∈ s.image (orderKey A) := by simpa using hk
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hk'
      rfl
    _ = _ := List.map_id _

private lemma orderedLevels_of_list (A : AtomSystem) (l : List (ℕ × ℕ))
    (hnd : l.Nodup) (hord : (l.map (orderKey A)).Pairwise (· ≤ ·)) :
    orderedLevels A l.toFinset = l := by
  apply (orderKey_injective A).list_map
  rw [map_orderedLevels, ← list_toFinset_map]
  exact (List.toFinset_sort (· ≤ ·) (hnd.map (orderKey_injective A))).mpr hord

private lemma modulus_dvd_product_iff (A : AtomSystem) (m : ℕ) (s : Finset (ℕ × ℕ))
    (hs : s ⊆ retained A m) (hinj : Set.InjOn Prod.fst (s : Set (ℕ × ℕ)))
    (b : ℕ × ℕ) (hb : b ∈ retained A m) :
    (modulus b ∣ ∏ a ∈ s, modulus a) ↔ ∃ a ∈ s, a.1 = b.1 ∧ b.2 ≤ a.2 := by
  classical
  have hbp := carrier_retained_prime A m hb
  induction s using Finset.induction_on with
  | empty =>
    have hb1 : 1 < modulus b := hbp.1.one_lt.trans_le (by
      simpa only [modulus, pow_one] using Nat.pow_le_pow_right hbp.1.pos hbp.2)
    simp [ne_of_gt hb1]
  | @insert a s ha ih =>
    have har : a ∈ retained A m := hs (mem_insert_self _ _)
    have hs' : s ⊆ retained A m := fun c hc => hs (mem_insert_of_mem hc)
    have hinj' : Set.InjOn Prod.fst (s : Set (ℕ × ℕ)) :=
      fun c hc d hd hcd => hinj (mem_insert_of_mem hc) (mem_insert_of_mem hd) hcd
    by_cases hab : a.1 = b.1
    · have hcop : Nat.Coprime (modulus b) (∏ c ∈ s, modulus c) := by
        apply Nat.Coprime.prod_right
        intro c hc
        apply Nat.coprime_pow_primes _ _ hbp.1 (carrier_retained_prime A m (hs' hc)).1
        intro hbc
        have hac : a = c := hinj (mem_insert_self _ _) (mem_insert_of_mem hc) (hab.trans hbc)
        exact ha (hac ▸ hc)
      rw [prod_insert ha, hcop.dvd_mul_right]
      have hdvd : modulus b ∣ modulus a ↔ b.2 ≤ a.2 := by
        simpa only [modulus, hab] using Nat.pow_dvd_pow_iff_le_right hbp.1.one_lt
      rw [hdvd]
      constructor
      · intro h
        exact ⟨a, mem_insert_self _ _, hab, h⟩
      · rintro ⟨c, hc, hcb, hbc⟩
        have hca : c = a := hinj hc (mem_insert_self _ _) (hcb.trans hab.symm)
        simpa only [hca] using hbc
    · have hcop : Nat.Coprime (modulus b) (modulus a) :=
        Nat.coprime_pow_primes _ _ hbp.1 (carrier_retained_prime A m har).1 (Ne.symm hab)
      rw [prod_insert ha, hcop.dvd_mul_left]
      constructor
      · intro hdiv
        obtain ⟨c, hc, hcb, hbc⟩ := (ih hs' hinj').mp hdiv
        exact ⟨c, mem_insert_of_mem hc, hcb, hbc⟩
      · rintro ⟨c, hc, hcb, hbc⟩
        apply (ih hs' hinj').mpr
        rcases mem_insert.mp hc with rfl | hc
        · exact (hab hcb).elim
        · exact ⟨c, hc, hcb, hbc⟩

private lemma effective_product (A : AtomSystem) (m : ℕ) (s : Finset (ℕ × ℕ))
    (hs : s ⊆ retained A m) (hinj : Set.InjOn Prod.fst (s : Set (ℕ × ℕ))) :
    effective A m (∏ a ∈ s, modulus a) = s := by
  ext b
  constructor
  · intro hb
    obtain ⟨hb, hbd, hbm⟩ := mem_filter.mp hb
    obtain ⟨a, ha, hab, hba⟩ := (modulus_dvd_product_iff A m s hs hinj b hb).mp hbd
    have hab' : a.2 ≤ b.2 := hbm a (hs ha) hab (dvd_prod_of_mem modulus ha)
    have hbeq : b = a := Prod.ext hab.symm (le_antisymm hba hab')
    simpa only [hbeq] using ha
  · intro hb
    apply mem_filter.mpr
    refine ⟨hs hb, dvd_prod_of_mem modulus hb, ?_⟩
    intro a ha hab had
    obtain ⟨c, hc, hca, hac⟩ := (modulus_dvd_product_iff A m s hs hinj a ha).mp had
    have hcb : c = b := hinj hc hb (hca.trans hab)
    simpa only [hcb] using hac

private lemma prefix_nodup (A : AtomSystem) (m k i : ℕ) :
    (prefixLevels A m k i).Nodup := (orderedLevels_nodup A (effective A m k)).take

private lemma prefix_subset_effective (A : AtomSystem) (m k i : ℕ) :
    (prefixLevels A m k i).toFinset ⊆ effective A m k := by
  intro a ha
  have hamem := List.mem_of_mem_take (List.mem_toFinset.mp ha)
  have hh := List.mem_toFinset.mpr hamem
  change a ∈ (orderedLevels A (effective A m k)).toFinset at hh
  rwa [orderedLevels_toFinset] at hh

private lemma effectiveList_prefix (A : AtomSystem) (m k i : ℕ) :
    effectiveList A m (prefixProd A m k i) = prefixLevels A m k i := by
  let s := (prefixLevels A m k i).toFinset
  have hs : s ⊆ retained A m := fun a ha =>
    (mem_filter.mp (prefix_subset_effective A m k i ha)).1
  have hinj : Set.InjOn Prod.fst (s : Set (ℕ × ℕ)) := fun a ha b hb hab =>
    effective_fst_injective A m k (prefix_subset_effective A m k i ha)
      (prefix_subset_effective A m k i hb) hab
  have hprod : ∏ a ∈ s, modulus a = prefixProd A m k i := List.prod_toFinset modulus (prefix_nodup A m k i)
  have heff : effective A m (prefixProd A m k i) = s := by
    rw [← hprod]
    exact effective_product A m s hs hinj
  rw [effectiveList, heff]
  apply orderedLevels_of_list A _ (prefix_nodup A m k i)
  rw [prefixLevels, effectiveList, List.map_take, map_orderedLevels]
  exact ((effective A m k).image (orderKey A)).pairwise_sort (· ≤ ·) |>.take

private lemma effective_value_eq_bp (A : AtomSystem) (m n : ℕ) (a : ℕ × ℕ)
    (ha : a ∈ effective A m n) : bp A m a.1 n = (levelValue A a : ℝ) := by
  obtain ⟨ha, had, ham⟩ := mem_filter.mp ha
  have hh : bpNN A m a.1 n = levelValue A a := by
    apply le_antisymm
    · apply Finset.sup_le
      intro b hb
      obtain ⟨hb, hbp, hbd⟩ := mem_filter.mp hb
      exact retained_value_mono A m hb ha hbp (ham b hb hbp hbd)
    · exact Finset.le_sup (mem_filter.mpr ⟨ha, rfl, had⟩)
  exact congrArg (fun z : ℝ≥0 => (z : ℝ)) hh

private lemma bp_eq_effective_sum (A : AtomSystem) (m p n : ℕ) :
    bp A m p n = ∑ a ∈ (effective A m n).filter (fun a => a.1 = p), (levelValue A a : ℝ) := by
  classical
  let t := (retained A m).filter (fun a => a.1 = p ∧ modulus a ∣ n)
  by_cases ht : t.Nonempty
  · obtain ⟨a, ha, hmax⟩ := t.exists_max_image Prod.snd ht
    obtain ⟨har, hap, had⟩ := mem_filter.mp ha
    have hae : a ∈ effective A m n := by
      apply mem_filter.mpr
      refine ⟨har, had, ?_⟩
      intro b hb hbp hbd
      exact hmax b (mem_filter.mpr ⟨hb, hbp.trans hap, hbd⟩)
    have hfilter : (effective A m n).filter (fun b => b.1 = p) = {a} := by
      ext b
      constructor
      · intro hb
        exact mem_singleton.mpr (effective_fst_injective A m n (mem_filter.mp hb).1 hae
          ((mem_filter.mp hb).2.trans hap.symm))
      · intro hb
        obtain rfl := mem_singleton.mp hb
        exact mem_filter.mpr ⟨hae, hap⟩
    rw [hfilter, sum_singleton]
    simpa only [hap] using effective_value_eq_bp A m n a hae
  · have ht0 : t = ∅ := not_nonempty_iff_eq_empty.mp ht
    have he0 : (effective A m n).filter (fun a => a.1 = p) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro a ha
      obtain ⟨hae, hap⟩ := mem_filter.mp ha
      obtain ⟨har, had, ham⟩ := mem_filter.mp hae
      exact ht ⟨a, mem_filter.mpr ⟨har, hap, had⟩⟩
    rw [he0, sum_empty]
    change (t.sup (levelValue A) : ℝ≥0) = (0 : ℝ)
    rw [ht0, sup_empty]
    rfl

private lemma B_eq_effectiveList_sum (A : AtomSystem) (m n : ℕ) :
    B A m n = ((effectiveList A m n).map (fun a => (levelValue A a : ℝ))).sum := by
  classical
  have hmap : ∀ a ∈ effective A m n, a.1 ∈ primes A := by
    intro a ha
    exact mem_image_of_mem Prod.fst (rounding_retained_mem_atoms A m (mem_filter.mp ha).1)
  calc
    _ = ∑ p ∈ primes A, ∑ a ∈ (effective A m n).filter (fun a => a.1 = p), (levelValue A a : ℝ) := by
      apply sum_congr rfl
      intro p hp
      exact bp_eq_effective_sum A m p n
    _ = ∑ a ∈ effective A m n, (levelValue A a : ℝ) :=
      sum_fiberwise_of_maps_to hmap (fun a => (levelValue A a : ℝ))
    _ = _ := by
      have hh := List.sum_toFinset (fun a => (levelValue A a : ℝ))
        (orderedLevels_nodup A (effective A m n))
      rw [orderedLevels_toFinset] at hh
      exact hh

private lemma B_prefix_eq_partialMass (A : AtomSystem) (m k i : ℕ) :
    B A m (prefixProd A m k i) = partialMass A m k i := by
  rw [B_eq_effectiveList_sum, effectiveList_prefix]
  rfl

private lemma carrier_witness (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) :
    ∃ k i, k ∈ hot A m ∧ i ∈ Icc 1 (effectiveList A m k).length ∧
      0 < prefixWeight A m k i ∧ prefixProd A m k i = P := by
  obtain ⟨ki, hki, hprod⟩ := mem_image.mp hP
  obtain ⟨k, hk, hki⟩ := mem_biUnion.mp hki
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hki
  exact ⟨k, i, hk, (mem_filter.mp hi).1, (mem_filter.mp hi).2, hprod⟩

private lemma prefix_succ (A : AtomSystem) (m k i : ℕ) (hi : i < (effectiveList A m k).length) :
    prefixLevels A m k (i + 1) = prefixLevels A m k i ++ [(effectiveList A m k)[i]] :=
  List.take_succ_eq_append_getElem hi

private lemma prefix_last (A : AtomSystem) (m k i : ℕ) (hi : i < (effectiveList A m k).length) :
    lastLevel A m (prefixProd A m k (i + 1)) = (effectiveList A m k)[i] := by
  rw [lastLevel, effectiveList_prefix, prefix_succ A m k i hi]
  simp

private lemma partialMass_succ (A : AtomSystem) (m k i : ℕ) (hi : i < (effectiveList A m k).length) :
    partialMass A m k (i + 1) = partialMass A m k i + (levelValue A (effectiveList A m k)[i] : ℝ) := by
  simp only [partialMass, prefix_succ A m k i hi, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, add_zero]

private lemma positive_prefix_mass (A : AtomSystem) (m k i : ℕ)
    (hw : 0 < prefixWeight A m k i) : 2 < partialMass A m k i ∧ partialMass A m k (i - 1) < 3 := by
  have hgap : 0 < min (partialMass A m k i) 3 - max (partialMass A m k (i - 1)) 2 := by
    rcases lt_max_iff.mp hw with h | h
    · exact h
    · exact (lt_irrefl _ h).elim
  constructor
  · linarith [min_le_left (partialMass A m k i) 3, le_max_right (partialMass A m k (i - 1)) 2]
  · linarith [min_le_right (partialMass A m k i) 3, le_max_left (partialMass A m k (i - 1)) 2]

private lemma carrier_mass_range (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) :
    2 < mu A m P ∧ mu A m P < 4 := by
  obtain ⟨k, i, hk, hi, hw, rfl⟩ := carrier_witness A m P hP
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := (mem_Icc.mp hi).1; omega : i ≠ 0)
  have hil : i < (effectiveList A m k).length := by have := (mem_Icc.mp hi).2; omega
  have hh := positive_prefix_mass A m k (i + 1) hw
  have hval : (levelValue A (effectiveList A m k)[i] : ℝ) ≤ 1 := by
    exact_mod_cast (pow_le_one₀ (by positivity : (0 : ℝ≥0) ≤ (2 : ℝ≥0)⁻¹)
      (by norm_num : (2 : ℝ≥0)⁻¹ ≤ 1) : (2 : ℝ≥0)⁻¹ ^ levelHeight A (effectiveList A m k)[i] ≤ 1)
  rw [mu, B_prefix_eq_partialMass]
  refine ⟨hh.1, ?_⟩
  have hsum := partialMass_succ A m k i hil
  simp only [Nat.add_sub_cancel] at hh
  linarith

private lemma carrier_data (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) :
    lastLevel A m P ∈ effective A m P ∧
    P = ∏ b ∈ effective A m P, modulus b ∧
    (∑ b ∈ (effective A m P).erase (lastLevel A m P), (levelValue A b : ℝ)) < 3 ∧
    ∀ b ∈ effective A m P, levelHeight A b ≤ levelHeight A (lastLevel A m P) := by
  classical
  obtain ⟨k, i, hk, hi, hw, rfl⟩ := carrier_witness A m P hP
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := (mem_Icc.mp hi).1; omega : i ≠ 0)
  have hil : i < (effectiveList A m k).length := by have := (mem_Icc.mp hi).2; omega
  let a := (effectiveList A m k)[i]
  let l := prefixLevels A m k i
  have hpre : prefixLevels A m k (i + 1) = l ++ [a] := prefix_succ A m k i hil
  have hlast : lastLevel A m (prefixProd A m k (i + 1)) = a := prefix_last A m k i hil
  have heff : effective A m (prefixProd A m k (i + 1)) = (l ++ [a]).toFinset := by
    have hh := congrArg List.toFinset (effectiveList_prefix A m k (i + 1))
    rw [effectiveList, orderedLevels_toFinset, hpre] at hh
    exact hh
  have hnot : a ∉ l.toFinset := by
    have hnd : (l ++ [a]).Nodup := hpre ▸ prefix_nodup A m k (i + 1)
    intro ha
    exact (List.pairwise_append.mp hnd).2.2 a (List.mem_toFinset.mp ha) a (by simp) rfl
  have hset : effective A m (prefixProd A m k (i + 1)) = insert a l.toFinset := by
    rw [heff]
    ext b
    simp [or_comm]
  have hord : (l ++ [a]).Pairwise (fun b c => orderKey A b ≤ orderKey A c) := by
    rw [← hpre, ← List.pairwise_map, prefixLevels, effectiveList, List.map_take, map_orderedLevels]
    exact ((effective A m k).image (orderKey A)).pairwise_sort (· ≤ ·) |>.take
  rw [hlast]
  refine ⟨by rw [hset]; exact mem_insert_self _ _, ?_, ?_, ?_⟩
  · have hh := List.prod_toFinset modulus (prefix_nodup A m k (i + 1))
    have heff' : effective A m (prefixProd A m k (i + 1)) = (prefixLevels A m k (i + 1)).toFinset := by
      rw [heff, hpre]
    rw [← heff'] at hh
    exact hh.symm
  · rw [hset, erase_insert hnot]
    have hh := List.sum_toFinset (fun b => (levelValue A b : ℝ)) (prefix_nodup A m k i)
    have hp := (positive_prefix_mass A m k (i + 1) hw).2
    simp only [Nat.add_sub_cancel] at hp
    exact hh.trans_lt hp
  · intro b hb
    have hkey : orderKey A b ≤ orderKey A a := by
      rw [hset] at hb
      rcases mem_insert.mp hb with rfl | hb
      · exact le_rfl
      · exact (List.pairwise_append.mp hord).2.2 b (List.mem_toFinset.mp hb) a (by simp)
    exact Prod.Lex.monotone_fst _ _ hkey

/-! Lemma 14.10: finite signed expansion and counts on an arbitrary window. -/

private def windowCount (x m d : ℕ) : ℕ :=
  #((Icc (x + 1) (x + m)).filter (fun n => d ∣ n))

private lemma initialCount (N d : ℕ) : #((Icc 1 N).filter (fun n => d ∣ n)) = N / d := by
  have heq : (Icc 1 N).filter (fun n => d ∣ n) =
      (range N.succ).filter (fun n => n ≠ 0 ∧ d ∣ n) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_range]
    omega
  rw [heq, Nat.card_multiples']

private lemma windowCount_add (x m d : ℕ) : x / d + windowCount x m d = (x + m) / d := by
  have hu : (Icc 1 (x + m)).filter (fun n => d ∣ n) =
      (Icc 1 x).filter (fun n => d ∣ n) ∪
      (Icc (x + 1) (x + m)).filter (fun n => d ∣ n) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_union]
    omega
  have hd : Disjoint ((Icc 1 x).filter (fun n => d ∣ n))
      ((Icc (x + 1) (x + m)).filter (fun n => d ∣ n)) := by
    apply disjoint_left.mpr
    intro n hn hn'
    have h1 := (mem_Icc.mp (mem_filter.mp hn).1).2
    have h2 := (mem_Icc.mp (mem_filter.mp hn').1).1
    omega
  have hh := congrArg Finset.card hu
  rw [card_union_of_disjoint hd, initialCount, initialCount] at hh
  exact hh.symm

private lemma windowCount_lower (x m d : ℕ) : m / d ≤ windowCount x m d := by
  have hh : x / d + m / d ≤ (x + m) / d := Nat.div_add_div_le_add_div
  have hc := windowCount_add x m d
  omega

private lemma windowCount_upper (x m d : ℕ) (hd : 0 < d) :
    (windowCount x m d : ℝ) ≤ (m : ℝ) / d + 1 := by
  have hc := windowCount_add x m d
  have hlo := Nat.div_mul_le_self (x + m) d
  rw [← hc, Nat.add_mul] at hlo
  have hx : x < x / d * d + d := by
    have hh := Nat.mod_add_div x d
    have hr := Nat.mod_lt x hd
    nlinarith
  have hloR : ((x / d : ℕ) : ℝ) * d + (windowCount x m d : ℝ) * d ≤ x + m := by
    exact_mod_cast hlo
  have hxR : (x : ℝ) < ((x / d : ℕ) : ℝ) * d + d := by exact_mod_cast hx
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hh : (windowCount x m d : ℝ) ≤ ((m : ℝ) + d) / d := by
    apply (le_div_iff₀ hdR).2
    linarith
  simpa only [add_div, div_self (ne_of_gt hdR)] using hh

private lemma windowCount_upper_two (x m d : ℕ) (hd : 0 < d) (hdm : d ≤ m) :
    (windowCount x m d : ℝ) ≤ 2 * ((m : ℝ) / d) := by
  have hh := windowCount_upper x m d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hratio : (1 : ℝ) ≤ (m : ℝ) / d := (le_div_iff₀ hdR).2 (by simpa only [one_mul] using (show (d : ℝ) ≤ m by exact_mod_cast hdm))
  linarith

private lemma occurrence_hot (A : AtomSystem) (m : ℕ) {ki : ℕ × ℕ}
    (hki : ki ∈ occurrences A m) : ki.1 ∈ hot A m := by
  obtain ⟨k, hk, hki⟩ := mem_biUnion.mp hki
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hki
  exact hk

private lemma carried_mass_nonneg (A : AtomSystem) (m P : ℕ) : 0 ≤ M A m P := by
  apply sum_nonneg
  intro ki hki
  have hk := occurrence_hot A m (mem_filter.mp hki).1
  have hB : 16 < B A m ki.1 := (mem_filter.mp hk).2
  exact mul_nonneg (by linarith) (le_max_right _ _)

private lemma coefficient_nonneg (A : AtomSystem) (m P : ℕ) : 0 ≤ coefficient A m P :=
  div_nonneg (carried_mass_nonneg A m P) (Nat.cast_nonneg _)

private lemma retained_modulus_pos (A : AtomSystem) (m : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) : 0 < modulus a :=
  pow_pos (carrier_retained_prime A m ha).1.pos _

private lemma retained_log_bound (A : AtomSystem) (m : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) :
    Real.log (modulus a : ℝ) ≤ (levelValue A a : ℝ) / 16 * Real.log (m : ℝ) := by
  have hcut := (mem_filter.mp ha).2
  have hqpos : (0 : ℝ) < modulus a := by exact_mod_cast retained_modulus_pos A m ha
  have hlog := Real.log_le_log (pow_pos hqpos (16 * 2 ^ levelHeight A a))
    (show (modulus a : ℝ) ^ (16 * 2 ^ levelHeight A a) ≤ m by exact_mod_cast hcut)
  rw [Real.log_pow, Nat.cast_mul, Nat.cast_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hcancel : (levelValue A a : ℝ) * (2 : ℝ) ^ levelHeight A a = 1 := by
    simp [levelValue, inv_pow]
  calc
    _ = ((levelValue A a : ℝ) / 16) *
        (16 * (2 : ℝ) ^ levelHeight A a * Real.log (modulus a : ℝ)) := by
      calc
        _ = ((levelValue A a : ℝ) * (2 : ℝ) ^ levelHeight A a) * Real.log (modulus a : ℝ) := by rw [hcancel]; ring
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)

private lemma B_eq_effective_sum (A : AtomSystem) (m n : ℕ) :
    B A m n = ∑ a ∈ effective A m n, (levelValue A a : ℝ) := by
  have hh := List.sum_toFinset (fun a => (levelValue A a : ℝ))
    (orderedLevels_nodup A (effective A m n))
  rw [orderedLevels_toFinset] at hh
  exact (B_eq_effectiveList_sum A m n).trans hh.symm

private lemma carrier_pos (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) : 0 < P := by
  rw [(carrier_data A m P hP).2.1]
  exact prod_pos (fun a ha => retained_modulus_pos A m (mem_filter.mp ha).1)

private lemma carrier_log_bound (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) :
    Real.log (P : ℝ) ≤ mu A m P / 16 * Real.log (m : ℝ) := by
  have hfactor := (carrier_data A m P hP).2.1
  have hlogeq : Real.log (P : ℝ) = ∑ a ∈ effective A m P, Real.log (modulus a : ℝ) := by
    conv_lhs => rw [hfactor, Nat.cast_prod]
    apply Real.log_prod
    intro a ha
    exact_mod_cast (retained_modulus_pos A m (mem_filter.mp ha).1).ne'
  rw [hlogeq]
  calc
    _ ≤ ∑ a ∈ effective A m P, (levelValue A a : ℝ) / 16 * Real.log (m : ℝ) :=
      sum_le_sum (fun a ha => retained_log_bound A m (mem_filter.mp ha).1)
    _ = _ := by
      rw [← sum_mul, ← sum_div, ← B_eq_effective_sum]
      rfl

private lemma carrier_small (A : AtomSystem) (m : ℕ) (hm : 4096 < m)
    (P : ℕ) (hP : P ∈ carriers A m) : (P : ℝ) < (m : ℝ) ^ (1 / 4 : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hPpos : (0 : ℝ) < P := by exact_mod_cast carrier_pos A m P hP
  rw [← Real.log_lt_log_iff hPpos (Real.rpow_pos_of_pos hmR _), Real.log_rpow hmR]
  apply (carrier_log_bound A m P hP).trans_lt
  apply mul_lt_mul_of_pos_right
  · have hh := (carrier_mass_range A m P hP).2
    linarith
  · exact Real.log_pos (by exact_mod_cast (by omega : 1 < m))

private lemma retained_small (A : AtomSystem) (m : ℕ) (hm : 4096 < m)
    (a : ℕ × ℕ) (ha : a ∈ retained A m) : (modulus a : ℝ) ≤ (m : ℝ) ^ (1 / 16 : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hqpos : (0 : ℝ) < modulus a := by exact_mod_cast retained_modulus_pos A m ha
  rw [← Real.log_le_log_iff hqpos (Real.rpow_pos_of_pos hmR _), Real.log_rpow hmR]
  apply (retained_log_bound A m ha).trans
  have hval : (levelValue A a : ℝ) ≤ 1 := by
    exact_mod_cast (pow_le_one₀ (by positivity : (0 : ℝ≥0) ≤ (2 : ℝ≥0)⁻¹)
      (by norm_num : (2 : ℝ≥0)⁻¹ ≤ 1) : (2 : ℝ≥0)⁻¹ ^ levelHeight A a ≤ 1)
  have hmlog : 0 ≤ Real.log (m : ℝ) := Real.log_natCast_nonneg _
  gcongr

private lemma negative_modulus_small (A : AtomSystem) (m : ℕ) (hm : 4096 < m)
    (P : ℕ) (hP : P ∈ carriers A m) (a : ℕ × ℕ) (ha : a ∈ retained A m) :
    ((P * modulus a : ℕ) : ℝ) < (m : ℝ) ^ (5 / 16 : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hqpos : (0 : ℝ) < modulus a := by exact_mod_cast retained_modulus_pos A m ha
  calc
    _ = (P : ℝ) * (modulus a : ℝ) := Nat.cast_mul _ _
    _ < (m : ℝ) ^ (1 / 4 : ℝ) * (modulus a : ℝ) :=
      mul_lt_mul_of_pos_right (carrier_small A m hm P hP) hqpos
    _ ≤ (m : ℝ) ^ (1 / 4 : ℝ) * (m : ℝ) ^ (1 / 16 : ℝ) :=
      mul_le_mul_of_nonneg_left (retained_small A m hm a ha) (Real.rpow_pos_of_pos hmR _).le
    _ = _ := by rw [← Real.rpow_add hmR]; norm_num

private lemma carrier_le_m (A : AtomSystem) (m : ℕ) (hm : 4096 < m)
    (P : ℕ) (hP : P ∈ carriers A m) : P ≤ m := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hpow : (m : ℝ) ^ (1 / 4 : ℝ) ≤ m := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num : (1 / 4 : ℝ) ≤ 1)
  exact_mod_cast (carrier_small A m hm P hP).le.trans hpow

private lemma K_pos (A : AtomSystem) (m : ℕ) (hm : 4096 < m)
    (P : ℕ) (hP : P ∈ carriers A m) : 0 < K m P :=
  Nat.div_pos (carrier_le_m A m hm P hP) (carrier_pos A m P hP)

private lemma quotient_le_two_K (A : AtomSystem) (m : ℕ) (hm : 4096 < m)
    (P : ℕ) (hP : P ∈ carriers A m) : (m : ℝ) / P ≤ 2 * (K m P : ℝ) := by
  have hPpos := carrier_pos A m P hP
  have hKpos := K_pos A m hm P hP
  have hrem : m < m / P * P + P := by
    have hh := Nat.mod_add_div m P
    have hr := Nat.mod_lt m hPpos
    nlinarith
  have hnat : m ≤ 2 * (m / P) * P := by dsimp only [K] at hKpos; nlinarith
  apply (div_le_iff₀ (by exact_mod_cast hPpos : (0 : ℝ) < P)).2
  exact_mod_cast hnat

private lemma esymm_insert {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (x : ι → ℝ) (a : ι) (ha : a ∉ s) (k : ℕ) :
    (∑ t ∈ (insert a s).powersetCard (k + 1), ∏ i ∈ t, x i) =
      (∑ t ∈ s.powersetCard (k + 1), ∏ i ∈ t, x i) +
      x a * ∑ t ∈ s.powersetCard k, ∏ i ∈ t, x i := by
  rw [powersetCard_succ_insert ha, sum_union]
  · congr 1
    rw [sum_image, mul_sum]
    · apply sum_congr rfl
      intro t ht
      exact prod_insert (fun hat => ha ((mem_powersetCard.mp ht).1 hat))
    · intro t ht u hu heq
      have hat : a ∉ t := fun h => ha ((mem_powersetCard.mp ht).1 h)
      have hau : a ∉ u := fun h => ha ((mem_powersetCard.mp hu).1 h)
      simpa [hat, hau] using congrArg (erase · a) heq
  · apply disjoint_left.mpr
    intro t ht ht'
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ht'
    exact ha ((mem_powersetCard.mp ht).1 (mem_insert_self _ _))

 theorem hinge_le_esymm {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1)
    (C : ℕ) :
    max (∑ i ∈ s, x i - C) 0 ≤ ∑ t ∈ s.powersetCard (C + 1), ∏ i ∈ t, x i := by
  classical
  induction s using Finset.induction_on generalizing C with
  | empty =>
    have hempty : (∅ : Finset ι).powersetCard (C + 1) = ∅ :=
      powersetCard_eq_empty.mpr (by simp)
    simp [hempty]
  | @insert a s ha ih =>
    have hxa := hx a (mem_insert_self _ _)
    have hxs : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1 := fun i hi => hx i (mem_insert_of_mem hi)
    have hnonneg (k : ℕ) : 0 ≤ ∑ t ∈ s.powersetCard k, ∏ i ∈ t, x i := by
      apply sum_nonneg
      intro t ht
      exact prod_nonneg (fun i hi => (hxs i ((mem_powersetCard.mp ht).1 hi)).1)
    cases C with
    | zero =>
      simp only [Nat.cast_zero, sub_zero, Nat.zero_add, powersetCard_one, sum_map,
        Function.Embedding.coeFn_mk, prod_singleton]
      exact max_le (le_refl _) (sum_nonneg fun i hi => (hx i hi).1)
    | succ C =>
      rw [sum_insert ha, esymm_insert s x a ha (C + 1)]
      apply max_le
      · have h₁ := (le_max_left _ _).trans (ih hxs (C + 1))
        have h₂ := (le_max_left _ _).trans (ih hxs C)
        calc
          x a + ∑ i ∈ s, x i - (C + 1 : ℕ) =
              (1 - x a) * ((∑ i ∈ s, x i) - (C + 1 : ℕ)) +
              x a * ((∑ i ∈ s, x i) - (C : ℝ)) := by push_cast; ring
          _ ≤ (1 - x a) * (∑ t ∈ s.powersetCard (C + 1 + 1), ∏ i ∈ t, x i) +
              x a * (∑ t ∈ s.powersetCard (C + 1), ∏ i ∈ t, x i) :=
            add_le_add (mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr hxa.2))
              (mul_le_mul_of_nonneg_left h₂ hxa.1)
          _ ≤ _ := by nlinarith [mul_nonneg hxa.1 (hnonneg (C + 1 + 1))]
      · exact add_nonneg (hnonneg _) (mul_nonneg hxa.1 (hnonneg _))

private lemma moment_esymm_insert {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (x : ι → ℝ) (a : ι) (ha : a ∉ s) (k : ℕ) :
    (∑ t ∈ (insert a s).powersetCard (k + 1), ∏ i ∈ t, x i) =
      (∑ t ∈ s.powersetCard (k + 1), ∏ i ∈ t, x i) +
      x a * ∑ t ∈ s.powersetCard k, ∏ i ∈ t, x i := by
  rw [powersetCard_succ_insert ha, sum_union]
  · congr 1
    rw [sum_image, mul_sum]
    · apply sum_congr rfl
      intro t ht
      exact prod_insert (fun hat => ha ((mem_powersetCard.mp ht).1 hat))
    · intro t ht u hu heq
      have hat : a ∉ t := fun h => ha ((mem_powersetCard.mp ht).1 h)
      have hau : a ∉ u := fun h => ha ((mem_powersetCard.mp hu).1 h)
      simpa [hat, hau] using congrArg (erase · a) heq
  · apply disjoint_left.mpr
    intro t ht ht'
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ht'
    exact ha ((mem_powersetCard.mp ht).1 (mem_insert_self _ _))

private lemma factorial_mul_esymm_le {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (r : ℕ) :
    (Nat.factorial r : ℝ) * (∑ t ∈ s.powersetCard r, ∏ i ∈ t, x i) ≤
      (∑ i ∈ s, x i) ^ r := by
  classical
  induction s using Finset.induction_on generalizing r with
  | empty =>
    cases r with
    | zero => simp [powersetCard_zero]
    | succ r =>
      have hempty : (∅ : Finset ι).powersetCard (r + 1) = ∅ :=
        powersetCard_eq_empty.mpr (by simp)
      simp [hempty]
  | @insert a s ha ih =>
    have hxa : 0 ≤ x a := hx a (mem_insert_self _ _)
    have hxs : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (mem_insert_of_mem hi)
    have hs : 0 ≤ ∑ i ∈ s, x i := sum_nonneg hxs
    cases r with
    | zero => simp [powersetCard_zero]
    | succ r =>
      rw [moment_esymm_insert s x a ha r, sum_insert ha]
      calc
        _ = (Nat.factorial (r + 1) : ℝ) *
              (∑ t ∈ s.powersetCard (r + 1), ∏ i ∈ t, x i) +
            ((r + 1 : ℕ) : ℝ) * x a *
              ((Nat.factorial r : ℝ) * (∑ t ∈ s.powersetCard r, ∏ i ∈ t, x i)) := by
          rw [Nat.factorial_succ, Nat.cast_mul]
          ring
        _ ≤ (∑ i ∈ s, x i) ^ (r + 1) +
            ((r + 1 : ℕ) : ℝ) * x a * (∑ i ∈ s, x i) ^ r :=
          add_le_add (ih hxs (r + 1))
            (mul_le_mul_of_nonneg_left (ih hxs r) (by positivity))
        _ ≤ (x a + ∑ i ∈ s, x i) ^ (r + 1) := by
          simpa [mul_assoc, mul_left_comm, mul_comm, add_comm] using
            (pow_add_mul_le_add_pow hs (by positivity : 0 ≤ 2 * (∑ i ∈ s, x i) + x a)
              (r + 1))

private lemma coprime_indicator_sum_le {ι : Type*} (s : Finset ι)
    (q : ι → ℕ) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hcop : ∀ i ∈ s, ∀ k ∈ s, i ≠ k → Nat.Coprime (q i) (q k)) (N : ℕ) :
    (∑ j ∈ Icc 1 N, ∏ i ∈ s, if q i ∣ j then w i else 0) ≤
      (N : ℝ) * ∏ i ∈ s, w i / (q i : ℝ) := by
  classical
  have hdvd (j : ℕ) : (∏ i ∈ s, q i) ∣ j ↔ ∀ i ∈ s, q i ∣ j := by
    constructor
    · intro h i hi
      exact (dvd_prod_of_mem q hi).trans h
    · exact prod_dvd_of_isRelPrime
        (fun i hi k hk hik => Nat.coprime_iff_isRelPrime.mp (hcop i hi k hk hik))
  have hc : #((Icc 1 N).filter (fun j => (∏ i ∈ s, q i) ∣ j)) = N / (∏ i ∈ s, q i) := by
    have heq : (Icc 1 N).filter (fun j => (∏ i ∈ s, q i) ∣ j) =
        (range N.succ).filter (fun j => j ≠ 0 ∧ (∏ i ∈ s, q i) ∣ j) := by
      ext j
      simp only [mem_filter, mem_Icc, mem_range]
      omega
    rw [heq, Nat.card_multiples']
  calc
    _ = ((N / (∏ i ∈ s, q i) : ℕ) : ℝ) * ∏ i ∈ s, w i := by
      simp_rw [prod_ite_zero, ← hdvd]
      rw [← sum_filter, sum_const, nsmul_eq_mul, hc]
    _ ≤ ((N : ℝ) / (∏ i ∈ s, q i : ℕ)) * ∏ i ∈ s, w i :=
      mul_le_mul_of_nonneg_right Nat.cast_div_le (prod_nonneg hw)
    _ = _ := by
      rw [prod_div_distrib, Nat.cast_prod]
      ring

private lemma bp_indicator_expansion (A : AtomSystem) (m p n : ℕ) :
    bp A m p n = ∑ a ∈ (retained A m).filter (fun a => a.1 = p),
      if modulus a ∣ n then increment A m a else 0 := by
  classical
  rw [← increments_telescope, sum_filter, sum_filter]
  apply sum_congr rfl
  intro a ha
  by_cases hp : a.1 = p <;> by_cases hn : modulus a ∣ n <;> simp [hp, hn]

private lemma retained_prime_mean (A : AtomSystem) (m : ℕ) :
    (∑ p ∈ primes A, ∑ a ∈ (retained A m).filter (fun a => a.1 = p),
      increment A m a / (modulus a : ℝ)) = HB A m := by
  have hmap : ∀ a ∈ retained A m, a.1 ∈ primes A := fun a ha =>
    mem_image_of_mem Prod.fst (rounding_retained_mem_atoms A m ha)
  exact sum_fiberwise_of_maps_to hmap (fun a => increment A m a / (modulus a : ℝ))

private lemma retained_product_moment (A : AtomSystem) (m N : ℕ) (T : Finset ℕ)
    (hT : T ⊆ primes A) :
    (∑ j ∈ Icc 1 N, ∏ p ∈ T, bp A m p j) ≤
      (N : ℝ) * ∏ p ∈ T, ∑ a ∈ (retained A m).filter (fun a => a.1 = p),
        increment A m a / (modulus a : ℝ) := by
  classical
  simp_rw [bp_indicator_expansion, prod_sum]
  rw [sum_comm, mul_sum]
  apply sum_le_sum
  intro f hf
  apply coprime_indicator_sum_le
  · intro p hp
    exact increment_nonneg A m (mem_filter.mp (mem_pi.mp hf p.1 p.2)).1
  · intro p hp q hq hpq
    have hpa := mem_filter.mp (mem_pi.mp hf p.1 p.2)
    have hqa := mem_filter.mp (mem_pi.mp hf q.1 q.2)
    have hpp : Nat.Prime p.1 := hpa.2 ▸ (carrier_retained_prime A m hpa.1).1
    have hqp : Nat.Prime q.1 := hqa.2 ▸ (carrier_retained_prime A m hqa.1).1
    dsimp only [modulus]
    rw [hpa.2, hqa.2]
    exact Nat.coprime_pow_primes _ _ hpp hqp (fun he => hpq (Subtype.ext he))

theorem moment_retained (A : AtomSystem) (m N r : ℕ) (hN : 1 ≤ N) (hr : 1 ≤ r) :
    (∑ j ∈ Icc 1 N, ∑ T ∈ (primes A).powersetCard r, ∏ p ∈ T, bp A m p j) ≤
      (N : ℝ) * (HB A m) ^ r / (Nat.factorial r : ℝ) := by
  classical
  let h : ℕ → ℝ := fun p => ∑ a ∈ (retained A m).filter (fun a => a.1 = p),
    increment A m a / (modulus a : ℝ)
  have hh : ∀ p ∈ primes A, 0 ≤ h p := fun p hp =>
    sum_nonneg (fun a ha => div_nonneg (increment_nonneg A m (mem_filter.mp ha).1) (Nat.cast_nonneg _))
  calc
    _ = ∑ T ∈ (primes A).powersetCard r, ∑ j ∈ Icc 1 N, ∏ p ∈ T, bp A m p j := sum_comm
    _ ≤ ∑ T ∈ (primes A).powersetCard r, (N : ℝ) * ∏ p ∈ T, h p := by
      apply sum_le_sum
      intro T hT
      exact retained_product_moment A m N T (mem_powersetCard.mp hT).1
    _ = (N : ℝ) * ∑ T ∈ (primes A).powersetCard r, ∏ p ∈ T, h p := (mul_sum _ _ _).symm
    _ ≤ (N : ℝ) * (∑ p ∈ primes A, h p) ^ r / (Nat.factorial r : ℝ) := by
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < Nat.factorial r)).2
      simpa only [mul_comm] using factorial_mul_esymm_le (primes A) h hh r
    _ = _ := by rw [show (∑ p ∈ primes A, h p) = HB A m from retained_prime_mean A m]

private lemma occurrence_data (A : AtomSystem) (m : ℕ) {ki : ℕ × ℕ}
    (hki : ki ∈ occurrences A m) :
    ki.1 ∈ hot A m ∧ ki.2 ∈ Icc 1 (effectiveList A m ki.1).length ∧
      0 < prefixWeight A m ki.1 ki.2 := by
  obtain ⟨k, hk, hki⟩ := mem_biUnion.mp hki
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hki
  exact ⟨hk, (mem_filter.mp hi).1, (mem_filter.mp hi).2⟩

private lemma occurrence_index (A : AtomSystem) (m : ℕ) {ki : ℕ × ℕ}
    (hki : ki ∈ occurrences A m) :
    (effectiveList A m (prefixProd A m ki.1 ki.2)).length = ki.2 := by
  rw [effectiveList_prefix]
  exact List.length_take_of_le (mem_Icc.mp (occurrence_data A m hki).2.1).2

private lemma occurrence_weight_le (A : AtomSystem) (m : ℕ) {ki : ℕ × ℕ}
    (hki : ki ∈ occurrences A m) :
    prefixWeight A m ki.1 ki.2 ≤ theta A m (prefixProd A m ki.1 ki.2) := by
  obtain ⟨k, i⟩ := ki
  have hi := mem_Icc.mp (occurrence_data A m hki).2.1
  dsimp only [Prod.fst, Prod.snd] at hi
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  subst i
  have hjl : j < (effectiveList A m k).length := by omega
  have hmass := partialMass_succ A m k j hjl
  dsimp only [theta]
  rw [prefix_last A m k j hjl]
  unfold prefixWeight
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  apply max_le
  · have hmin := min_le_left (partialMass A m k (j + 1)) (3 : ℝ)
    have hmax := le_max_left (partialMass A m k j) (2 : ℝ)
    linarith
  · exact NNReal.coe_nonneg _

private lemma occurrence_fst_injective (A : AtomSystem) (m P : ℕ) :
    Set.InjOn Prod.fst ((occurrences A m).filter
      (fun ki => prefixProd A m ki.1 ki.2 = P) : Set (ℕ × ℕ)) := by
  intro ki hki li hli he
  have hi := occurrence_index A m (mem_filter.mp hki).1
  have hj := occurrence_index A m (mem_filter.mp hli).1
  rw [(mem_filter.mp hki).2] at hi
  rw [(mem_filter.mp hli).2] at hj
  exact Prod.ext he (hi.symm.trans hj)

private lemma bp_dvd_mono (A : AtomSystem) (m p : ℕ) {n k : ℕ} (hnk : n ∣ k) :
    bp A m p n ≤ bp A m p k := by
  change (bpNN A m p n : ℝ) ≤ bpNN A m p k
  exact_mod_cast (show bpNN A m p n ≤ bpNN A m p k from
    Finset.sup_mono (fun a ha => mem_filter.mpr ⟨(mem_filter.mp ha).1,
      (mem_filter.mp ha).2.1, (mem_filter.mp ha).2.2.trans hnk⟩))

private lemma B_dvd_mono (A : AtomSystem) (m : ℕ) {n k : ℕ} (hnk : n ∣ k) :
    B A m n ≤ B A m k := sum_le_sum (fun p hp => bp_dvd_mono A m p hnk)

private lemma prime_dvd_carrier (A : AtomSystem) (m P p : ℕ) (hP : P ∈ carriers A m)
    (hp : Nat.Prime p) : p ∣ P ↔ ∃ a ∈ effective A m P, a.1 = p := by
  conv_lhs => rw [(carrier_data A m P hP).2.1]
  rw [hp.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨a, ha, hpa⟩
    have hap := (carrier_retained_prime A m (mem_filter.mp ha).1).1
    exact ⟨a, ha, ((Nat.prime_dvd_prime_iff_eq hp hap).mp (hp.dvd_of_dvd_pow hpa)).symm⟩
  · rintro ⟨a, ha, hap⟩
    refine ⟨a, ha, ?_⟩
    have hj := (carrier_retained_prime A m (mem_filter.mp ha).1).2
    dsimp only [modulus]
    rw [hap]
    exact dvd_pow_self p (by omega : a.2 ≠ 0)

private lemma effective_prefix_subset (A : AtomSystem) (m k i : ℕ) :
    effective A m (prefixProd A m k i) ⊆ effective A m k := by
  have he := congrArg List.toFinset (effectiveList_prefix A m k i)
  rw [effectiveList, orderedLevels_toFinset] at he
  rw [he]
  exact prefix_subset_effective A m k i

private lemma prefix_dvd (A : AtomSystem) (m k i : ℕ) : prefixProd A m k i ∣ k := by
  have he := congrArg List.toFinset (effectiveList_prefix A m k i)
  rw [effectiveList, orderedLevels_toFinset] at he
  have hh := List.prod_toFinset modulus (prefix_nodup A m k i)
  change (∏ a ∈ (prefixLevels A m k i).toFinset, modulus a) = prefixProd A m k i at hh
  rw [← hh]
  apply prod_dvd_of_isRelPrime
  · intro a ha b hb hab
    have hae := prefix_subset_effective A m k i ha
    have hbe := prefix_subset_effective A m k i hb
    apply Nat.coprime_iff_isRelPrime.mp
    exact Nat.coprime_pow_primes _ _
      (carrier_retained_prime A m (mem_filter.mp hae).1).1
      (carrier_retained_prime A m (mem_filter.mp hbe).1).1
      (fun hp => hab (effective_fst_injective A m k hae hbe hp))
  · intro a ha
    exact (mem_filter.mp (prefix_subset_effective A m k i ha)).2.1

private lemma bp_on_prefix_prime (A : AtomSystem) (m : ℕ) {ki : ℕ × ℕ}
    (hki : ki ∈ occurrences A m) (p : ℕ) (hp : Nat.Prime p)
    (hpP : p ∣ prefixProd A m ki.1 ki.2) :
    bp A m p ki.1 = bp A m p (prefixProd A m ki.1 ki.2) := by
  have hP : prefixProd A m ki.1 ki.2 ∈ carriers A m := mem_image_of_mem _ hki
  obtain ⟨a, ha, hap⟩ := (prime_dvd_carrier A m _ p hP hp).mp hpP
  rw [← hap, effective_value_eq_bp A m ki.1 a (effective_prefix_subset A m ki.1 ki.2 ha),
    effective_value_eq_bp A m _ a ha]

private lemma bp_zero_of_not_dvd (A : AtomSystem) (m p n : ℕ) (hpn : ¬ p ∣ n) :
    bp A m p n = 0 := by
  have he : (retained A m).filter (fun a => a.1 = p ∧ modulus a ∣ n) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro a ha
    obtain ⟨har, hap, han⟩ := mem_filter.mp ha
    have hj := (carrier_retained_prime A m har).2
    have hpq : p ∣ modulus a := by
      dsimp only [modulus]
      rw [hap]
      exact dvd_pow_self p (by omega : a.2 ≠ 0)
    exact hpn (hpq.trans han)
  norm_num [bp, bpNN, he]

private lemma bp_remove_coprime (A : AtomSystem) (m P p j : ℕ) (hpP : ¬ p ∣ P) :
    bp A m p (P * j) = bp A m p j := by
  have he : (retained A m).filter (fun a => a.1 = p ∧ modulus a ∣ P * j) =
      (retained A m).filter (fun a => a.1 = p ∧ modulus a ∣ j) := by
    ext a
    simp only [mem_filter]
    constructor
    · rintro ⟨ha, hap, had⟩
      have hc : Nat.Coprime (modulus a) P :=
        ((carrier_retained_prime A m ha).1.coprime_iff_not_dvd.mpr (hap ▸ hpP)).pow_left _
      exact ⟨ha, hap, hc.dvd_mul_left.mp had⟩
    · rintro ⟨ha, hap, had⟩
      exact ⟨ha, hap, had.trans (dvd_mul_left j P)⟩
  simp only [bp, bpNN, he]

private lemma B_occurrence_split (A : AtomSystem) (m : ℕ) {ki : ℕ × ℕ}
    (hki : ki ∈ occurrences A m) :
    B A m ki.1 = mu A m (prefixProd A m ki.1 ki.2) +
      ∑ p ∈ (primes A).filter (fun p => ¬ p ∣ prefixProd A m ki.1 ki.2),
        bp A m p (ki.1 / prefixProd A m ki.1 ki.2) := by
  classical
  let P := prefixProd A m ki.1 ki.2
  have hdiv : P ∣ ki.1 := prefix_dvd A m ki.1 ki.2
  have hk : P * (ki.1 / P) = ki.1 := Nat.mul_div_cancel' hdiv
  have hin : (∑ p ∈ (primes A).filter (fun p => p ∣ P), bp A m p ki.1) = mu A m P := by
    calc
      _ = ∑ p ∈ (primes A).filter (fun p => p ∣ P), bp A m p P := by
        apply sum_congr rfl
        intro p hp
        obtain ⟨a, ha, hap⟩ := mem_image.mp (mem_filter.mp hp).1
        have hprime : Nat.Prime p := hap ▸ (A.prime_of_mem a ha).1
        exact bp_on_prefix_prime A m hki p hprime (mem_filter.mp hp).2
      _ = _ := by
        apply sum_subset (filter_subset _ _)
        intro p hp hn
        exact bp_zero_of_not_dvd A m p P (fun h => hn (mem_filter.mpr ⟨hp, h⟩))
  calc
    _ = (∑ p ∈ (primes A).filter (fun p => p ∣ P), bp A m p ki.1) +
        ∑ p ∈ (primes A).filter (fun p => ¬ p ∣ P), bp A m p ki.1 :=
      (sum_filter_add_sum_filter_not _ _ _).symm
    _ = _ := by
      rw [hin]
      congr 1
      apply sum_congr rfl
      intro p hp
      change bp A m p ki.1 = bp A m p (ki.1 / P)
      conv_lhs => rw [← hk]
      exact bp_remove_coprime A m P p _ (mem_filter.mp hp).2

private lemma outside_value_le_theta (A : AtomSystem) (m : ℕ) {ki : ℕ × ℕ}
    (hki : ki ∈ occurrences A m) {a : ℕ × ℕ} (ha : a ∈ effective A m ki.1)
    (haP : ¬ a.1 ∣ prefixProd A m ki.1 ki.2) :
    (levelValue A a : ℝ) ≤ theta A m (prefixProd A m ki.1 ki.2) := by
  let P := prefixProd A m ki.1 ki.2
  let l := effectiveList A m ki.1
  have hP : P ∈ carriers A m := mem_image_of_mem _ hki
  have hpre : (prefixLevels A m ki.1 ki.2).toFinset = effective A m P := by
    have he := congrArg List.toFinset (effectiveList_prefix A m ki.1 ki.2)
    rw [effectiveList, orderedLevels_toFinset] at he
    exact he.symm
  have hnot : a ∉ prefixLevels A m ki.1 ki.2 := by
    intro hh
    have he : a ∈ effective A m P := hpre ▸ List.mem_toFinset.mpr hh
    exact haP ((prime_dvd_carrier A m P a.1 hP (carrier_retained_prime A m (mem_filter.mp ha).1).1).mpr ⟨a, he, rfl⟩)
  have hal : a ∈ l := by
    apply List.mem_toFinset.mp
    simpa only [l, effectiveList, orderedLevels_toFinset] using ha
  have hadrop : a ∈ l.drop ki.2 := by
    have hh : a ∈ l.take ki.2 ++ l.drop ki.2 := by rw [List.take_append_drop]; exact hal
    exact (List.mem_append.mp hh).resolve_left hnot
  have hlast : lastLevel A m P ∈ l.take ki.2 := by
    apply List.mem_toFinset.mp
    rw [show l.take ki.2 = prefixLevels A m ki.1 ki.2 from rfl, hpre]
    exact (carrier_data A m P hP).1
  have hord : l.Pairwise (fun a b => orderKey A a ≤ orderKey A b) := by
    have hh : (l.map (orderKey A)).Pairwise (· ≤ ·) := by
      rw [show l = orderedLevels A (effective A m ki.1) from rfl, map_orderedLevels]
      exact pairwise_sort _ _
    simpa only [List.pairwise_map] using hh
  rw [← List.take_append_drop ki.2 l] at hord
  have hkey := (List.pairwise_append.mp hord).2.2 _ hlast _ hadrop
  have hheight : levelHeight A (lastLevel A m P) ≤ levelHeight A a := Prod.Lex.monotone_fst _ _ hkey
  exact_mod_cast (pow_le_pow_of_le_one (by positivity : (0 : ℝ≥0) ≤ (2 : ℝ≥0)⁻¹)
    (by norm_num : (2 : ℝ≥0)⁻¹ ≤ 1) hheight)

private lemma bp_outside_le_theta (A : AtomSystem) (m : ℕ) {ki : ℕ × ℕ}
    (hki : ki ∈ occurrences A m) (p : ℕ) (hpP : ¬ p ∣ prefixProd A m ki.1 ki.2) :
    bp A m p (ki.1 / prefixProd A m ki.1 ki.2) ≤ theta A m (prefixProd A m ki.1 ki.2) := by
  classical
  have hdiv := prefix_dvd A m ki.1 ki.2
  have hk := Nat.mul_div_cancel' hdiv
  rw [← bp_remove_coprime A m _ p _ hpP, hk]
  by_cases hh : ((effective A m ki.1).filter (fun a => a.1 = p)).Nonempty
  · obtain ⟨a, ha⟩ := hh
    rw [← (mem_filter.mp ha).2, effective_value_eq_bp A m ki.1 a (mem_filter.mp ha).1]
    exact outside_value_le_theta A m hki (mem_filter.mp ha).1 ((mem_filter.mp ha).2 ▸ hpP)
  · rw [bp_eq_effective_sum, not_nonempty_iff_eq_empty.mp hh, sum_empty]
    exact NNReal.coe_nonneg _

private lemma scaled_hinge {ι : Type*} (s : Finset ι) (x : ι → ℝ) (θ : ℝ)
    (hθ : 0 < θ) (hx : ∀ p ∈ s, 0 ≤ x p ∧ x p ≤ θ) (C : ℕ) :
    max ((∑ p ∈ s, x p) - (C : ℝ) * θ) 0 ≤
      θ ^ ((1 : ℤ) - ((C + 1 : ℕ) : ℤ)) * ∑ T ∈ s.powersetCard (C + 1), ∏ p ∈ T, x p := by
  have hn : ∀ p ∈ s, 0 ≤ x p / θ ∧ x p / θ ≤ 1 := by
    intro p hp
    exact ⟨div_nonneg (hx p hp).1 hθ.le, (div_le_one hθ).2 (hx p hp).2⟩
  calc
    _ = θ * max ((∑ p ∈ s, x p / θ) - (C : ℝ)) 0 := by
      rw [mul_max_of_nonneg _ _ hθ.le, mul_zero, ← sum_div]
      congr 1
      field_simp
      <;> ring
    _ ≤ θ * ∑ T ∈ s.powersetCard (C + 1), ∏ p ∈ T, (x p / θ) :=
      mul_le_mul_of_nonneg_left (hinge_le_esymm s (fun p => x p / θ) hn C) hθ.le
    _ = _ := by
      rw [zpow_sub₀ hθ.ne', zpow_one, zpow_natCast, mul_sum, mul_sum]
      apply sum_congr rfl
      intro T hT
      rw [prod_div_distrib, prod_const, (mem_powersetCard.mp hT).2]
      ring

private lemma occurrence_mass_bound (A : AtomSystem) (m : ℕ) {ki : ℕ × ℕ}
    (hki : ki ∈ occurrences A m) :
    (B A m ki.1 - 16) * prefixWeight A m ki.1 ki.2 ≤
      (theta A m (prefixProd A m ki.1 ki.2)) ^
        ((2 : ℤ) - (momentOrder (levelHeight A (lastLevel A m (prefixProd A m ki.1 ki.2))) : ℤ)) *
      ∑ T ∈ (primes A).powersetCard (momentOrder (levelHeight A (lastLevel A m (prefixProd A m ki.1 ki.2)))),
        ∏ p ∈ T, bp A m p (ki.1 / prefixProd A m ki.1 ki.2) := by
  classical
  let P := prefixProd A m ki.1 ki.2
  let θ := theta A m P
  let h := levelHeight A (lastLevel A m P)
  let C := 12 * 2 ^ h
  let j := ki.1 / P
  let s := (primes A).filter (fun p => ¬ p ∣ P)
  have hP : P ∈ carriers A m := mem_image_of_mem _ hki
  have hθ : 0 < θ := by dsimp [θ, theta, levelValue]; positivity
  have hC : (C : ℝ) * θ = 12 := by
    simp [C, θ, theta, levelValue, h, inv_pow, mul_assoc]
  have hB0 : 0 ≤ B A m ki.1 - 16 := by
    have hh := (mem_filter.mp (occurrence_data A m hki).1).2
    linarith
  have hsplit : B A m ki.1 = mu A m P + ∑ p ∈ s, bp A m p j := B_occurrence_split A m hki
  have hmu := (carrier_mass_range A m P hP).2
  have hh : B A m ki.1 - 16 ≤
      θ ^ ((1 : ℤ) - ((C + 1 : ℕ) : ℤ)) * ∑ T ∈ s.powersetCard (C + 1), ∏ p ∈ T, bp A m p j := by
    apply le_trans _ (scaled_hinge s (fun p => bp A m p j) θ hθ
      (fun p hp => ⟨NNReal.coe_nonneg _, bp_outside_le_theta A m hki p (mem_filter.mp hp).2⟩) C)
    rw [hC]
    exact (show B A m ki.1 - 16 ≤ (∑ p ∈ s, bp A m p j) - 12 by linarith).trans (le_max_left _ _)
  have hsub : s.powersetCard (C + 1) ⊆ (primes A).powersetCard (C + 1) := by
    intro T hT
    exact mem_powersetCard.mpr ⟨(mem_powersetCard.mp hT).1.trans (filter_subset _ _), (mem_powersetCard.mp hT).2⟩
  have hes : (∑ T ∈ s.powersetCard (C + 1), ∏ p ∈ T, bp A m p j) ≤
      ∑ T ∈ (primes A).powersetCard (C + 1), ∏ p ∈ T, bp A m p j := by
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro T hT hn
    exact prod_nonneg (fun p hp => NNReal.coe_nonneg _)
  have hpow : θ ^ ((1 : ℤ) - ((C + 1 : ℕ) : ℤ)) * θ =
      θ ^ ((2 : ℤ) - ((C + 1 : ℕ) : ℤ)) := by
    calc
      _ = θ ^ ((1 : ℤ) - ((C + 1 : ℕ) : ℤ)) * θ ^ (1 : ℤ) := by rw [zpow_one]
      _ = θ ^ (((1 : ℤ) - ((C + 1 : ℕ) : ℤ)) + 1) := (zpow_add₀ hθ.ne' _ _).symm
      _ = _ := by congr 1; omega
  calc
    _ ≤ (B A m ki.1 - 16) * θ := mul_le_mul_of_nonneg_left (occurrence_weight_le A m hki) hB0
    _ ≤ (θ ^ ((1 : ℤ) - ((C + 1 : ℕ) : ℤ)) *
        ∑ T ∈ s.powersetCard (C + 1), ∏ p ∈ T, bp A m p j) * θ := mul_le_mul_of_nonneg_right hh hθ.le
    _ = θ ^ ((2 : ℤ) - ((C + 1 : ℕ) : ℤ)) *
        ∑ T ∈ s.powersetCard (C + 1), ∏ p ∈ T, bp A m p j := by rw [mul_right_comm, hpow]
    _ ≤ _ := mul_le_mul_of_nonneg_left hes (zpow_nonneg hθ.le _)

private lemma M_le_epsilon_K (A : AtomSystem) (m : ℕ) (hm : 4096 < m)
    (P : ℕ) (hP : P ∈ carriers A m) :
    M A m P ≤ epsilon (HB A m) (levelHeight A (lastLevel A m P)) * (K m P : ℝ) := by
  classical
  let h := levelHeight A (lastLevel A m P)
  let r := momentOrder h
  let θ := theta A m P
  let z : ℤ := 2 - (r : ℤ)
  let e : ℕ → ℝ := fun j => ∑ T ∈ (primes A).powersetCard r, ∏ p ∈ T, bp A m p j
  let s := (occurrences A m).filter (fun ki => prefixProd A m ki.1 ki.2 = P)
  let f : ℕ × ℕ → ℕ := fun ki => ki.1 / P
  have hθ : 0 < θ := by dsimp [θ, theta, levelValue]; positivity
  have hdiv (ki : ℕ × ℕ) (hki : ki ∈ s) : P ∣ ki.1 := by
    have hh := prefix_dvd A m ki.1 ki.2
    rwa [(mem_filter.mp hki).2] at hh
  have hmap : ∀ ki ∈ s, f ki ∈ Icc 1 (K m P) := by
    intro ki hki
    have hk := mem_Icc.mp (mem_filter.mp (occurrence_data A m (mem_filter.mp hki).1).1).1
    have heq : P * f ki = ki.1 := Nat.mul_div_cancel' (hdiv ki hki)
    apply mem_Icc.mpr
    constructor
    · have hfpos : f ki ≠ 0 := by intro hh; rw [hh, mul_zero] at heq; omega
      omega
    · exact Nat.div_le_div_right hk.2
  have hinj : Set.InjOn f (s : Set (ℕ × ℕ)) := by
    intro ki hki li hli he
    apply occurrence_fst_injective A m P hki hli
    calc
      ki.1 = P * f ki := (Nat.mul_div_cancel' (hdiv ki hki)).symm
      _ = P * f li := congrArg (P * ·) he
      _ = li.1 := Nat.mul_div_cancel' (hdiv li hli)
  have he0 (j : ℕ) : 0 ≤ e j :=
    sum_nonneg (fun T hT => prod_nonneg (fun p hp => NNReal.coe_nonneg _))
  have hθeq : θ = (2 : ℝ)⁻¹ ^ h := by simp [θ, theta, levelValue, h]
  calc
    _ ≤ ∑ ki ∈ s, θ ^ z * e (f ki) := by
      apply sum_le_sum
      intro ki hki
      have hh := occurrence_mass_bound A m (mem_filter.mp hki).1
      rw [(mem_filter.mp hki).2] at hh
      exact hh
    _ = θ ^ z * ∑ ki ∈ s, e (f ki) := (mul_sum _ _ _).symm
    _ = θ ^ z * ∑ j ∈ s.image f, e j := by rw [sum_image hinj]
    _ ≤ θ ^ z * ∑ j ∈ Icc 1 (K m P), e j := by
      apply mul_le_mul_of_nonneg_left _ (zpow_nonneg hθ.le _)
      exact sum_le_sum_of_subset_of_nonneg (image_subset_iff.mpr hmap) (fun j hj hn => he0 j)
    _ ≤ θ ^ z * ((K m P : ℝ) * (HB A m) ^ r / (Nat.factorial r : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (zpow_nonneg hθ.le _)
      exact moment_retained A m (K m P) r (K_pos A m hm P hP) (by dsimp [r, momentOrder]; omega)
    _ = _ := by
      rw [hθeq]
      dsimp only [epsilon, z, r, h]
      ring

theorem carried_mass (A : AtomSystem) (m : ℕ) (hm : 4096 < m)
    (P : ℕ) (hP : P ∈ carriers A m) :
    (P : ℝ) < (m : ℝ) ^ (1 / 4 : ℝ) ∧ 1 ≤ K m P ∧
      M A m P ≤ epsilon (HB A m) (levelHeight A (lastLevel A m P)) * ((m : ℝ) / P) ∧
      coefficient A m P ≤ 2 * epsilon (HB A m) (levelHeight A (lastLevel A m P)) := by
  have hM := M_le_epsilon_K A m hm P hP
  have hHB : 0 ≤ HB A m := sum_nonneg (fun a ha =>
    div_nonneg (increment_nonneg A m ha) (Nat.cast_nonneg _))
  have heps : 0 ≤ epsilon (HB A m) (levelHeight A (lastLevel A m P)) := by
    unfold epsilon
    positivity
  have hK : (0 : ℝ) < K m P := by exact_mod_cast K_pos A m hm P hP
  refine ⟨carrier_small A m hm P hP, K_pos A m hm P hP, ?_, ?_⟩
  · exact hM.trans (mul_le_mul_of_nonneg_left Nat.cast_div_le heps)
  · have hc : coefficient A m P ≤ epsilon (HB A m) (levelHeight A (lastLevel A m P)) :=
      (div_le_iff₀ hK).2 hM
    linarith


private lemma retained_mem_atoms (A : AtomSystem) (m : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) : a ∈ A.atoms :=
  (mem_filter.mp (mem_filter.mp ha).1).1

private lemma retained_height_injective (A : AtomSystem) (m p : ℕ) :
    Set.InjOn (levelHeight A) {a | a ∈ retained A m ∧ a.1 = p} := by
  intro a ha b hb hab
  have ha' := (mem_filter.mp (mem_filter.mp ha.1).1).2
  have hb' := (mem_filter.mp (mem_filter.mp hb.1).1).2
  apply Prod.ext (ha.2.trans hb.2.symm)
  exact le_antisymm
    (ha'.2 b (retained_mem_atoms A m hb.1) (hb.2.trans ha.2.symm) hb'.1 hab.symm)
    (hb'.2 a (retained_mem_atoms A m ha.1) (ha.2.trans hb.2.symm) ha'.1 hab)

private lemma finite_dyadic_sum_le_twice_sup {ι : Type*} (s : Finset ι) (h : ι → ℕ)
    (hinj : Set.InjOn h (s : Set ι)) :
    (∑ a ∈ s, (2 : ℝ)⁻¹ ^ h a) ≤
      2 * (s.sup (fun a => (2 : ℝ≥0)⁻¹ ^ h a) : ℝ≥0) := by
  classical
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  let t := s.image h
  have ht : t.Nonempty := hs.image h
  let j := t.min' ht
  have hj : j ∈ t := min'_mem t ht
  have hmin (i : ℕ) (hi : i ∈ t) : j ≤ i := min'_le t i hi
  have htail : Summable (fun i : ℕ => if j ≤ i then (2 : ℝ)⁻¹ ^ i else 0) := by
    simpa only [← Set.piecewise_eq_indicator, one_div] using!
      summable_geometric_two.indicator {i | j ≤ i}
  calc
    _ = ∑ i ∈ t, (2 : ℝ)⁻¹ ^ i := (sum_image hinj).symm
    _ = ∑ i ∈ t, if j ≤ i then (2 : ℝ)⁻¹ ^ i else 0 := by
      apply sum_congr rfl
      intro i hi
      rw [if_pos (hmin i hi)]
    _ ≤ ∑' i : ℕ, if j ≤ i then (2 : ℝ)⁻¹ ^ i else 0 :=
      htail.sum_le_tsum t (fun i hi => by positivity)
    _ = 2 * (2 : ℝ)⁻¹ ^ j := tsum_geometric_inv_two_ge j
    _ ≤ _ := by
      obtain ⟨a, ha, haj⟩ := mem_image.mp hj
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      rw [← haj]
      exact_mod_cast (le_sup (f := fun a => (2 : ℝ≥0)⁻¹ ^ h a) ha)

theorem values_at_point (A : AtomSystem) (m n : ℕ) :
    (∑ a ∈ (retained A m).filter (fun a => modulus a ∣ n), (levelValue A a : ℝ)) ≤
      2 * B A m n := by
  classical
  have hmap : ∀ a ∈ (retained A m).filter (fun a => modulus a ∣ n), a.1 ∈ primes A := by
    intro a ha
    exact mem_image_of_mem Prod.fst (retained_mem_atoms A m (mem_filter.mp ha).1)
  rw [← sum_fiberwise_of_maps_to hmap (fun a => (levelValue A a : ℝ)), B, mul_sum]
  apply sum_le_sum
  intro p hp
  have hfilter : ((retained A m).filter (fun a => modulus a ∣ n)).filter (fun a => a.1 = p) =
      (retained A m).filter (fun a => a.1 = p ∧ modulus a ∣ n) := by
    ext a
    simp only [mem_filter]
    tauto
  rw [hfilter]
  have hinj : Set.InjOn (levelHeight A)
      ((retained A m).filter (fun a => a.1 = p ∧ modulus a ∣ n) : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    exact retained_height_injective A m p
      ⟨(mem_filter.mp ha).1, (mem_filter.mp ha).2.1⟩
      ⟨(mem_filter.mp hb).1, (mem_filter.mp hb).2.1⟩ hab
  have hfun : levelValue A = fun a => (2 : ℝ≥0)⁻¹ ^ levelHeight A a := rfl
  simpa only [bp, bpNN, hfun, NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat] using
    finite_dyadic_sum_le_twice_sup
      ((retained A m).filter (fun a => a.1 = p ∧ modulus a ∣ n)) (levelHeight A) hinj

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


private def selectedAt (s : Finset (ℕ × ℕ)) (p : ℕ) : Option (ℕ × ℕ) :=
  if (s.filter (fun a => a.1 = p)).Nonempty then
    some (p, (s.filter (fun a => a.1 = p)).sup Prod.snd) else none

private lemma selectedAt_some_iff (s : Finset (ℕ × ℕ))
    (hinj : Set.InjOn Prod.fst (s : Set (ℕ × ℕ))) (p : ℕ) (b : ℕ × ℕ) :
    selectedAt s p = some b ↔ b ∈ s ∧ b.1 = p := by
  classical
  by_cases ht : (s.filter (fun a => a.1 = p)).Nonempty
  · obtain ⟨a, ha⟩ := ht
    have hap := (mem_filter.mp ha).2
    have has := (mem_filter.mp ha).1
    have hf : s.filter (fun a => a.1 = p) = {a} := by
      ext c
      constructor
      · intro hc
        exact mem_singleton.mpr (hinj (mem_filter.mp hc).1 has ((mem_filter.mp hc).2.trans hap.symm))
      · intro hc
        obtain rfl := mem_singleton.mp hc
        exact ha
    have hsel : selectedAt s p = some a := by
      rw [selectedAt, hf]
      simp only [singleton_nonempty, if_pos, sup_singleton]
      rw [← hap]
    constructor
    · intro hb
      have hab : a = b := Option.some.inj (hsel.symm.trans hb)
      simpa only [hab] using And.intro has hap
    · rintro ⟨hb, hbp⟩
      have hba : b = a := hinj hb has (hbp.trans hap.symm)
      simpa only [hba] using hsel
  · rw [selectedAt, if_neg ht]
    constructor
    · intro h
      cases h
    · rintro ⟨hb, hbp⟩
      exact (ht ⟨b, mem_filter.mpr ⟨hb, hbp⟩⟩).elim

private lemma selectedAt_prod (P : Finset ℕ) (s : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    (hinj : Set.InjOn Prod.fst (s : Set (ℕ × ℕ))) (hs : ∀ a ∈ s, a.1 ∈ P) :
    (∏ p ∈ P, (selectedAt s p).elim 1 w) = ∏ a ∈ s, w a := by
  classical
  rw [← prod_fiberwise_of_maps_to hs w]
  apply prod_congr rfl
  intro p hp
  by_cases ht : (s.filter (fun a => a.1 = p)).Nonempty
  · obtain ⟨a, ha⟩ := ht
    have has := (mem_filter.mp ha).1
    have hap := (mem_filter.mp ha).2
    have hf : s.filter (fun a => a.1 = p) = {a} := by
      ext b
      constructor
      · intro hb
        exact mem_singleton.mpr (hinj (mem_filter.mp hb).1 has ((mem_filter.mp hb).2.trans hap.symm))
      · intro hb
        obtain rfl := mem_singleton.mp hb
        exact ha
    rw [(selectedAt_some_iff s hinj p a).mpr ⟨has, hap⟩, hf]
    simp
  · have hf := not_nonempty_iff_eq_empty.mp ht
    rw [selectedAt, if_neg ht, hf]
    simp

private lemma weighted_subset_family_bound (P : Finset ℕ) (S : ℕ → Finset (ℕ × ℕ))
    (w : ℕ × ℕ → ℝ) (C : Finset (Finset (ℕ × ℕ)))
    (hC : ∀ t ∈ C, Set.InjOn Prod.fst (t : Set (ℕ × ℕ)) ∧
      ∀ a ∈ t, a.1 ∈ P ∧ a ∈ S a.1)
    (hw : ∀ p ∈ P, ∀ a ∈ S p, 0 ≤ w a) :
    (∑ t ∈ C, ∏ a ∈ t, w a) ≤ ∏ p ∈ P, (1 + ∑ a ∈ S p, w a) := by
  classical
  let opts (p : ℕ) := insert none ((S p).image some)
  let enc (t : Finset (ℕ × ℕ)) : ∀ p ∈ P, Option (ℕ × ℕ) := fun p _ => selectedAt t p
  have henc (t : Finset (ℕ × ℕ)) (ht : t ∈ C) : enc t ∈ P.pi opts := by
    apply mem_pi.mpr
    intro p hp
    change selectedAt t p ∈ insert none ((S p).image some)
    cases he : selectedAt t p with
    | none => exact mem_insert_self _ _
    | some a =>
      obtain ⟨hat, hap⟩ := (selectedAt_some_iff t (hC t ht).1 p a).mp he
      apply mem_insert_of_mem
      apply mem_image_of_mem
      simpa only [hap] using (hC t ht).2 a hat |>.2
  have hinj : Set.InjOn enc (C : Set (Finset (ℕ × ℕ))) := by
    intro t ht u hu heq
    ext a
    constructor
    · intro hat
      have hp := (hC t ht).2 a hat |>.1
      have hh := congrArg (fun f => f a.1 hp) heq
      change selectedAt t a.1 = selectedAt u a.1 at hh
      exact ((selectedAt_some_iff u (hC u hu).1 a.1 a).mp
        (hh.symm.trans ((selectedAt_some_iff t (hC t ht).1 a.1 a).mpr ⟨hat, rfl⟩))).1
    · intro hau
      have hp := (hC u hu).2 a hau |>.1
      have hh := congrArg (fun f => f a.1 hp) heq
      change selectedAt t a.1 = selectedAt u a.1 at hh
      exact ((selectedAt_some_iff t (hC t ht).1 a.1 a).mp
        (hh.trans ((selectedAt_some_iff u (hC u hu).1 a.1 a).mpr ⟨hau, rfl⟩))).1
  calc
    _ = ∑ t ∈ C, ∏ p ∈ P.attach, (enc t p.1 p.2).elim 1 w := by
      apply sum_congr rfl
      intro t ht
      dsimp only [enc]
      rw [Finset.prod_attach P (fun p => (selectedAt t p).elim 1 w)]
      exact (selectedAt_prod P t w (hC t ht).1 (fun a ha => (hC t ht).2 a ha |>.1)).symm
    _ = ∑ f ∈ C.image enc, ∏ p ∈ P.attach, (f p.1 p.2).elim 1 w := by
      exact (Finset.sum_image (f := fun f : ∀ p ∈ P, Option (ℕ × ℕ) =>
        ∏ p ∈ P.attach, (f p.1 p.2).elim 1 w) hinj).symm
    _ ≤ ∑ f ∈ P.pi opts, ∏ p ∈ P.attach, (f p.1 p.2).elim 1 w := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact image_subset_iff.mpr henc
      · intro f hf _
        apply prod_nonneg
        intro p hp
        have hh := mem_pi.mp hf p.1 p.2
        rcases mem_insert.mp hh with hh | hh
        · rw [hh]
          norm_num
        · obtain ⟨a, ha, he⟩ := mem_image.mp hh
          rw [← he]
          exact hw p.1 p.2 a ha
    _ = ∏ p ∈ P, ∑ o ∈ opts p, o.elim 1 w := (prod_sum P opts (fun _ o => o.elim 1 w)).symm
    _ = _ := by
      apply prod_congr rfl
      intro p hp
      rw [show opts p = insert none ((S p).image some) from rfl, sum_insert (by simp), sum_image]
      · simp
      · intro a ha b hb hab
        exact Option.some.inj hab

private lemma carrier_height_injective (A : AtomSystem) (m p : ℕ) :
    Set.InjOn (levelHeight A) {a | a ∈ retained A m ∧ a.1 = p} := by
  intro a ha b hb hab
  have ha' := (mem_filter.mp (mem_filter.mp ha.1).1).2
  have hb' := (mem_filter.mp (mem_filter.mp hb.1).1).2
  apply Prod.ext (ha.2.trans hb.2.symm)
  exact le_antisymm
    (ha'.2 b (rounding_retained_mem_atoms A m hb.1) (hb.2.trans ha.2.symm) hb'.1 hab.symm)
    (hb'.2 a (rounding_retained_mem_atoms A m ha.1) (ha.2.trans hb.2.symm) ha'.1 hab)

private lemma dyadic_ratio (h k : ℕ) (hkh : k ≤ h) :
    (2 : ℝ)⁻¹ ^ k / (2 : ℝ)⁻¹ ^ h = (2 : ℝ) ^ (h - k) := by
  rw [inv_pow, inv_pow, div_inv_eq_mul, mul_comm]
  exact (pow_sub₀ (2 : ℝ) (by norm_num) hkh).symm

private lemma available_weight_sum_le (A : AtomSystem) (m n p h : ℕ) :
    (∑ b ∈ (retained A m).filter
      (fun b => b.1 = p ∧ modulus b ∣ n ∧ levelHeight A b ≤ h),
      (2 : ℝ) ^ (-((levelValue A b : ℝ) / ((2 : ℝ)⁻¹ ^ h)))) ≤ 1 := by
  classical
  let s := (retained A m).filter (fun b => b.1 = p ∧ modulus b ∣ n ∧ levelHeight A b ≤ h)
  let f (b : ℕ × ℕ) := h - levelHeight A b
  have hinj : Set.InjOn f (s : Set (ℕ × ℕ)) := by
    intro b hb c hc hbc
    have hbh := (mem_filter.mp hb).2.2.2
    have hch := (mem_filter.mp hc).2.2.2
    have heq : levelHeight A b = levelHeight A c := by dsimp only [f] at hbc; omega
    exact carrier_height_injective A m p
      ⟨(mem_filter.mp hb).1, (mem_filter.mp hb).2.1⟩
      ⟨(mem_filter.mp hc).1, (mem_filter.mp hc).2.1⟩ heq
  have hw (b : ℕ × ℕ) (hb : b ∈ s) :
      (2 : ℝ) ^ (-((levelValue A b : ℝ) / ((2 : ℝ)⁻¹ ^ h))) ≤ (2 : ℝ)⁻¹ ^ (f b + 1) := by
    have hratio : (levelValue A b : ℝ) / ((2 : ℝ)⁻¹ ^ h) = (2 : ℝ) ^ f b := by
      simpa only [levelValue, NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat, f] using
        dyadic_ratio h (levelHeight A b) (mem_filter.mp hb).2.2.2
    rw [hratio]
    calc
      _ ≤ (2 : ℝ) ^ (-((f b + 1 : ℕ) : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        have hh : ((f b + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ f b := by
          exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := f b))
        linarith
      _ = _ := by rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, inv_pow]
  have hfinite : (∑ i ∈ s.image f, (2 : ℝ)⁻¹ ^ i) ≤ 2 := by
    have hh := summable_geometric_two.sum_le_tsum (s.image f) (fun i hi => by positivity)
    simp only [one_div] at hh
    rw [tsum_geometric_inv_two] at hh
    exact hh
  calc
    _ ≤ ∑ b ∈ s, (2 : ℝ)⁻¹ ^ (f b + 1) := sum_le_sum hw
    _ = (2 : ℝ)⁻¹ * ∑ b ∈ s, (2 : ℝ)⁻¹ ^ f b := by
      simp only [pow_succ]
      rw [← sum_mul]
      ring
    _ = (2 : ℝ)⁻¹ * ∑ i ∈ s.image f, (2 : ℝ)⁻¹ ^ i := by rw [sum_image hinj]
    _ ≤ (2 : ℝ)⁻¹ * 2 := mul_le_mul_of_nonneg_left hfinite (by norm_num)
    _ = 1 := by norm_num

private lemma theta_mul_Ntheta_le (A : AtomSystem) (m n : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    θ * (Ntheta A m n θ : ℝ) ≤ Ttheta A m n θ := by
  classical
  calc
    _ = ∑ p ∈ (primes A).filter (fun p => θ ≤ bp A m p n), θ := by
      rw [sum_const, nsmul_eq_mul, mul_comm]
      rfl
    _ = ∑ p ∈ (primes A).filter (fun p => θ ≤ bp A m p n), min (bp A m p n) θ := by
      apply sum_congr rfl
      intro p hp
      exact (min_eq_right (mem_filter.mp hp).2).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun p hp hn => le_min (NNReal.coe_nonneg _) hθ)

theorem carrier_count (A : AtomSystem) (m n : ℕ) (hn : 1 ≤ n)
    (a : ℕ × ℕ) (ha : a ∈ retained A m) (han : modulus a ∣ n) :
    (#((carriers A m).filter (fun P => P ∣ n ∧ lastLevel A m P = a)) : ℝ) ≤
      (2 : ℝ) ^ ((3 + Ttheta A m n (levelValue A a)) / (levelValue A a : ℝ)) := by
  classical
  let θ : ℝ := levelValue A a
  let D := (carriers A m).filter (fun P => P ∣ n ∧ lastLevel A m P = a)
  let f : ℕ → Finset (ℕ × ℕ) := fun P => (effective A m P).erase a
  let C := D.image f
  let Q := (primes A).filter (fun p => θ ≤ bp A m p n)
  let S : ℕ → Finset (ℕ × ℕ) := fun p => (retained A m).filter
    (fun b => b.1 = p ∧ modulus b ∣ n ∧ levelHeight A b ≤ levelHeight A a)
  let w : ℕ × ℕ → ℝ := fun b => (2 : ℝ) ^ (-((levelValue A b : ℝ) / θ))
  have hθ : 0 < θ := by dsimp [θ, levelValue]; positivity
  have hlast (P : ℕ) (hP : P ∈ D) : a ∈ effective A m P := by
    have hh := (carrier_data A m P (mem_filter.mp hP).1).1
    rwa [(mem_filter.mp hP).2.2] at hh
  have hinj : Set.InjOn f (D : Set ℕ) := by
    intro P hP R hR he
    have heff : effective A m P = effective A m R := by
      calc
        _ = insert a (f P) := (insert_erase (hlast P hP)).symm
        _ = insert a (f R) := congrArg (insert a) he
        _ = _ := insert_erase (hlast R hR)
    calc
      P = ∏ b ∈ effective A m P, modulus b := (carrier_data A m P (mem_filter.mp hP).1).2.1
      _ = ∏ b ∈ effective A m R, modulus b := congrArg (fun t => ∏ b ∈ t, modulus b) heff
      _ = R := (carrier_data A m R (mem_filter.mp hR).1).2.1.symm
  have hC : ∀ t ∈ C, Set.InjOn Prod.fst (t : Set (ℕ × ℕ)) ∧
      ∀ b ∈ t, b.1 ∈ Q ∧ b ∈ S b.1 := by
    intro t ht
    obtain ⟨P, hP, rfl⟩ := mem_image.mp ht
    have hPd := mem_filter.mp hP
    constructor
    · intro b hb c hc he
      exact effective_fst_injective A m P (mem_of_mem_erase hb) (mem_of_mem_erase hc) he
    · intro b hb
      have hbe := mem_of_mem_erase hb
      have hbr := (mem_filter.mp hbe).1
      have hbn := (mem_filter.mp hbe).2.1.trans hPd.2.1
      have hheight := (carrier_data A m P hPd.1).2.2.2 b hbe
      rw [hPd.2.2] at hheight
      have hval : θ ≤ (levelValue A b : ℝ) := by
        exact_mod_cast (pow_le_pow_of_le_one (by positivity : (0 : ℝ≥0) ≤ (2 : ℝ≥0)⁻¹)
          (by norm_num : (2 : ℝ≥0)⁻¹ ≤ 1) hheight)
      have hbp : (levelValue A b : ℝ) ≤ bp A m b.1 n := by
        exact_mod_cast (le_sup (f := levelValue A) (mem_filter.mpr ⟨hbr, rfl, hbn⟩) :
          levelValue A b ≤ bpNN A m b.1 n)
      exact ⟨mem_filter.mpr ⟨mem_image_of_mem Prod.fst (rounding_retained_mem_atoms A m hbr),
        hval.trans hbp⟩, mem_filter.mpr ⟨hbr, rfl, hbn, hheight⟩⟩
  have hgen : (∑ t ∈ C, ∏ b ∈ t, w b) ≤ (2 : ℝ) ^ Q.card := by
    calc
      _ ≤ ∏ p ∈ Q, (1 + ∑ b ∈ S p, w b) := weighted_subset_family_bound Q S w C hC
        (fun p hp b hb => Real.rpow_nonneg (by norm_num) _)
      _ ≤ ∏ p ∈ Q, (2 : ℝ) := by
        apply prod_le_prod
        · intro p hp
          have hs0 : 0 ≤ ∑ b ∈ S p, w b := sum_nonneg (fun b hb => Real.rpow_nonneg (by norm_num) _)
          linarith
        · intro p hp
          have hh := available_weight_sum_le A m n p (levelHeight A a)
          have hθeq : θ = (2 : ℝ)⁻¹ ^ levelHeight A a := by simp [θ, levelValue]
          change 1 + (∑ b ∈ S p, w b) ≤ 2
          have hs : (∑ b ∈ S p, w b) ≤ 1 := by simpa only [S, w, hθeq] using hh
          linarith
      _ = _ := prod_const _
  have hweight (t : Finset (ℕ × ℕ)) (ht : t ∈ C) :
      (2 : ℝ) ^ (-(3 / θ)) ≤ ∏ b ∈ t, w b := by
    obtain ⟨P, hP, rfl⟩ := mem_image.mp ht
    have hmass := (carrier_data A m P (mem_filter.mp hP).1).2.2.1
    rw [(mem_filter.mp hP).2.2] at hmass
    calc
      _ ≤ (2 : ℝ) ^ (-((∑ b ∈ f P, (levelValue A b : ℝ)) / θ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        exact neg_le_neg (div_le_div_of_nonneg_right hmass.le hθ.le)
      _ = _ := by
        dsimp only [w]
        rw [← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)]
        congr 1
        rw [sum_neg_distrib, ← sum_div]
  have hcount : (D.card : ℝ) * (2 : ℝ) ^ (-(3 / θ)) ≤ (2 : ℝ) ^ (Q.card : ℝ) := by
    calc
      _ = ∑ t ∈ C, (2 : ℝ) ^ (-(3 / θ)) := by
        rw [sum_const, nsmul_eq_mul, show C.card = D.card from card_image_iff.mpr hinj]
      _ ≤ ∑ t ∈ C, ∏ b ∈ t, w b := sum_le_sum hweight
      _ ≤ (2 : ℝ) ^ Q.card := hgen
      _ = _ := (Real.rpow_natCast _ _).symm
  have hN : θ * (Q.card : ℝ) ≤ Ttheta A m n θ := theta_mul_Ntheta_le A m n θ hθ.le
  calc
    _ ≤ (2 : ℝ) ^ (Q.card : ℝ) / (2 : ℝ) ^ (-(3 / θ)) :=
      (le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)).2 hcount
    _ = (2 : ℝ) ^ (3 / θ + (Q.card : ℝ)) := by
      rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      apply (le_div_iff₀ hθ).2
      have hcancel : (3 / θ) * θ = (3 : ℝ) := div_mul_cancel₀ _ hθ.ne'
      nlinarith


private lemma U_nonneg (A : AtomSystem) (m P n : ℕ) : 0 ≤ U A m P n :=
  sum_nonneg (fun p hp => le_min (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))

private lemma carrier_theta_le_bp (A : AtomSystem) (m P p : ℕ) (hP : P ∈ carriers A m)
    (hp : Nat.Prime p) (hpP : p ∣ P) : theta A m P ≤ bp A m p P := by
  obtain ⟨a, ha, hap⟩ := (prime_dvd_carrier A m P p hP hp).mp hpP
  rw [← hap, effective_value_eq_bp A m P a ha]
  have hh := (carrier_data A m P hP).2.2.2 a ha
  exact_mod_cast (pow_le_pow_of_le_one (by positivity : (0 : ℝ≥0) ≤ (2 : ℝ≥0)⁻¹)
    (by norm_num : (2 : ℝ≥0)⁻¹ ≤ 1) hh)

private lemma T_le_U_add_mu (A : AtomSystem) (m P n : ℕ) (hP : P ∈ carriers A m) :
    Ttheta A m n (theta A m P) ≤ U A m P n + mu A m P := by
  classical
  calc
    _ = (∑ p ∈ (primes A).filter (fun p => p ∣ P), min (bp A m p n) (theta A m P)) + U A m P n :=
      (sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ (∑ p ∈ (primes A).filter (fun p => p ∣ P), bp A m p P) + U A m P n := by
      apply add_le_add _ le_rfl
      apply sum_le_sum
      intro p hp
      obtain ⟨a, ha, hap⟩ := mem_image.mp (mem_filter.mp hp).1
      have hprime : Nat.Prime p := hap ▸ (A.prime_of_mem a ha).1
      exact (min_le_right _ _).trans (carrier_theta_le_bp A m P p hP hprime (mem_filter.mp hp).2)
    _ ≤ B A m P + U A m P n := add_le_add
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p hp hn => NNReal.coe_nonneg _)) le_rfl
    _ = _ := add_comm _ _

private def activeCarriers (A : AtomSystem) (m n : ℕ) : Finset ℕ := by
  classical
  exact (carriers A m).filter (fun P => P ∣ n ∧ U A m P n < 16)

private lemma F_active_bound (A : AtomSystem) (m n : ℕ) :
    F A m n ≤ 3 * ∑ P ∈ activeCarriers A m n, coefficient A m P := by
  classical
  unfold F activeCarriers
  rw [sum_filter]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
  apply sum_le_sum
  intro P hP
  have hc := coefficient_nonneg A m P
  have hU := U_nonneg A m P n
  by_cases hd : P ∣ n
  · by_cases hu : U A m P n < 16
    · simp only [hd, hu, and_self, if_true]
      nlinarith
    · simp only [hd, hu, and_false, if_true, if_false]
      have hh : 16 ≤ U A m P n := le_of_not_gt hu
      nlinarith
  · simp [hd]

private lemma active_last_mem (A : AtomSystem) (m n P : ℕ) (hP : P ∈ activeCarriers A m n) :
    lastLevel A m P ∈ (retained A m).filter (fun a => modulus a ∣ n) := by
  have hPa := mem_filter.mp hP
  have ha := mem_filter.mp (carrier_data A m P hPa.1).1
  exact mem_filter.mpr ⟨ha.1, ha.2.1.trans hPa.2.1⟩

private lemma dyadic_rpow23 (A : AtomSystem) (a : ℕ × ℕ) :
    (2 : ℝ) ^ (23 / (levelValue A a : ℝ)) = (2 : ℝ) ^ (23 * 2 ^ levelHeight A a) := by
  have he : (23 : ℝ) / (levelValue A a : ℝ) = ((23 * 2 ^ levelHeight A a : ℕ) : ℝ) := by
    simp [levelValue, inv_pow, div_inv_eq_mul]
  rw [he, Real.rpow_natCast]

private lemma active_group_bound (A : AtomSystem) (m : ℕ) (hm : 4096 < m)
    (hH : mean A < 17 / 16) (n : ℕ) (hn : 1 ≤ n) (a : ℕ × ℕ)
    (ha : a ∈ retained A m) (han : modulus a ∣ n) :
    (∑ P ∈ (activeCarriers A m n).filter (fun P => lastLevel A m P = a), coefficient A m P) ≤
      (17 / 208 : ℝ) * (levelValue A a : ℝ) := by
  classical
  let t := (activeCarriers A m n).filter (fun P => lastLevel A m P = a)
  let θ : ℝ := levelValue A a
  let h := levelHeight A a
  let eps := epsilon (HB A m) h
  have hθ : 0 < θ := by dsimp [θ, levelValue]; positivity
  have hHB0 : 0 ≤ HB A m := sum_nonneg (fun a ha =>
    div_nonneg (increment_nonneg A m ha) (Nat.cast_nonneg _))
  have heps : 0 ≤ eps := by dsimp [eps, epsilon]; positivity
  by_cases ht : t.Nonempty
  · obtain ⟨P, hPt⟩ := ht
    have hPa := mem_filter.mp (mem_filter.mp hPt).1
    have hlast := (mem_filter.mp hPt).2
    have hT : Ttheta A m n θ < 20 := by
      have hh := T_le_U_add_mu A m P n hPa.1
      have hmu := (carrier_mass_range A m P hPa.1).2
      rw [theta, hlast] at hh
      have hU := hPa.2.2
      linarith
    have hsub : t ⊆ (carriers A m).filter (fun P => P ∣ n ∧ lastLevel A m P = a) := by
      intro Q hQ
      have hQa := mem_filter.mp (mem_filter.mp hQ).1
      exact mem_filter.mpr ⟨hQa.1, hQa.2.1, (mem_filter.mp hQ).2⟩
    have hcard : (t.card : ℝ) ≤ (2 : ℝ) ^ (23 / θ) := by
      calc
        _ ≤ (#((carriers A m).filter (fun P => P ∣ n ∧ lastLevel A m P = a)) : ℝ) := by
          exact_mod_cast card_le_card hsub
        _ ≤ (2 : ℝ) ^ ((3 + Ttheta A m n θ) / θ) := carrier_count A m n hn a ha han
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (div_le_div_of_nonneg_right (by linarith) hθ.le)
    have hsum : (∑ P ∈ t, coefficient A m P) ≤ (t.card : ℝ) * (2 * eps) := by
      calc
        _ ≤ ∑ P ∈ t, 2 * eps := by
          apply sum_le_sum
          intro Q hQ
          have hQc := (mem_filter.mp (mem_filter.mp hQ).1).1
          have hh := (carried_mass A m hm Q hQc).2.2.2
          rw [(mem_filter.mp hQ).2] at hh
          exact hh
        _ = _ := by rw [sum_const, nsmul_eq_mul]
    have hG := uniform_numerical (HB A m) hHB0 ((HB_le_mean A m).trans hH.le) h
    have heq : (2 : ℝ) ^ (23 / θ) * (2 * eps) = 2 * θ * G (HB A m) h := by
      rw [show θ = (levelValue A a : ℝ) from rfl, dyadic_rpow23]
      have hθeq : (2 : ℝ)⁻¹ ^ h = (levelValue A a : ℝ) := by simp [h, levelValue]
      dsimp only [G]
      rw [hθeq]
      dsimp only [eps, h]
      have hvne : (levelValue A a : ℝ) ≠ 0 := hθ.ne'
      field_simp [hvne]
    calc
      _ ≤ (t.card : ℝ) * (2 * eps) := hsum
      _ ≤ (2 : ℝ) ^ (23 / θ) * (2 * eps) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 * θ * G (HB A m) h := heq
      _ ≤ 2 * θ * (17 / 416 : ℝ) := mul_le_mul_of_nonneg_left hG (by positivity)
      _ = _ := by ring
  · have hz : t = ∅ := not_nonempty_iff_eq_empty.mp ht
    change (∑ P ∈ t, coefficient A m P) ≤ _
    rw [hz, sum_empty]
    positivity

private lemma active_total_bound (A : AtomSystem) (m : ℕ) (hm : 4096 < m)
    (hH : mean A < 17 / 16) (n : ℕ) (hn : 1 ≤ n) :
    (∑ P ∈ activeCarriers A m n, coefficient A m P) ≤
      (17 / 208 : ℝ) * ∑ a ∈ (retained A m).filter (fun a => modulus a ∣ n), (levelValue A a : ℝ) := by
  have hmap : ∀ P ∈ activeCarriers A m n,
      lastLevel A m P ∈ (retained A m).filter (fun a => modulus a ∣ n) := active_last_mem A m n
  rw [← sum_fiberwise_of_maps_to hmap (coefficient A m), mul_sum]
  apply sum_le_sum
  intro a ha
  exact active_group_bound A m hm hH n hn a (mem_filter.mp ha).1 (mem_filter.mp ha).2

theorem pointwise_feasibility (A : AtomSystem) (m : ℕ) (hm : 4096 < m)
    (hH : mean A < 17 / 16) (n : ℕ) (hn : 1 ≤ n) :
    F A m n ≤ max (B A m n - 1) 0 := by
  classical
  by_cases hB : B A m n ≤ 2
  · have hnone : ∀ P ∈ carriers A m, ¬ P ∣ n := by
      intro P hP hPn
      have hlow := (carrier_mass_range A m P hP).1
      have hmono := B_dvd_mono A m hPn
      dsimp only [mu] at hlow
      linarith
    have hz : F A m n = 0 := by
      unfold F
      rw [sum_eq_zero (fun P hP => if_neg (hnone P hP)), mul_zero]
    rw [hz]
    exact le_max_right _ _
  · have hB' : 2 < B A m n := lt_of_not_ge hB
    calc
      _ ≤ 3 * ∑ P ∈ activeCarriers A m n, coefficient A m P := F_active_bound A m n
      _ ≤ 3 * ((17 / 208 : ℝ) * ∑ a ∈ (retained A m).filter (fun a => modulus a ∣ n), (levelValue A a : ℝ)) :=
        mul_le_mul_of_nonneg_left (active_total_bound A m hm hH n hn) (by norm_num)
      _ ≤ (51 / 104 : ℝ) * B A m n := by have hh := values_at_point A m n; nlinarith
      _ ≤ max (B A m n - 1) 0 := (by linarith : (51 / 104 : ℝ) * B A m n ≤ B A m n - 1).trans (le_max_left _ _)

#print axioms pointwise_feasibility
#print axioms T_le_U_add_mu
#print axioms active_group_bound

end
end Erdos708SparseCore
