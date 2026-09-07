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


#print axioms moment_retained

end
end Erdos708SparseCore
