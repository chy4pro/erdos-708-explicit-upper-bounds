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

private lemma beta_bounds (A : AtomSystem) (m : ℕ) (θ : ℝ) (a : ℕ × ℕ)
    (ha : a ∈ retained A m) : 0 ≤ beta A m θ a ∧ beta A m θ a ≤ increment A m a := by
  have hprev : (previousValue A m a : ℝ) ≤ levelValue A a := sub_nonneg.mp (increment_nonneg A m ha)
  constructor
  · exact sub_nonneg.mpr (min_le_min hprev le_rfl)
  · dsimp only [beta, increment]
    by_cases hv : (levelValue A a : ℝ) ≤ θ
    · rw [min_eq_left hv, min_eq_left (hprev.trans hv)]
    · rw [min_eq_right (le_of_not_ge hv)]
      by_cases hp : (previousValue A m a : ℝ) ≤ θ
      · rw [min_eq_left hp]
        linarith
      · rw [min_eq_right (le_of_not_ge hp)]
        linarith

private lemma beta_telescope (A : AtomSystem) (m p n : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∑ a ∈ (retained A m).filter (fun a => a.1 = p ∧ modulus a ∣ n), beta A m θ a) =
      min (bp A m p n) θ := by
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
  let Θ : ℝ≥0 := ⟨θ, hθ⟩
  have hclip (t : Finset (ℕ × ℕ)) :
      ((t.sup (fun a => min (levelValue A a) Θ) : ℝ≥0) : ℝ) =
        min ((t.sup (levelValue A) : ℝ≥0) : ℝ) θ := by
    rw [← Finset.sup_inf_distrib_right]
    rfl
  calc
    _ = ∑ a ∈ s, (((min (levelValue A a) Θ : ℝ≥0) : ℝ) -
        (((s.filter (fun b => b.2 < a.2)).sup (fun a => min (levelValue A a) Θ) : ℝ≥0) : ℝ)) := by
      apply sum_congr rfl
      intro a ha
      rw [beta, hprev a ha, hclip]
      rfl
    _ = ((s.sup (fun a => min (levelValue A a) Θ) : ℝ≥0) : ℝ) :=
      sum_jumps_eq_sup s Prod.snd (fun a => min (levelValue A a) Θ) hinj
        (fun a ha b hb hab => min_le_min (hmono a ha b hb hab) le_rfl)
    _ = _ := hclip s

private lemma positive_support (A : AtomSystem) (m : ℕ) (hm : 4096 < m)
    (D : ℕ) (hD : 0 < signedCoefficient A m D) :
    D ∈ carriers A m ∧ (D : ℝ) < (m : ℝ) ^ (1 / 4 : ℝ) := by
  classical
  have hneg : 0 ≤ ∑ P ∈ carriers A m, coefficient A m P *
      ∑ a ∈ (retained A m).filter (fun a => ¬ a.1 ∣ P),
        if P * modulus a = D then beta A m (theta A m P) a else 0 := by
    apply sum_nonneg
    intro P hP
    apply mul_nonneg (coefficient_nonneg A m P)
    apply sum_nonneg
    intro a ha
    split_ifs
    · exact (beta_bounds A m _ a (mem_filter.mp ha).1).1
    · exact le_rfl
  have hmem : D ∈ carriers A m := by
    by_contra hn
    have hz : (∑ P ∈ carriers A m, if P = D then 3 * coefficient A m P else 0) = 0 := by
      apply sum_eq_zero
      intro P hP
      exact if_neg (fun (he : P = D) => hn (he ▸ hP))
    unfold signedCoefficient at hD
    rw [hz] at hD
    linarith
  exact ⟨hmem, carrier_small A m hm D hmem⟩

private lemma negative_support (A : AtomSystem) (m : ℕ) (hm : 4096 < m)
    (D : ℕ) (hD : signedCoefficient A m D < 0) :
    ∃ P ∈ carriers A m, ∃ a ∈ retained A m, ¬ a.1 ∣ P ∧
      D = P * modulus a ∧ (D : ℝ) < (m : ℝ) ^ (5 / 16 : ℝ) := by
  classical
  have hex : ∃ P ∈ carriers A m, ∃ a ∈ retained A m, ¬ a.1 ∣ P ∧ D = P * modulus a := by
    by_contra hn
    push_neg at hn
    have hz (P : ℕ) (hP : P ∈ carriers A m) :
        (∑ a ∈ (retained A m).filter (fun a => ¬ a.1 ∣ P),
          if P * modulus a = D then beta A m (theta A m P) a else 0) = 0 := by
      apply sum_eq_zero
      intro a ha
      exact if_neg (Ne.symm (hn P hP a (mem_filter.mp ha).1 (mem_filter.mp ha).2))
    have hpos : 0 ≤ ∑ P ∈ carriers A m, if P = D then 3 * coefficient A m P else 0 := by
      apply sum_nonneg
      intro P hP
      split_ifs
      · exact mul_nonneg (by norm_num) (coefficient_nonneg A m P)
      · exact le_rfl
    have hz' : (∑ P ∈ carriers A m, coefficient A m P *
        ∑ a ∈ (retained A m).filter (fun a => ¬ a.1 ∣ P),
          if P * modulus a = D then beta A m (theta A m P) a else 0) = 0 := by
      apply sum_eq_zero
      intro P hP
      rw [hz P hP, mul_zero]
    unfold signedCoefficient at hD
    rw [hz', mul_zero, sub_zero] at hD
    linarith
  obtain ⟨P, hP, a, ha, hpa, rfl⟩ := hex
  exact ⟨P, hP, a, ha, hpa, rfl, negative_modulus_small A m hm P hP a ha⟩

private lemma clip_difference (s t : ℝ) (hst : s ≤ t) :
    max (min t 3 - max s 2) 0 = min (max t 2) 3 - min (max s 2) 3 := by
  simp only [min_def, max_def]
  split_ifs <;> linarith

private lemma prefixWeight_sum_partial (A : AtomSystem) (m k i : ℕ)
    (hi : i ≤ (effectiveList A m k).length) :
    (∑ j ∈ Icc 1 i, prefixWeight A m k j) = min (max (partialMass A m k i) 2) 3 - 2 := by
  induction i with
  | zero => norm_num [partialMass, prefixLevels]
  | succ i ih =>
    rw [sum_Icc_succ_top (by omega), ih (by omega)]
    have hmass := partialMass_succ A m k i (by omega)
    have hmono : partialMass A m k i ≤ partialMass A m k (i + 1) := by
      rw [hmass]
      exact le_add_of_nonneg_right (NNReal.coe_nonneg _)
    have hw : prefixWeight A m k (i + 1) =
        min (max (partialMass A m k (i + 1)) 2) 3 - min (max (partialMass A m k i) 2) 3 := by
      simp only [prefixWeight, Nat.add_sub_cancel]
      exact clip_difference _ _ hmono
    rw [hw]
    ring

private lemma prefixWeight_sum (A : AtomSystem) (m k : ℕ) (hk : k ∈ hot A m) :
    (∑ i ∈ Icc 1 (effectiveList A m k).length, prefixWeight A m k i) = 1 := by
  rw [prefixWeight_sum_partial A m k _ le_rfl]
  have hm : partialMass A m k (effectiveList A m k).length = B A m k := by
    simp only [partialMass, prefixLevels, List.take_length, B_eq_effectiveList_sum]
  rw [hm]
  have hhot := (mem_filter.mp hk).2
  rw [max_eq_left (by linarith), min_eq_right (by linarith)]
  norm_num

private lemma total_carried_mass (A : AtomSystem) (m : ℕ) :
    (∑ P ∈ carriers A m, M A m P) = LB A m := by
  classical
  have hmap : ∀ ki ∈ occurrences A m, prefixProd A m ki.1 ki.2 ∈ carriers A m :=
    fun ki hki => mem_image_of_mem _ hki
  unfold M
  rw [sum_fiberwise_of_maps_to hmap]
  unfold occurrences
  rw [sum_biUnion]
  · calc
      _ = ∑ k ∈ hot A m, (B A m k - 16) := by
        apply sum_congr rfl
        intro k hk
        rw [sum_image]
        · calc
            _ = ∑ i ∈ Icc 1 (effectiveList A m k).length,
                (B A m k - 16) * prefixWeight A m k i := by
              apply sum_subset (filter_subset _ _)
              intro i hi hn
              have hw : prefixWeight A m k i = 0 := by
                have hn' : ¬ 0 < prefixWeight A m k i := fun h => hn (mem_filter.mpr ⟨hi, h⟩)
                exact le_antisymm (le_of_not_gt hn') (le_max_right _ _)
              simp only [hw, mul_zero]
            _ = _ := by rw [← mul_sum, prefixWeight_sum A m k hk, mul_one]
        · intro i hi j hj he
          exact (Prod.mk.inj he).2
      _ = LB A m := by
        unfold hot LB
        rw [sum_filter]
        apply sum_congr rfl
        intro k hk
        by_cases hh : 16 < B A m k
        · rw [if_pos hh, max_eq_left (by linarith)]
        · rw [if_neg hh, max_eq_right (by linarith)]
  · intro k hk l hl hkl
    apply disjoint_left.mpr
    intro ki hik hil
    obtain ⟨i, hi, he⟩ := mem_image.mp hik
    obtain ⟨j, hj, he'⟩ := mem_image.mp hil
    exact hkl (congrArg Prod.fst (he.trans he'.symm))

private lemma U_eq_beta_sum (A : AtomSystem) (m P n : ℕ) :
    U A m P n = ∑ a ∈ (retained A m).filter (fun a => ¬ a.1 ∣ P ∧ modulus a ∣ n),
      beta A m (theta A m P) a := by
  classical
  calc
    _ = ∑ p ∈ (primes A).filter (fun p => ¬ p ∣ P),
        ∑ a ∈ (retained A m).filter (fun a => a.1 = p ∧ modulus a ∣ n),
          beta A m (theta A m P) a := by
      apply sum_congr rfl
      intro p hp
      exact (beta_telescope A m p n _ (NNReal.coe_nonneg _)).symm
    _ = _ := by
      have hmap : ∀ a ∈ (retained A m).filter (fun a => ¬ a.1 ∣ P ∧ modulus a ∣ n),
          a.1 ∈ (primes A).filter (fun p => ¬ p ∣ P) := by
        intro a ha
        exact mem_filter.mpr ⟨mem_image_of_mem Prod.fst
          (rounding_retained_mem_atoms A m (mem_filter.mp ha).1), (mem_filter.mp ha).2.1⟩
      rw [← sum_fiberwise_of_maps_to hmap (beta A m (theta A m P))]
      apply sum_congr rfl
      intro p hp
      apply sum_congr
      · ext a
        simp only [mem_filter]
        constructor
        · rintro ⟨ha, hap, had⟩
          exact ⟨⟨ha, hap ▸ (mem_filter.mp hp).2, had⟩, hap⟩
        · rintro ⟨⟨ha, hpa, had⟩, hap⟩
          exact ⟨ha, hap, had⟩
      · intro a ha
        rfl

private lemma outside_coprime (A : AtomSystem) (m P : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) (hpa : ¬ a.1 ∣ P) : Nat.Coprime P (modulus a) :=
  ((carrier_retained_prime A m ha).1.coprime_iff_not_dvd.mpr hpa).symm.pow_right _

private lemma indicator_U (A : AtomSystem) (m P n : ℕ) :
    (if P ∣ n then U A m P n else 0) =
      ∑ a ∈ (retained A m).filter (fun a => ¬ a.1 ∣ P),
        if P * modulus a ∣ n then beta A m (theta A m P) a else 0 := by
  classical
  by_cases hPn : P ∣ n
  · rw [if_pos hPn, U_eq_beta_sum]
    rw [sum_filter, sum_filter]
    apply sum_congr rfl
    intro a ha
    by_cases hp : a.1 ∣ P
    · simp [hp]
    · have he : P * modulus a ∣ n ↔ modulus a ∣ n :=
        ⟨fun hh => (dvd_mul_left (modulus a) P).trans hh,
          fun hh => (outside_coprime A m P ha hp).mul_dvd_of_dvd_of_dvd hPn hh⟩
      simp [hp, he]
  · rw [if_neg hPn]
    symm
    apply sum_eq_zero
    intro a ha
    exact if_neg (fun hh => hPn ((dvd_mul_right P (modulus a)).trans hh))

private lemma F_expanded (A : AtomSystem) (m n : ℕ) :
    F A m n =
      (∑ P ∈ carriers A m, if P ∣ n then 3 * coefficient A m P else 0) -
      (3 / 16 : ℝ) * ∑ P ∈ carriers A m, coefficient A m P *
        ∑ a ∈ (retained A m).filter (fun a => ¬ a.1 ∣ P),
          if P * modulus a ∣ n then beta A m (theta A m P) a else 0 := by
  classical
  rw [F, mul_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro P hP
  rw [← indicator_U]
  by_cases hPn : P ∣ n <;> simp [hPn] <;> ring

private lemma beta_mean_le (A : AtomSystem) (m P : ℕ) :
    (∑ a ∈ (retained A m).filter (fun a => ¬ a.1 ∣ P),
      beta A m (theta A m P) a / (modulus a : ℝ)) ≤ HB A m := by
  calc
    _ ≤ ∑ a ∈ (retained A m).filter (fun a => ¬ a.1 ∣ P),
        increment A m a / (modulus a : ℝ) := by
      apply sum_le_sum
      intro a ha
      exact div_le_div_of_nonneg_right (beta_bounds A m _ a (mem_filter.mp ha).1).2 (Nat.cast_nonneg _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun a ha hn =>
      div_nonneg (increment_nonneg A m ha) (Nat.cast_nonneg _))

private lemma negative_window_count (A : AtomSystem) (m : ℕ) (hm : 4096 < m)
    (P : ℕ) (hP : P ∈ carriers A m) (x : ℕ) :
    (∑ a ∈ (retained A m).filter (fun a => ¬ a.1 ∣ P),
      beta A m (theta A m P) a * (windowCount x m (P * modulus a) : ℝ)) ≤
      2 * ((m : ℝ) / P) * HB A m := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hPpos : (0 : ℝ) < P := by exact_mod_cast carrier_pos A m P hP
  calc
    _ ≤ ∑ a ∈ (retained A m).filter (fun a => ¬ a.1 ∣ P),
        beta A m (theta A m P) a * (2 * ((m : ℝ) / (P * modulus a : ℕ))) := by
      apply sum_le_sum
      intro a ha
      have har := (mem_filter.mp ha).1
      apply mul_le_mul_of_nonneg_left _ (beta_bounds A m _ a har).1
      apply windowCount_upper_two
      · exact Nat.mul_pos (carrier_pos A m P hP) (retained_modulus_pos A m har)
      · have hh := negative_modulus_small A m hm P hP a har
        have hpow : (m : ℝ) ^ (5 / 16 : ℝ) ≤ m := by
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num : (5 / 16 : ℝ) ≤ 1)
        exact_mod_cast hh.le.trans hpow
    _ = 2 * ((m : ℝ) / P) *
        ∑ a ∈ (retained A m).filter (fun a => ¬ a.1 ∣ P), beta A m (theta A m P) a / (modulus a : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro a ha
      have hqpos : (0 : ℝ) < modulus a := by exact_mod_cast retained_modulus_pos A m (mem_filter.mp ha).1
      rw [Nat.cast_mul]
      field_simp
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (beta_mean_le A m P) (by positivity)

private lemma indicator_window_sum (x m d : ℕ) (w : ℝ) :
    (∑ n ∈ Icc (x + 1) (x + m), if d ∣ n then w else 0) = w * (windowCount x m d : ℝ) := by
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  exact mul_comm _ _

private lemma F_window_eq (A : AtomSystem) (m x : ℕ) :
    (∑ n ∈ Icc (x + 1) (x + m), F A m n) =
      ∑ P ∈ carriers A m, (3 * coefficient A m P * (windowCount x m P : ℝ) -
        (3 / 16 : ℝ) * coefficient A m P *
          ∑ a ∈ (retained A m).filter (fun a => ¬ a.1 ∣ P),
            beta A m (theta A m P) a * (windowCount x m (P * modulus a) : ℝ)) := by
  classical
  have hf (n : ℕ) : F A m n = ∑ P ∈ carriers A m,
      ((if P ∣ n then 3 * coefficient A m P else 0) -
        ((3 / 16 : ℝ) * coefficient A m P) *
          ∑ a ∈ (retained A m).filter (fun a => ¬ a.1 ∣ P),
            if P * modulus a ∣ n then beta A m (theta A m P) a else 0) := by
    rw [sum_sub_distrib]
    simp_rw [mul_assoc]
    rw [← mul_sum]
    exact F_expanded A m n
  simp_rw [hf]
  rw [sum_comm]
  apply sum_congr rfl
  intro P hP
  rw [sum_sub_distrib, indicator_window_sum, ← mul_sum, sum_comm]
  congr 2
  apply sum_congr rfl
  intro a ha
  exact indicator_window_sum x m _ _

private lemma F_window_lower (A : AtomSystem) (m : ℕ) (hm : 4096 < m)
    (hH : mean A < 17 / 16) (x : ℕ) :
    (141 / 64 : ℝ) * LB A m ≤ ∑ n ∈ Icc (x + 1) (x + m), F A m n := by
  have hHB0 : 0 ≤ HB A m := sum_nonneg (fun a ha =>
    div_nonneg (increment_nonneg A m ha) (Nat.cast_nonneg _))
  have hHB : HB A m ≤ 17 / 16 := (HB_le_mean A m).trans hH.le
  have hLB : 0 ≤ LB A m := sum_nonneg (fun k hk => le_max_right _ _)
  rw [F_window_eq]
  calc
    _ ≤ (3 - (3 / 4 : ℝ) * HB A m) * LB A m := by nlinarith
    _ = ∑ P ∈ carriers A m, (3 - (3 / 4 : ℝ) * HB A m) * M A m P := by
      rw [← total_carried_mass, mul_sum]
    _ ≤ _ := by
      apply sum_le_sum
      intro P hP
      have hc := coefficient_nonneg A m P
      have hM := carried_mass_nonneg A m P
      have hK : (0 : ℝ) < K m P := by exact_mod_cast K_pos A m hm P hP
      have hcK : coefficient A m P * (K m P : ℝ) = M A m P := div_mul_cancel₀ _ hK.ne'
      have hcount : (K m P : ℝ) ≤ windowCount x m P := by exact_mod_cast windowCount_lower x m P
      have hpos : 3 * M A m P ≤ 3 * coefficient A m P * (windowCount x m P : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hcount hc]
      have hneg : (3 / 16 : ℝ) * coefficient A m P *
          (∑ a ∈ (retained A m).filter (fun a => ¬ a.1 ∣ P),
            beta A m (theta A m P) a * (windowCount x m (P * modulus a) : ℝ)) ≤
          (3 / 4 : ℝ) * HB A m * M A m P := by
        calc
          _ ≤ (3 / 16 : ℝ) * coefficient A m P * (2 * ((m : ℝ) / P) * HB A m) :=
            mul_le_mul_of_nonneg_left (negative_window_count A m hm P hP x) (by positivity)
          _ ≤ (3 / 16 : ℝ) * coefficient A m P * (2 * (2 * (K m P : ℝ)) * HB A m) := by
            gcongr
            exact quotient_le_two_K A m hm P hP
          _ = _ := by rw [← hcK]; ring
      nlinarith

private lemma delta_sum (s : Finset ℕ) (d : ℕ) (w : ℝ) (f : ℕ → ℝ) (hd : d ∈ s) :
    (∑ D ∈ s, (if d = D then w else 0) * f D) = w * f d := by
  classical
  simp [ite_mul, hd]

private lemma F_signed_expansion (A : AtomSystem) (m n : ℕ) :
    F A m n = ∑ D ∈ certificateSupport A m,
      signedCoefficient A m D * (if D ∣ n then 1 else 0) := by
  classical
  have hPmem (P : ℕ) (hP : P ∈ carriers A m) : P ∈ certificateSupport A m := mem_union_left _ hP
  have hqmem (P : ℕ) (hP : P ∈ carriers A m) (a : ℕ × ℕ)
      (ha : a ∈ (retained A m).filter (fun a => ¬ a.1 ∣ P)) : P * modulus a ∈ certificateSupport A m :=
    mem_union_right _ (mem_biUnion.mpr ⟨P, hP, mem_image_of_mem _ ha⟩)
  rw [F_expanded]
  symm
  unfold signedCoefficient
  simp_rw [sub_mul, mul_assoc]
  rw [sum_sub_distrib, ← mul_sum]
  congr 1
  · simp_rw [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro P hP
    rw [delta_sum _ P _ _ (hPmem P hP)]
    split_ifs <;> ring
  · congr 1
    simp_rw [sum_mul, mul_assoc]
    rw [sum_comm]
    apply sum_congr rfl
    intro P hP
    rw [← mul_sum]
    congr 1
    simp_rw [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    rw [delta_sum _ _ _ _ (hqmem P hP a ha)]
    split_ifs <;> ring

theorem value_on_window (A : AtomSystem) (m : ℕ) (hm : 4096 < m)
    (hH : mean A < 17 / 16) (x : ℕ) :
    (∀ n : ℕ, F A m n = ∑ D ∈ certificateSupport A m,
      signedCoefficient A m D * (if D ∣ n then 1 else 0)) ∧
    (∀ D ∈ certificateSupport A m, 0 < signedCoefficient A m D →
      D ∈ carriers A m ∧ (D : ℝ) < (m : ℝ) ^ (1 / 4 : ℝ)) ∧
    (∀ D ∈ certificateSupport A m, signedCoefficient A m D < 0 →
      ∃ P ∈ carriers A m, ∃ a ∈ retained A m, ¬ a.1 ∣ P ∧
        D = P * modulus a ∧ (D : ℝ) < (m : ℝ) ^ (5 / 16 : ℝ)) ∧
    (141 / 64 : ℝ) * LB A m ≤ ∑ n ∈ Icc (x + 1) (x + m), F A m n := by
  exact ⟨F_signed_expansion A m, (fun D hD hp => positive_support A m hm D hp),
    (fun D hD hn => negative_support A m hm D hn), F_window_lower A m hm hH x⟩

#print axioms value_on_window
#print axioms windowCount_upper_two
#print axioms negative_modulus_small
#print axioms beta_bounds
#print axioms beta_telescope
#print axioms positive_support
#print axioms negative_support
#print axioms total_carried_mass
#print axioms F_expanded
#print axioms F_window_lower
#print axioms F_signed_expansion

end
end Erdos708SparseCore
