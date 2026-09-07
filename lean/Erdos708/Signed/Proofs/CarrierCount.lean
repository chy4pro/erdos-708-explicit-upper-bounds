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

/-! Carrier geometry and the count in Lemma 14.6. -/

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

#print axioms available_weight_sum_le
#print axioms carrier_data
#print axioms weighted_subset_family_bound
#print axioms carrier_mass_range
#print axioms effectiveList_prefix
#print axioms carrier_count

end
end Erdos708SparseCore
