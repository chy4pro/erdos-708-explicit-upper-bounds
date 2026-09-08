import Erdos708.H97.Proofs.Levels
import Erdos708.H97.Proofs.Lemma2
open Finset BigOperators
open scoped NNReal
namespace Erdos708H97.Rounded
noncomputable section
lemma rounding_retained_mem_atoms (A : AtomSystem) (m : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) : a ∈ A.atoms :=
  (mem_filter.mp (mem_filter.mp ha).1).1

lemma retained_cumulative_pos (A : AtomSystem) (m : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) : 0 < cumulative A a.1 a.2 :=
  (mem_filter.mp (mem_filter.mp ha).1).2.1

lemma cumulative_nonneg (A : AtomSystem) (p j : ℕ) : 0 ≤ cumulative A p j :=
  sum_nonneg (fun a ha => A.weight_nonneg a (mem_filter.mp ha).1)

lemma cumulative_le_one (A : AtomSystem) (p j : ℕ) : cumulative A p j ≤ 1 := by
  apply le_trans _ (A.perPrime_le_one p)
  apply sum_le_sum_of_subset_of_nonneg
  · intro a ha
    exact mem_filter.mpr ⟨(mem_filter.mp ha).1, (mem_filter.mp ha).2.1⟩
  · intro a ha _
    exact A.weight_nonneg a (mem_filter.mp ha).1

lemma cumulative_mono (A : AtomSystem) (p : ℕ) {i j : ℕ} (hij : i ≤ j) :
    cumulative A p i ≤ cumulative A p j := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro a ha
    exact mem_filter.mpr ⟨(mem_filter.mp ha).1, (mem_filter.mp ha).2.1,
      (mem_filter.mp ha).2.2.trans hij⟩
  · intro a ha _
    exact A.weight_nonneg a (mem_filter.mp ha).1

lemma retained_value_le_cumulative (A : AtomSystem) (m : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) : (levelValue A a : ℝ) ≤ cumulative A a.1 a.2 := by
  simpa [levelValue, levelHeight] using rounded_le (retained_cumulative_pos A m ha)

lemma retained_value_mono (A : AtomSystem) (m : ℕ) {a b : ℕ × ℕ}
    (ha : a ∈ retained A m) (hb : b ∈ retained A m) (hp : a.1 = b.1) (hj : a.2 ≤ b.2) :
    levelValue A a ≤ levelValue A b := by
  apply level_antitone
  apply roundIndex_antitone (retained_cumulative_pos A m ha)
  simpa only [hp] using cumulative_mono A b.1 hj

def ap (A : AtomSystem) (p n : ℕ) : ℝ :=
  ∑ a ∈ A.atoms.filter (fun a => a.1 = p ∧ modulus a ∣ n), A.weight a

lemma ap_nonneg (A : AtomSystem) (p n : ℕ) : 0 ≤ ap A p n :=
  sum_nonneg (fun a ha => A.weight_nonneg a (mem_filter.mp ha).1)

lemma bp_le_ap (A : AtomSystem) (m p n : ℕ) : bp A m p n ≤ ap A p n := by
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

lemma B_le_S (A : AtomSystem) (m n : ℕ) : B A m n ≤ S A n := by
  calc
    _ ≤ ∑ p ∈ primes A, ap A p n := sum_le_sum (fun p hp => bp_le_ap A m p n)
    _ = _ := by
      have hmap : ∀ a ∈ A.atoms.filter (fun a => modulus a ∣ n), a.1 ∈ primes A := by
        intro a ha
        exact mem_image_of_mem Prod.fst (mem_filter.mp ha).1
      dsimp only [ap, S]
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

lemma RB_le_R (A : AtomSystem) (m x : ℕ) : RB A m x ≤ R A x m := by
  unfold RB R hingeSum
  apply sum_le_sum
  intro n hn
  exact max_le_max (sub_le_sub_right (B_le_S A m n) 1) le_rfl

lemma sum_jumps_eq_sup {ι : Type*} (s : Finset ι) (key : ι → ℕ) (v : ι → ℝ≥0)
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

lemma increment_nonneg (A : AtomSystem) (m : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) : 0 ≤ increment A m a := by
  apply sub_nonneg.mpr
  have hh : previousValue A m a ≤ levelValue A a := by
    apply Finset.sup_le
    intro b hb
    obtain ⟨hb, hbp, hbj⟩ := mem_filter.mp hb
    exact retained_value_mono A m hb ha hbp hbj.le
  exact_mod_cast hh

lemma increments_telescope (A : AtomSystem) (m p n : ℕ) :
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

lemma B_eq_increment_sum (A : AtomSystem) (m n : ℕ) :
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

lemma average_divisor_sum {ι : Type*} (s : Finset ι) (q : ι → ℕ) (w : ι → ℝ)
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

lemma HB_le_mean (A : AtomSystem) (m : ℕ) : HB A m ≤ mean A := by
  let Q := ∏ a ∈ A.atoms, modulus a
  have hQ : 0 < Q := prod_pos (fun a ha => pow_pos (A.prime_of_mem a ha).1.pos _)
  have hdiv : ∀ a ∈ A.atoms, modulus a ∣ Q := fun a ha => dvd_prod_of_mem modulus ha
  have hdivB : ∀ a ∈ retained A m, modulus a ∣ Q :=
    fun a ha => hdiv a (rounding_retained_mem_atoms A m ha)
  have hle : (∑ n ∈ Icc 1 Q, B A m n) ≤ ∑ n ∈ Icc 1 Q, S A n :=
    sum_le_sum (fun n hn => B_le_S A m n)
  simp_rw [B_eq_increment_sum] at hle
  change (∑ n ∈ Icc 1 Q, ∑ a ∈ (retained A m).filter (fun a => modulus a ∣ n), increment A m a) ≤
    (∑ n ∈ Icc 1 Q, ∑ a ∈ A.atoms.filter (fun a => modulus a ∣ n), A.weight a) at hle
  rw [average_divisor_sum _ _ _ Q hQ hdivB, average_divisor_sum _ _ _ Q hQ hdiv] at hle
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hh := (_root_.mul_le_mul_iff_right₀ hQreal).mp hle
  simpa only [HB, mean, modulus, Nat.cast_pow] using hh

lemma rounded_current_level (A : AtomSystem) (p n : ℕ) (hp : 0 < ap A p n) :
    ∃ a ∈ roundedLevels A, a.1 = p ∧ modulus a ∣ n ∧ ap A p n ≤ (5/4) * (levelValue A a : ℝ) := by
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
    have hh := rounding_factor hcpos (cumulative_le_one A a.1 a.2)
    simpa [levelValue, levelHeight, hap, hcum] using hh

lemma sum_ap_eq_S (A : AtomSystem) (n : ℕ) :
    (∑ p ∈ primes A, ap A p n) = S A n := by
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

lemma bp_nonneg (A : AtomSystem) (m p n : ℕ) : 0 ≤ bp A m p n :=
  (bpNN A m p n).coe_nonneg

/-- G1: each rounded prime contribution is at most one. -/
lemma bp_le_one (A : AtomSystem) (m p n : ℕ) : bp A m p n ≤ 1 :=
  (bp_le_ap A m p n).trans (Erdos708H17.Proofs.component_le_one A p n)

#print axioms B_le_S
#print axioms HB_le_mean
#print axioms rounded_current_level
end
end Erdos708H97.Rounded
