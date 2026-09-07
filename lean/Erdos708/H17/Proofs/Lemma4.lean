import Erdos708.H17.Proofs.Lemma2
open Finset BigOperators
open scoped NNReal
namespace Erdos708H17.Rounded
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

lemma exists_dyadic_le {u : ℝ} (hu : 0 < u) : ∃ h : ℕ, (2 : ℝ)⁻¹ ^ h ≤ u := by
  obtain ⟨h, hh⟩ := exists_pow_lt_of_lt_one hu (by norm_num : (2 : ℝ)⁻¹ < 1)
  exact ⟨h, hh.le⟩

lemma dyadic_le {u : ℝ} (hu : 0 < u) : (2 : ℝ)⁻¹ ^ dyadicHeight u ≤ u := by
  rw [dyadicHeight, dif_pos (exists_dyadic_le hu)]
  exact Nat.find_spec (exists_dyadic_le hu)

lemma lt_twice_dyadic {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    u < 2 * (2 : ℝ)⁻¹ ^ dyadicHeight u := by
  rw [dyadicHeight, dif_pos (exists_dyadic_le hu)]
  generalize heq : Nat.find (exists_dyadic_le hu) = h
  cases h with
  | zero => norm_num; linarith
  | succ h =>
    have hlt : u < (2 : ℝ)⁻¹ ^ h :=
      lt_of_not_ge (Nat.find_min (exists_dyadic_le hu) (by omega))
    convert hlt using 1 <;> ring

lemma dyadicHeight_antitone {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    dyadicHeight v ≤ dyadicHeight u := by
  rw [dyadicHeight, dif_pos (exists_dyadic_le (hu.trans_le huv)),
    dyadicHeight, dif_pos (exists_dyadic_le hu)]
  exact Nat.find_min' _ ((Nat.find_spec (exists_dyadic_le hu)).trans huv)

lemma retained_value_le_cumulative (A : AtomSystem) (m : ℕ) {a : ℕ × ℕ}
    (ha : a ∈ retained A m) : (levelValue A a : ℝ) ≤ cumulative A a.1 a.2 := by
  simpa [levelValue, levelHeight] using dyadic_le (retained_cumulative_pos A m ha)

lemma retained_value_mono (A : AtomSystem) (m : ℕ) {a b : ℕ × ℕ}
    (ha : a ∈ retained A m) (hb : b ∈ retained A m) (hp : a.1 = b.1) (hj : a.2 ≤ b.2) :
    levelValue A a ≤ levelValue A b := by
  apply pow_le_pow_of_le_one (by positivity) (by norm_num : (2 : ℝ≥0)⁻¹ ≤ 1)
  apply dyadicHeight_antitone (retained_cumulative_pos A m ha)
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

lemma local_rounding_cost (A : AtomSystem) (m p k : ℕ) (hm : 4096 < m)
    (a : ℕ × ℕ) (ha : a ∈ roundedLevels A) (hap : a.1 = p) (hak : modulus a ∣ k)
    (hnear : ap A p k < 2 * (levelValue A a : ℝ)) :
    ap A p k ≤ 2 * bp A m p k + 6 * Real.log (modulus a) / Real.log m := by
  have hmlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have ht0 : (0 : ℝ) ≤ levelValue A a := (levelValue A a).coe_nonneg
  have hb0 : 0 ≤ bp A m p k := (bpNN A m p k).coe_nonneg
  have hqlog : 0 ≤ Real.log (modulus a : ℝ) := Real.log_natCast_nonneg _
  by_cases hret : modulus a ^ (3 * 2 ^ levelHeight A a) ≤ m
  · have ham : a ∈ retained A m := mem_filter.mpr ⟨ha, hret⟩
    have hb : (levelValue A a : ℝ) ≤ bp A m p k := by
      have hmem : a ∈ (retained A m).filter (fun b => b.1 = p ∧ modulus b ∣ k) :=
        mem_filter.mpr ⟨ham, hap, hak⟩
      have hsup : levelValue A a ≤ bpNN A m p k := Finset.le_sup hmem
      exact_mod_cast hsup
    have hc0 : 0 ≤ 6 * Real.log (modulus a : ℝ) / Real.log (m : ℝ) := by positivity
    linarith
  · have hlarge : m < modulus a ^ (3 * 2 ^ levelHeight A a) := lt_of_not_ge hret
    have hlog := Real.log_lt_log (by exact_mod_cast (by omega : 0 < m))
      (show (m : ℝ) < (modulus a ^ (3 * 2 ^ levelHeight A a) : ℕ) by exact_mod_cast hlarge)
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_pow] at hlog
    norm_num only [Nat.cast_ofNat] at hlog
    have hcancel : (levelValue A a : ℝ) * (2 : ℝ) ^ levelHeight A a = 1 := by
      simp [levelValue, inv_pow]
    have hcost : (levelValue A a : ℝ) * Real.log m ≤ 3 * Real.log (modulus a : ℝ) := by
      calc
        _ ≤ (levelValue A a : ℝ) * (3 * (2 : ℝ) ^ levelHeight A a * Real.log (modulus a : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog.le ht0
        _ = 3 * Real.log (modulus a : ℝ) := by
          calc
            _ = 3 * Real.log (modulus a : ℝ) *
                ((levelValue A a : ℝ) * (2 : ℝ) ^ levelHeight A a) := by ring
            _ = _ := by rw [hcancel]; ring
    have hnearlog := mul_le_mul_of_nonneg_right hnear.le hmlog.le
    have hc : ap A p k ≤ 6 * Real.log (modulus a : ℝ) / Real.log (m : ℝ) := by
      apply (le_div_iff₀ hmlog).2
      nlinarith
    linarith

lemma S_le_two_B_add6 (A : AtomSystem) (m k : ℕ) (hm : 4096 < m)
    (hk : 0 < k) (hkm : k ≤ m) : S A k ≤ 2 * B A m k + 6 := by
  classical
  have hex (p : ℕ) : ∃ e : ℕ, p ^ e ∣ k ∧
      ap A p k ≤ 2 * bp A m p k + 6 * Real.log (p ^ e : ℕ) / Real.log m := by
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
      (2 * bp A m p k + 6 * Real.log (p ^ e p : ℕ) / Real.log m)) =
      2 * B A m k + 6 * (∑ p ∈ primes A, Real.log (p ^ e p : ℕ)) / Real.log m := by
    rw [sum_add_distrib, ← mul_sum, ← sum_div, ← mul_sum]
    rfl
  rw [sum_ap_eq_S, hform] at hsum
  have hmlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hratio : 6 * (∑ p ∈ primes A, Real.log (p ^ e p : ℕ)) / Real.log m ≤ 6 := by
    apply (div_le_iff₀ hmlog).2
    linarith
  linarith

lemma L_le_two_LB (A : AtomSystem) (m : ℕ) (hm : 4096 < m) : L A m ≤ 2 * LB A m := by
  simp only [L, hingeSum, zero_add]
  rw [LB, mul_sum]
  apply sum_le_sum
  intro k hk
  have hpoint := S_le_two_B_add6 A m k hm (by have := (mem_Icc.mp hk).1; omega) (mem_Icc.mp hk).2
  apply max_le
  · have hh := le_max_left (B A m k - 11/2) 0
    linarith
  · exact mul_nonneg (by norm_num) (le_max_right _ _)

theorem rounding (A : AtomSystem) (m : ℕ) (hm : 4096 < m) (x : ℕ) :
    HB A m ≤ mean A ∧ RB A m x ≤ R A x m ∧ L A m ≤ 2 * LB A m := by
  exact ⟨HB_le_mean A m, RB_le_R A m x, L_le_two_LB A m hm⟩


lemma retained_cube_le (A : AtomSystem) (m : ℕ) (a : ℕ × ℕ) (ha : a ∈ retained A m) :
    modulus a ^ 3 ≤ m := by
  have hq : 1 ≤ modulus a := (pow_pos (A.prime_of_mem a (rounding_retained_mem_atoms A m ha)).1.pos _)
  have he : 3 ≤ 3 * 2^levelHeight A a := by
    have hh : 1 ≤ (2 : ℕ)^levelHeight A a := Nat.one_le_pow _ _ (by omega)
    omega
  exact (pow_le_pow_right₀ hq he).trans (mem_filter.mp ha).2

#print axioms B_le_S
#print axioms HB_le_mean
#print axioms S_le_two_B_add6
#print axioms L_le_two_LB
#print axioms retained_cube_le
end
end Erdos708H17.Rounded
