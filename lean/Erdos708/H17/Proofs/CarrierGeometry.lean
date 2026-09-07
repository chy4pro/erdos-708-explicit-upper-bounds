import Erdos708.H17.Proofs.Geometry
open Finset BigOperators
open scoped NNReal
namespace Erdos708H17.Proofs
noncomputable section
attribute [local instance] Classical.propDecidable

lemma carrier_index (A : AtomSystem) (m k : ℕ) (hk : k ∈ hot A m) :
    carrierLength A m k ∈ Icc 1 (Rounded.effectiveList (small A m) m k).length ∧
    1 < Rounded.partialMass (small A m) m k (carrierLength A m k) ∧
    Rounded.partialMass (small A m) m k (carrierLength A m k - 1) ≤ 1 := by
  have hfull : Rounded.partialMass (small A m) m k
      (Rounded.effectiveList (small A m) m k).length = B A m k := by
    simp only [Rounded.partialMass, Rounded.prefixLevels, List.take_length, B,
      Rounded.B_eq_effectiveList_sum]
  have hex : ∃ i, 1 < Rounded.partialMass (small A m) m k i := by
    refine ⟨(Rounded.effectiveList (small A m) m k).length, ?_⟩
    rw [hfull]
    have := (mem_filter.mp hk).2
    linarith
  have hs := Nat.find_spec hex
  have hpos : 0 < Nat.find hex := by
    by_contra hh
    have hz : Nat.find hex = 0 := by omega
    rw [hz] at hs
    norm_num [Rounded.partialMass, Rounded.prefixLevels] at hs
  have hlen := Nat.find_min' hex (show 1 < Rounded.partialMass (small A m) m k
    (Rounded.effectiveList (small A m) m k).length by rw [hfull]; have := (mem_filter.mp hk).2; linarith)
  have hprev := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
  simpa only [carrierLength, dif_pos hex] using
    (show Nat.find hex ∈ Icc 1 (Rounded.effectiveList (small A m) m k).length ∧
      1 < Rounded.partialMass (small A m) m k (Nat.find hex) ∧
      Rounded.partialMass (small A m) m k (Nat.find hex-1) ≤ 1 from
      ⟨mem_Icc.mpr ⟨hpos,hlen⟩, hs, le_of_not_gt hprev⟩)

lemma carrier_witness (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) :
    ∃ k i, k ∈ hot A m ∧ i ∈ Icc 1 (Rounded.effectiveList (small A m) m k).length ∧
      (1 < Rounded.partialMass (small A m) m k i ∧
        Rounded.partialMass (small A m) m k (i-1) ≤ 1) ∧
      P = Rounded.prefixProd (small A m) m k i := by
  obtain ⟨k,hk,rfl⟩ := mem_image.mp hP
  exact ⟨k,carrierLength A m k,hk,(carrier_index A m k hk).1,(carrier_index A m k hk).2,rfl⟩

lemma prefix_last (A : AtomSystem) (m k i : ℕ)
    (hi : i < (Rounded.effectiveList (small A m) m k).length) :
    lastLevel A m (Rounded.prefixProd (small A m) m k (i+1)) =
      (Rounded.effectiveList (small A m) m k)[i] := by
  rw [lastLevel, Rounded.effectiveList_prefix, Rounded.prefix_succ (small A m) m k i hi]
  simp

lemma carrier_data (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) :
    lastLevel A m P ∈ Rounded.effective (small A m) m P ∧
    P = ∏ b ∈ Rounded.effective (small A m) m P, Rounded.modulus b ∧
    (∑ b ∈ (Rounded.effective (small A m) m P).erase (lastLevel A m P), (Rounded.levelValue (small A m) b : ℝ)) ≤ 1 ∧
    ∀ b ∈ Rounded.effective (small A m) m P, Rounded.levelHeight (small A m) b ≤ Rounded.levelHeight (small A m) (lastLevel A m P) := by
  classical
  obtain ⟨k, i, hk, hi, hw, rfl⟩ := carrier_witness A m P hP
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := (mem_Icc.mp hi).1; omega : i ≠ 0)
  have hil : i < (Rounded.effectiveList (small A m) m k).length := by have := (mem_Icc.mp hi).2; omega
  let a := (Rounded.effectiveList (small A m) m k)[i]
  let l := Rounded.prefixLevels (small A m) m k i
  have hpre : Rounded.prefixLevels (small A m) m k (i + 1) = l ++ [a] := Rounded.prefix_succ (small A m) m k i hil
  have hlast : lastLevel A m (Rounded.prefixProd (small A m) m k (i + 1)) = a := prefix_last A m k i hil
  have heff : Rounded.effective (small A m) m (Rounded.prefixProd (small A m) m k (i + 1)) = (l ++ [a]).toFinset := by
    have hh := congrArg List.toFinset (Rounded.effectiveList_prefix (small A m) m k (i + 1))
    rw [Rounded.effectiveList, Rounded.orderedLevels_toFinset, hpre] at hh
    exact hh
  have hnot : a ∉ l.toFinset := by
    have hnd : (l ++ [a]).Nodup := hpre ▸ Rounded.prefix_nodup (small A m) m k (i + 1)
    intro ha
    exact (List.pairwise_append.mp hnd).2.2 a (List.mem_toFinset.mp ha) a (by simp) rfl
  have hset : Rounded.effective (small A m) m (Rounded.prefixProd (small A m) m k (i + 1)) = insert a l.toFinset := by
    rw [heff]
    ext b
    simp [or_comm]
  have hord : (l ++ [a]).Pairwise (fun b c => Rounded.orderKey (small A m) b ≤ Rounded.orderKey (small A m) c) := by
    rw [← hpre, ← List.pairwise_map, Rounded.prefixLevels, Rounded.effectiveList, List.map_take, Rounded.map_orderedLevels]
    convert (((Rounded.effective (small A m) m k).image (Rounded.orderKey (small A m))).pairwise_sort (· ≤ ·)).take (i := i+1) using 1
    congr 2
  rw [hlast]
  refine ⟨by rw [hset]; exact mem_insert_self _ _, ?_, ?_, ?_⟩
  · have hh := List.prod_toFinset Rounded.modulus (Rounded.prefix_nodup (small A m) m k (i + 1))
    have heff' : Rounded.effective (small A m) m (Rounded.prefixProd (small A m) m k (i + 1)) = (Rounded.prefixLevels (small A m) m k (i + 1)).toFinset := by
      rw [heff, hpre]
    rw [← heff'] at hh
    exact hh.symm
  · rw [hset, erase_insert hnot]
    have hh := List.sum_toFinset (fun b => (Rounded.levelValue (small A m) b : ℝ)) (Rounded.prefix_nodup (small A m) m k i)
    have hp := hw.2
    exact hh.trans_le hp
  · intro b hb
    have hkey : Rounded.orderKey (small A m) b ≤ Rounded.orderKey (small A m) a := by
      rw [hset] at hb
      rcases mem_insert.mp hb with rfl | hb
      · exact le_rfl
      · exact (List.pairwise_append.mp hord).2.2 b (List.mem_toFinset.mp hb) a (by simp)
    exact Prod.Lex.monotone_fst _ _ hkey


lemma theta_pos (A : AtomSystem) (m P : ℕ) : 0 < theta A m P := by
  simp only [theta, Rounded.levelValue, NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat]
  positivity
lemma theta_le_one (A : AtomSystem) (m P : ℕ) : theta A m P ≤ 1 := by
  simp only [theta, Rounded.levelValue, NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat]
  exact pow_le_one₀ (by norm_num) (by norm_num)

lemma carrier_mu_gt_one (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) : 1 < mu A m P := by
  obtain ⟨k,i,hk,hi,hw,rfl⟩ := carrier_witness A m P hP
  unfold mu B
  rw [Rounded.B_prefix_eq_partialMass]
  exact hw.1

lemma carrier_mu_exact (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) :
    mu A m P = 1 + theta A m P := by
  classical
  let a := lastLevel A m P
  let h := Rounded.levelHeight (small A m) a
  let t := (Rounded.effective (small A m) m P).erase a
  obtain ⟨ha,hprod,hprev,horder⟩ := carrier_data A m P hP
  have hθ := theta_pos A m P
  have hcancel : theta A m P * (2 : ℝ)^h = 1 := by
    simp [theta, Rounded.levelValue, h, a, inv_pow]
  have hmult (b : ℕ × ℕ) (hb : b ∈ t) :
      (Rounded.levelValue (small A m) b : ℝ) =
        (2^(h - Rounded.levelHeight (small A m) b) : ℕ) * theta A m P := by
    have hh := horder b (mem_erase.mp hb).2
    change Rounded.levelHeight (small A m) b ≤ h at hh
    apply mul_right_cancel₀ (pow_ne_zero h (by norm_num : (2:ℝ) ≠ 0))
    rw [mul_assoc, hcancel, mul_one]
    have hex : h = (h - Rounded.levelHeight (small A m) b) + Rounded.levelHeight (small A m) b := by omega
    simp only [Rounded.levelValue, NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat, Nat.cast_pow, Nat.cast_ofNat]
    rw [hex, pow_add]
    simp [inv_pow, mul_left_comm, mul_comm]
  let z : ℕ := ∑ b ∈ t, 2^(h - Rounded.levelHeight (small A m) b)
  have hsum : (∑ b ∈ t, (Rounded.levelValue (small A m) b : ℝ)) = (z : ℝ) * theta A m P := by
    dsimp only [z]
    rw [Nat.cast_sum, sum_mul]
    exact sum_congr rfl hmult
  have hsplit : mu A m P = (z : ℝ) * theta A m P + theta A m P := by
    change Rounded.B (small A m) m P = _
    rw [Rounded.B_eq_effective_sum, ← sum_erase_add _ _ ha, hsum]
    rfl
  have hprev' : (z : ℝ) * theta A m P ≤ 1 := by rw [← hsum]; exact hprev
  have hgt := carrier_mu_gt_one A m P hP
  have hzle : z ≤ 2^h := by
    have hh : (z : ℝ) ≤ (2:ℝ)^h := by nlinarith
    exact_mod_cast hh
  have hzgt : 2^h < z+1 := by
    have hh : (2:ℝ)^h < (z:ℝ)+1 := by rw [hsplit] at hgt; nlinarith
    exact_mod_cast hh
  have hz : z = 2^h := by omega
  rw [hsplit, hz]
  push_cast
  nlinarith

lemma carrier_pos (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) : 0 < P := by
  rw [(carrier_data A m P hP).2.1]
  exact prod_pos (fun a ha => Rounded.retained_modulus_pos (small A m) m (mem_filter.mp ha).1)

lemma carrier_log_bound (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) :
    Real.log (P : ℝ) ≤ mu A m P / 3 * Real.log (m : ℝ) := by
  have hfactor := (carrier_data A m P hP).2.1
  have hlogeq : Real.log (P : ℝ) = ∑ a ∈ Rounded.effective (small A m) m P, Real.log (Rounded.modulus a : ℝ) := by
    conv_lhs => rw [hfactor, Nat.cast_prod]
    apply Real.log_prod
    intro a ha
    exact_mod_cast (Rounded.retained_modulus_pos (small A m) m (mem_filter.mp ha).1).ne'
  rw [hlogeq]
  calc
    _ ≤ ∑ a ∈ Rounded.effective (small A m) m P,
        (Rounded.levelValue (small A m) a : ℝ) / 3 * Real.log (m : ℝ) :=
      sum_le_sum (fun a ha => Rounded.retained_log_bound (small A m) m (mem_filter.mp ha).1)
    _ = _ := by rw [← sum_mul, ← sum_div, ← Rounded.B_eq_effective_sum]; rfl

lemma carrier_size (A : AtomSystem) (m : ℕ) (hm : 1 ≤ m)
    (P : ℕ) (hP : P ∈ carriers A m) :
    (P : ℝ) ≤ (m : ℝ)^((1 + theta A m P)/3) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hpR : (0 : ℝ) < P := by exact_mod_cast carrier_pos A m P hP
  rw [← Real.log_le_log_iff hpR (Real.rpow_pos_of_pos hmR _), Real.log_rpow hmR]
  simpa only [carrier_mu_exact A m P hP, div_mul_eq_mul_div] using carrier_log_bound A m P hP

lemma carrier_cube (A : AtomSystem) (m : ℕ) (hm : 1 ≤ m)
    (P : ℕ) (hP : P ∈ carriers A m) : P^3 ≤ m^2 := by
  have hpR : (0 : ℝ) < P := by exact_mod_cast carrier_pos A m P hP
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hs := carrier_log_bound A m P hP
  rw [carrier_mu_exact A m P hP] at hs
  have hθ := theta_le_one A m P
  have hlog := Real.log_natCast_nonneg m
  have hle : Real.log ((P:ℝ)^3) ≤ Real.log ((m:ℝ)^2) := by
    rw [Real.log_pow, Real.log_pow]
    norm_num
    nlinarith [mul_le_mul_of_nonneg_right hθ hlog]
  have hh := (Real.log_le_log_iff (pow_pos hpR 3) (pow_pos hmR 2)).mp hle
  exact_mod_cast hh

lemma carrier_nu_pos (A : AtomSystem) (m : ℕ) (hm : 1 ≤ m)
    (P : ℕ) (hP : P ∈ carriers A m) : 0 < nu m P := by
  have hc := carrier_cube A m hm P hP
  have hp := carrier_pos A m P hP
  have hPm : P ≤ m := by
    by_contra hh
    have hmp : m < P := by omega
    have h2 : m^2 < P^2 := pow_lt_pow_left₀ hmp (by omega) (by omega)
    have h3 : P^2 ≤ P^3 := pow_le_pow_right₀ (by omega) (by omega)
    omega
  exact Nat.div_pos hPm hp

lemma carried_mass_nonneg (A : AtomSystem) (m P : ℕ) : 0 ≤ M A m P := by
  apply sum_nonneg
  intro k hk
  have hh := (mem_filter.mp (mem_filter.mp hk).1).2
  linarith
lemma coefficient_nonneg (A : AtomSystem) (m P : ℕ) : 0 ≤ coefficient A m P :=
  div_nonneg (carried_mass_nonneg A m P) (Nat.cast_nonneg _)

lemma total_carried_mass (A : AtomSystem) (m : ℕ) :
    (∑ P ∈ carriers A m, M A m P) = LB A m := by
  classical
  unfold M carriers
  rw [sum_fiberwise_of_maps_to (fun k hk => mem_image_of_mem (carrierAt A m) hk)]
  simp only [hot, LB, hingeSum, zero_add, sum_filter]
  apply sum_congr rfl
  intro k hk
  by_cases hh : 11/2 < B A m k
  · rw [if_pos hh, max_eq_left (by linarith)]
  · rw [if_neg hh, max_eq_right (by linarith)]

#print axioms carrier_mu_exact
#print axioms carrier_size
#print axioms carrier_cube
#print axioms carrier_nu_pos
#print axioms total_carried_mass
end
end Erdos708H17.Proofs
