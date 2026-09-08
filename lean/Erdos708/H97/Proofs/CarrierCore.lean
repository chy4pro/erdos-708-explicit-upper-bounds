import Erdos708.H97.Proofs.Geometry
open Finset BigOperators
open scoped NNReal
namespace Erdos708H97.Proofs
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
    norm_num [T] at this
    linarith
  have hs := Nat.find_spec hex
  have hpos : 0 < Nat.find hex := by
    by_contra hh
    have hz : Nat.find hex = 0 := by omega
    rw [hz] at hs
    norm_num [Rounded.partialMass, Rounded.prefixLevels] at hs
  have hlen := Nat.find_min' hex (show 1 < Rounded.partialMass (small A m) m k
    (Rounded.effectiveList (small A m) m k).length by rw [hfull]; have := (mem_filter.mp hk).2; norm_num [T] at this; linarith)
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
  exact_mod_cast Rounded.level_pos (Rounded.levelHeight (small A m) (lastLevel A m P))
lemma theta_le_one (A : AtomSystem) (m P : ℕ) : theta A m P ≤ 1 := by
  exact_mod_cast Rounded.level_le_one (Rounded.levelHeight (small A m) (lastLevel A m P))

lemma carrier_mu_gt_one (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) : 1 < mu A m P := by
  obtain ⟨k,i,hk,hi,hw,rfl⟩ := carrier_witness A m P hP
  unfold mu B
  rw [Rounded.B_prefix_eq_partialMass]
  exact hw.1

lemma carrier_mu_upper (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) :
    mu A m P ≤ 1+theta A m P := by
  have hd := carrier_data A m P hP
  change Rounded.B (small A m) m P ≤ _
  rw [Rounded.B_eq_effective_sum, ← sum_erase_add _ _ hd.1]
  change _ + theta A m P ≤ _
  linarith [hd.2.2.1]

lemma carrier_pos (A : AtomSystem) (m P : ℕ) (hP : P ∈ carriers A m) : 0 < P := by
  rw [(carrier_data A m P hP).2.1]
  exact prod_pos (fun a ha => Rounded.retained_modulus_pos (small A m) m (mem_filter.mp ha).1)

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
  by_cases hh : T < B A m k
  · rw [if_pos hh, max_eq_left (by linarith)]
  · rw [if_neg hh, max_eq_right (by linarith)]

#print axioms carrier_mu_upper
#print axioms total_carried_mass
end
end Erdos708H97.Proofs
