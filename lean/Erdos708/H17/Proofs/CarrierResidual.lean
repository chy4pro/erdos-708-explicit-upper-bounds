import Erdos708.H17.Proofs.CarrierGeometry
open Finset BigOperators
open scoped NNReal
namespace Erdos708H17.Proofs
noncomputable section
attribute [local instance] Classical.propDecidable

lemma prime_dvd_carrier (A : AtomSystem) (m P p : ℕ) (hP : P ∈ carriers A m)
    (hp : Nat.Prime p) : p ∣ P ↔ ∃ a ∈ Rounded.effective (small A m) m P, a.1 = p := by
  conv_lhs => rw [(carrier_data A m P hP).2.1]
  rw [hp.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨a, ha, hpa⟩
    have hap := (Rounded.carrier_retained_prime (small A m) m (mem_filter.mp ha).1).1
    exact ⟨a, ha, ((Nat.prime_dvd_prime_iff_eq hp hap).mp (hp.dvd_of_dvd_pow hpa)).symm⟩
  · rintro ⟨a, ha, hap⟩
    refine ⟨a, ha, ?_⟩
    have hj := (Rounded.carrier_retained_prime (small A m) m (mem_filter.mp ha).1).2
    dsimp only [Rounded.modulus]
    rw [hap]
    exact dvd_pow_self p (by omega : a.2 ≠ 0)

lemma bp_on_carrier_prime (A : AtomSystem) (m k : ℕ) (hk : k ∈ hot A m)
    (p : ℕ) (hp : p.Prime) (hpP : p ∣ carrierAt A m k) :
    bp A m p k = bp A m p (carrierAt A m k) := by
  have hP : carrierAt A m k ∈ carriers A m := mem_image_of_mem _ hk
  obtain ⟨a, ha, hap⟩ := (prime_dvd_carrier A m _ p hP hp).mp hpP
  unfold bp
  rw [← hap, Rounded.effective_value_eq_bp (small A m) m k a
    (Rounded.effective_prefix_subset (small A m) m k (carrierLength A m k) ha),
    Rounded.effective_value_eq_bp (small A m) m _ a ha]

lemma carrier_divides (A : AtomSystem) (m k : ℕ) : carrierAt A m k ∣ k :=
  Rounded.prefix_dvd (small A m) m k (carrierLength A m k)

lemma carrier_split (A : AtomSystem) (m k : ℕ) (hk : k ∈ hot A m) :
    B A m k = mu A m (carrierAt A m k) +
      ∑ p ∈ (Rounded.primes (small A m)).filter (fun p => ¬ p ∣ carrierAt A m k),
        bp A m p (k / carrierAt A m k) := by
  classical
  let P := carrierAt A m k
  have hdiv : P ∣ k := carrier_divides A m k
  have hkeq : P * (k / P) = k := Nat.mul_div_cancel' hdiv
  have hin : (∑ p ∈ (Rounded.primes (small A m)).filter (fun p => p ∣ P), bp A m p k) = mu A m P := by
    calc
      _ = ∑ p ∈ (Rounded.primes (small A m)).filter (fun p => p ∣ P), bp A m p P := by
        apply sum_congr rfl
        intro p hp
        obtain ⟨a, ha, hap⟩ := mem_image.mp (mem_filter.mp hp).1
        have hprime : Nat.Prime p := hap ▸ ((small A m).prime_of_mem a ha).1
        exact bp_on_carrier_prime A m k hk p hprime (mem_filter.mp hp).2
      _ = _ := by
        change _ = ∑ p ∈ Rounded.primes (small A m), bp A m p P
        apply sum_subset (filter_subset _ _)
        intro p hp hn
        exact Rounded.bp_zero_of_not_dvd (small A m) m p P (fun h => hn (mem_filter.mpr ⟨hp,h⟩))
  calc
    _ = (∑ p ∈ (Rounded.primes (small A m)).filter (fun p => p ∣ P), bp A m p k) +
        ∑ p ∈ (Rounded.primes (small A m)).filter (fun p => ¬ p ∣ P), bp A m p k :=
      (sum_filter_add_sum_filter_not _ _ _).symm
    _ = _ := by
      rw [hin]
      congr 1
      apply sum_congr rfl
      intro p hp
      change Rounded.bp (small A m) m p k = Rounded.bp (small A m) m p (k / P)
      conv_lhs => rw [← hkeq]
      exact Rounded.bp_remove_coprime (small A m) m P p _ (mem_filter.mp hp).2

lemma outside_value_le_theta (A : AtomSystem) (m k : ℕ) (hk : k ∈ hot A m)
    {a : ℕ × ℕ} (ha : a ∈ Rounded.effective (small A m) m k)
    (haP : ¬ a.1 ∣ carrierAt A m k) :
    (Rounded.levelValue (small A m) a : ℝ) ≤ theta A m (carrierAt A m k) := by
  let P := carrierAt A m k
  let l := Rounded.effectiveList (small A m) m k
  let i := carrierLength A m k
  have hP : P ∈ carriers A m := mem_image_of_mem _ hk
  have hpre : (Rounded.prefixLevels (small A m) m k i).toFinset = Rounded.effective (small A m) m P := by
    have he := congrArg List.toFinset (Rounded.effectiveList_prefix (small A m) m k i)
    rw [Rounded.effectiveList, Rounded.orderedLevels_toFinset] at he
    exact he.symm
  have hnot : a ∉ Rounded.prefixLevels (small A m) m k i := by
    intro hh
    have he : a ∈ Rounded.effective (small A m) m P := hpre ▸ List.mem_toFinset.mpr hh
    exact haP ((prime_dvd_carrier A m P a.1 hP
      (Rounded.carrier_retained_prime (small A m) m (mem_filter.mp ha).1).1).mpr ⟨a,he,rfl⟩)
  have hal : a ∈ l := by
    apply List.mem_toFinset.mp
    simpa only [l, Rounded.effectiveList, Rounded.orderedLevels_toFinset] using ha
  have hadrop : a ∈ l.drop i := by
    have hh : a ∈ l.take i ++ l.drop i := by rw [List.take_append_drop]; exact hal
    exact (List.mem_append.mp hh).resolve_left hnot
  have hlast : lastLevel A m P ∈ l.take i := by
    apply List.mem_toFinset.mp
    rw [show l.take i = Rounded.prefixLevels (small A m) m k i from rfl, hpre]
    exact (carrier_data A m P hP).1
  have hord : l.Pairwise (fun a b => Rounded.orderKey (small A m) a ≤ Rounded.orderKey (small A m) b) := by
    have hh : (l.map (Rounded.orderKey (small A m))).Pairwise (· ≤ ·) := by
      rw [show l = Rounded.orderedLevels (small A m) (Rounded.effective (small A m) m k) from rfl,
        Rounded.map_orderedLevels]
      convert pairwise_sort ((Rounded.effective (small A m) m k).image (Rounded.orderKey (small A m))) (· ≤ ·) using 1 <;> congr 1
    simpa only [List.pairwise_map] using hh
  rw [← List.take_append_drop i l] at hord
  have hkey := (List.pairwise_append.mp hord).2.2 _ hlast _ hadrop
  have hheight : Rounded.levelHeight (small A m) (lastLevel A m P) ≤ Rounded.levelHeight (small A m) a :=
    Prod.Lex.monotone_fst _ _ hkey
  exact_mod_cast (pow_le_pow_of_le_one (by positivity : (0 : ℝ≥0) ≤ (2 : ℝ≥0)⁻¹)
    (by norm_num : (2 : ℝ≥0)⁻¹ ≤ 1) hheight)

lemma bp_outside_le_theta (A : AtomSystem) (m k : ℕ) (hk : k ∈ hot A m)
    (p : ℕ) (hpP : ¬ p ∣ carrierAt A m k) :
    bp A m p (k / carrierAt A m k) ≤ theta A m (carrierAt A m k) := by
  classical
  have hdiv := carrier_divides A m k
  have heq := Nat.mul_div_cancel' hdiv
  unfold bp
  rw [← Rounded.bp_remove_coprime (small A m) m _ p _ hpP, heq]
  by_cases hh : ((Rounded.effective (small A m) m k).filter (fun a => a.1 = p)).Nonempty
  · obtain ⟨a,ha⟩ := hh
    rw [← (mem_filter.mp ha).2, Rounded.effective_value_eq_bp (small A m) m k a (mem_filter.mp ha).1]
    exact outside_value_le_theta A m k hk (mem_filter.mp ha).1 ((mem_filter.mp ha).2 ▸ hpP)
  · rw [Rounded.bp_eq_effective_sum, not_nonempty_iff_eq_empty.mp hh, sum_empty]
    exact (theta_pos A m _).le

#print axioms carrier_split
#print axioms bp_outside_le_theta
end
end Erdos708H17.Proofs
