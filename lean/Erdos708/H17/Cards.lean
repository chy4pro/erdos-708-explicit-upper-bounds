import Erdos708.H17.Proofs.Lemma1
import Erdos708.H17.Proofs.Moment
import Erdos708.H17.Proofs.Lemma2
import Erdos708.H17.Proofs.Lemma4
import Erdos708.H17.Proofs.Lemma3
import Erdos708.H17.Proofs.Lemma5
import Erdos708.H17.Proofs.Pointwise
import Erdos708.H17.Proofs.Lemma8
import Erdos708.H17.Proofs.Lemma9
import Erdos708.H17.Proofs.Lemma7
open Finset BigOperators
namespace Erdos708H17
noncomputable section

/-- Lemma 1: the two cube hinges, the atom moment bound, and mean monotonicity. -/
theorem lemma1 :
    (∀ (s : Finset ℕ) (u : ℕ → ℝ), (∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1) →
      ∀ r : ℕ, 1 ≤ r → max (∑ i ∈ s, u i - (r-1 : ℕ)) 0 ≤ esymm s u r) ∧
    (∀ (s : Finset ℕ) (u : ℕ → ℝ), (∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1) →
      max (∑ i ∈ s, u i - 7/2) 0 ≤ (1/2) * esymm s u 4) ∧
    (∀ (A : AtomSystem) (N r : ℕ), 1 ≤ r →
      (∑ n ∈ Icc 1 N, esymm (Rounded.primes A) (fun p => component A p n) r) ≤
        (N : ℝ) * mean A ^ r / (Nat.factorial r : ℝ)) ∧
    (∀ A G : AtomSystem, (∀ p v : ℕ, component A p (p^v) ≤ component G p (p^v)) →
      mean A ≤ mean G)  := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s u hu r hr
    have he : r - 1 + 1 = r := by omega
    simpa only [esymm, he] using Proofs.hinge_le_esymm s u hu (r-1)
  · exact fun s u hu => Proofs.special_hinge s u hu
  · exact fun A N r _ => Proofs.atom_moment A N r
  · exact Proofs.mean_mono

/-- Lemma 2: deletion preserves all hinges at c >= 7; the small-m left side vanishes. -/
theorem lemma2 (A : AtomSystem) (m : ℕ) :
    (∀ (c : ℝ), 7 ≤ c → ∀ k ∈ Icc 1 m,
      max (S A k - c) 0 = max (S_0 A m k - c) 0) ∧
    (m < 2^48 → L A m = 0) ∧ (∀ n, S_0 A m n ≤ S A n)  := by
  exact ⟨fun c hc k hk => Proofs.deletion_hinge A m c hc k hk,
    Proofs.small_m_hinge_zero A m, fun n => Proofs.S_restrict_le A _ n⟩

/-- Lemma 3: the dense branch, including its truncated first-moment certificate. -/
theorem lemma3 (A : AtomSystem) (m : ℕ) (hm : 1 ≤ m) (hH : Hstar ≤ H A m) :
    (m : ℝ) ≤ ∑ k ∈ Icc 1 m, min (S_0 A m k) 17 ∧
    ∀ x, L A m ≤ R A x m  := by
  exact ⟨Proofs.dense_truncation A m hm hH, Proofs.dense_branch A m hm hH⟩

/-- Lemma 4: rounded domination and mean, loss six, and the cube-root cutoff. -/
theorem lemma4 (A : AtomSystem) (m : ℕ) (hm : 2^48 ≤ m) :
    (∀ n, B A m n ≤ S_0 A m n) ∧ HB A m ≤ H A m ∧
    (∀ k ∈ Icc 1 m, S_0 A m k ≤ 2 * B A m k + 6) ∧
    hingeSum (S_0 A m) 17 0 m ≤ 2 * LB A m ∧
    (∀ a ∈ Rounded.retained (small A m) m, Rounded.modulus a ^ 3 ≤ m)  := by
  have hm' : 4096 < m := by omega
  refine ⟨Rounded.B_le_S (small A m) m, Rounded.HB_le_mean (small A m) m, ?_, ?_,
    Rounded.retained_cube_le (small A m) m⟩
  · intro k hk
    exact Rounded.S_le_two_B_add6 (small A m) m k hm'
      (by have := (mem_Icc.mp hk).1; omega) (mem_Icc.mp hk).2
  · simpa only [L, LB, hingeSum, B, Rounded.LB, S_0, zero_add] using
      Rounded.L_le_two_LB (small A m) m hm' 

/-- Lemma 5: exact carrier mass, support bound, partition of mass and scale bounds. -/
theorem lemma5 (A : AtomSystem) (m : ℕ) (hm : 2^48 ≤ m) (hH : H A m < Hstar) :
    (∀ P ∈ carriers A m, 0 < P ∧ mu A m P = 1 + theta A m P ∧
      0 < theta A m P ∧ theta A m P ≤ 1 ∧
      (P : ℝ) ≤ (m : ℝ)^((1 + theta A m P)/3) ∧ P^3 ≤ m^2 ∧ 0 < nu m P) ∧
    (∑ P ∈ carriers A m, M A m P) = LB A m ∧
    (∀ P ∈ carriers A m, 0 ≤ coefficient A m P ∧
      ∀ h : ℕ, theta A m P = (2 : ℝ)⁻¹^h → coefficient A m P ≤ epsilon h)  := by
  refine ⟨?_, Proofs.total_carried_mass A m, ?_⟩
  · intro P hP
    exact ⟨Proofs.carrier_pos A m P hP, Proofs.carrier_mu_exact A m P hP,
      Proofs.theta_pos A m P, Proofs.theta_le_one A m P,
      Proofs.carrier_size A m (by omega) P hP, Proofs.carrier_cube A m (by omega) P hP,
      Proofs.carrier_nu_pos A m (by omega) P hP⟩
  · intro P hP
    exact ⟨Proofs.coefficient_nonneg A m P, Proofs.coefficient_scale_bound A m hm hH P hP⟩

/-- Lemma 6: the signed expansion, bounded negative support and exact counting reduction. -/
theorem lemma6 (A : AtomSystem) (m : ℕ) (hm : 2^48 ≤ m) (hH : H A m < Hstar) :
    (∀ n, F A m n = ∑ D ∈ certificateSupport A m,
      signedCoefficient A m D * (if D ∣ n then 1 else 0)) ∧
    (∀ D ∈ certificateSupport A m, signedCoefficient A m D < 0 → D ≤ m) ∧
    (Summable numericTerm → ∀ n, F A m n ≤
      (∑' h, numericTerm h) * max (B A m n - 1) 0)  := by
  exact ⟨Proofs.F_signed_expansion A m, fun D _ hD => Proofs.negative_support_le A m (by omega) D hD,
    fun hs n => Proofs.counting_reduction A m hm hH hs n⟩

/-- Lemma 7: convergence and the strict numerical sum bound over all dyadic scales. -/
theorem lemma7 : Summable numericTerm ∧ (∑' h, numericTerm h) < 4/5 := by
  exact Proofs.numerical_sum

/-- Lemma 8: the non-strict value bound also covers the case LB = 0. -/
theorem lemma8 (A : AtomSystem) (m : ℕ) (hm : 2^48 ≤ m) (hH : H A m < Hstar) (x : ℕ) :
    (62248/30583 : ℝ) * LB A m ≤ ∑ n ∈ Icc (x+1) (x+m), F A m n := by
  exact Proofs.window_value A m hm hH x

/-- Lemma 9: sparse completion, with the estimates from Lemmas 2,4,6,7,8 explicit. -/
theorem lemma9 (A : AtomSystem) (m x : ℕ)
    (hleft : L A m ≤ 2 * LB A m) (hdom : RB A m x ≤ R A x m)
    (hpoint : ∀ n, F A m n ≤ (4/5 : ℝ) * max (B A m n - 1) 0)
    (hwindow : (62248/30583 : ℝ) * LB A m ≤ ∑ n ∈ Icc (x+1) (x+m), F A m n) :
    L A m ≤ (30583/38905 : ℝ) * RB A m x ∧ L A m ≤ R A x m := by
  exact Proofs.completion A m x hleft hdom hpoint hwindow

/-- Compose the nine cards into the threshold-17 hinge inequality. -/
theorem hinge17 : ∀ (A : AtomSystem) (m x : ℕ),
    (∑ k ∈ Icc 1 m, max (S A k - 17) 0) ≤
      ∑ b ∈ Icc (x+1) (x+m), max (S A b - 1) 0 := by
  intro A m x
  suffices hh : L A m ≤ R A x m by
    simpa only [L, R, hingeSum, zero_add] using hh
  by_cases hm : m < 2^48
  · rw [(lemma2 A m).2.1 hm]
    unfold R hingeSum
    exact sum_nonneg (fun _ _ => le_max_right _ _)
  have hm' : 2^48 ≤ m := le_of_not_gt hm
  by_cases hH : Hstar ≤ H A m
  · exact (lemma3 A m (by omega) hH).2 x
  have hH' := lt_of_not_ge hH
  obtain ⟨hB, hHB, hround, hleft, hmod⟩ := lemma4 A m hm'
  have hL : L A m ≤ 2 * LB A m := by
    have heq : L A m = hingeSum (S_0 A m) 17 0 m := by
      unfold L hingeSum
      apply sum_congr rfl
      intro k hk
      exact (lemma2 A m).1 17 (by norm_num) k (by simpa only [zero_add] using hk)
    rw [heq]
    exact hleft
  have hdom : RB A m x ≤ R A x m := by
    unfold RB R hingeSum
    apply sum_le_sum
    intro n hn
    exact max_le_max (sub_le_sub_right ((hB n).trans ((lemma2 A m).2.2 n)) 1) le_rfl
  have hpoint : ∀ n, F A m n ≤ (4/5 : ℝ) * max (B A m n - 1) 0 := by
    intro n
    exact ((lemma6 A m hm' hH').2.2 lemma7.1 n).trans
      (mul_le_mul_of_nonneg_right lemma7.2.le (le_max_right _ _))
  exact (lemma9 A m x hL hdom hpoint (lemma8 A m hm' hH' x)).2

#print axioms lemma1
#print axioms lemma2
#print axioms lemma3
#print axioms lemma4
#print axioms lemma5
#print axioms lemma6
#print axioms lemma7
#print axioms lemma8
#print axioms lemma9
#print axioms hinge17
end
end Erdos708H17
