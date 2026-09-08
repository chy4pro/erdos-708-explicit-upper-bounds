import Erdos708.H97.Defs
open Finset BigOperators
namespace Erdos708H97
noncomputable section

/-- Manuscript Lemma 1, including the optimized majorant (G6). -/
theorem lemma1 :
    (∀ (A : AtomSystem) (N r : ℕ),
      (∑ n ∈ Icc 1 N, esymm (Rounded.primes A) (fun p => component A p n) r) ≤
        (N : ℝ)*mean A^r/(Nat.factorial r : ℝ)) ∧
    (∀ A G : AtomSystem, (∀ n : ℕ, S A n ≤ S G n) → mean A ≤ mean G) ∧
    (∀ (s : Finset ℕ) (u : ℕ → ℝ) (a : ℝ) (r : ℕ),
      (∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1) → 2 ≤ r → (r : ℝ)-1 ≤ a →
      max (∑ i ∈ s, u i-a) 0 ≤ hingeMajorant a r * esymm s u r) := by
  sorry

/-- Lemma 2: all thresholds at least seven; dense branch at 97/10. -/
theorem lemma2 (A : AtomSystem) (m : ℕ) :
    (∀ c : ℝ, 7 ≤ c → ∀ k ∈ Icc 1 m,
      max (S A k-c) 0 = max (S_0 A m k-c) 0) ∧
    (∀ n, S_0 A m n ≤ S A n) ∧
    (m ≤ 1 → L A m = 0) ∧
    (1 ≤ m → Hstar ≤ H A m →
      (m : ℝ) ≤ ∑ k ∈ Icc 1 m, min (S_0 A m k) (97/10)) ∧
    (1 ≤ m → Hstar ≤ H A m → ∀ x, L A m ≤ R A x m) := by
  sorry

/-- Lemma 3: four-mantissa rounding; m >= 2 is exactly the log hypothesis (G2). -/
theorem lemma3 (A : AtomSystem) (m : ℕ) (hm : 2 ≤ m) :
    (∀ n, B A m n ≤ S_0 A m n) ∧ HB A m ≤ H A m ∧
    (∀ p n, 0 ≤ bp A m p n ∧ bp A m p n ≤ 1) ∧
    (∀ k ∈ Icc 1 m, S_0 A m k ≤ rho*B A m k+D0) ∧
    hingeSum (S_0 A m) (97/10) 0 m ≤ rho*LB A m ∧
    (∀ a ∈ Rounded.retained (small A m) m, Rounded.modulus a^3 ≤ m) := by
  sorry

/-- Lemma 4: no large-m assumption. G1 gives the cofactor bound 210. -/
theorem lemma4 (A : AtomSystem) (m : ℕ) :
    (∀ P ∈ carriers A m, 0 < P ∧ 1 < mu A m P ∧
      mu A m P ≤ 1+theta A m P ∧ 0 < theta A m P ∧ theta A m P ≤ 1 ∧
      P^3 ≤ m^2 ∧ 210 ≤ nu m P ∧
      (m : ℝ)/((P : ℝ)*(nu m P : ℝ)) < gamma) ∧
    (∑ P ∈ carriers A m, M A m P) = LB A m ∧
    (∀ P ∈ carriers A m, ∀ a ∈ Rounded.retained (small A m) m,
      P*Rounded.modulus a ≤ m) := by
  sorry

/-- Lemma 5: the true cofactor interval incurs no gamma loss. -/
theorem lemma5 (A : AtomSystem) (m : ℕ) (hH : H A m < Hstar) :
    ∀ P ∈ carriers A m, 0 ≤ coefficient A m P ∧
      coefficient A m P ≤ epsilon (theta A m P) (mu A m P) := by
  sorry

/-- Lemma 6: signed support and counting, using the tail substitute on tail scales. -/
theorem lemma6 (A : AtomSystem) (m : ℕ) (hH : H A m < Hstar) :
    (∀ n, F A m n = ∑ D ∈ certificateSupport A m,
      signedCoefficient A m D*(if D ∣ n then 1 else 0)) ∧
    (∀ D ∈ certificateSupport A m, signedCoefficient A m D < 0 → D ≤ m) ∧
    ((∀ P ∈ carriers A m, coefficient A m P ≤ tailEpsilon (theta A m P)) →
      Summable tailTerm → ∀ n, F A m n ≤
        lambda*(finiteTotal+∑' r, tailTerm r)*max (B A m n-1) 0) := by
  sorry

/-- Lemma 7: every one of the 29 finite scales, grouped as in (16). -/
theorem lemma7 :
    finiteGroup 2 < 24680/10^6 ∧ finiteGroup 3 < 128711/10^6 ∧
    finiteGroup 4 < 25773/10^6 ∧ finiteGroup 5 < 5665/10^6 ∧
    finiteGroup 6 < 1025/10^6 ∧ finiteGroup 7 < 150/10^6 ∧
    finiteGroup 8 < 21/10^6 ∧ finiteGroup 9 < 3/10^6 ∧
    finiteTotal < 187/1000 := by
  sorry

/-- Lemma 8: exponential coefficients and the entire infinite tail. -/
theorem lemma8 :
    (∀ (A : AtomSystem) (m : ℕ), H A m < Hstar →
      ∀ P ∈ carriers A m, coefficient A m P ≤ tailEpsilon (theta A m P)) ∧
    Summable tailTerm ∧ (∑' r, tailTerm r) ≤ tailBound ∧ tailBound < 3/1000 := by
  sorry

/-- Lemma 9: window value and completion, with no large-m assumption. -/
theorem lemma9 (A : AtomSystem) (m : ℕ) (hH : H A m < Hstar) (x : ℕ) :
    (718539/573440 : ℝ)*LB A m ≤ ∑ n ∈ Icc (x+1) (x+m), F A m n := by
  sorry

/-- The exact atom-system statement, including m=0, matching the H17 convention. -/
theorem hinge97 : ∀ (A : AtomSystem) (m x : ℕ),
    hingeSum (S A) (97/10) 0 m ≤ hingeSum (S A) 1 x m := by
  sorry
end
end Erdos708H97
