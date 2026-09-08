import Erdos708.H97.Proofs.TailCoefficient
import Erdos708.H97.Proofs.CountBounds
open Finset BigOperators
namespace Erdos708H97.Proofs
noncomputable section
set_option maxHeartbeats 2000000

lemma envelope_exponential (j L d N : ℕ) (hj : j ∈ Icc 4 7) (hL : 0 < L) :
    (carrierCount j L d N:ℝ)*tailEpsilon ((j:ℝ)/L) ≤
      (9*((j:ℝ)/L)/8)*(tailX j)⁻¹^d*
        Real.exp ((Real.log a0-(j:ℝ)*Real.log (tailX j))/((j:ℝ)/L)+(N:ℝ)*Real.log (tailF j)) := by
  have hj0 : (0:ℝ)<j := by exact_mod_cast (show 0<j by have := (mem_Icc.mp hj).1; omega)
  have hL0 : (0:ℝ)<L := by exact_mod_cast hL
  have hx := (tail_parameters j hj).1
  have hF : 0 < tailF j := lt_of_lt_of_le (by norm_num : (0:ℝ)<5/4) (tail_parameters j hj).2.2.1
  apply (mul_le_mul_of_nonneg_right (coefficient_envelope j L d N hj) (tailEpsilon_nonneg _ (by positivity))).trans_eq
  have heL : (tailX j)⁻¹^L = Real.exp (-(L:ℝ)*Real.log (tailX j)) := by
    rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hx,inv_pow]
  have heN : (tailF j)^N = Real.exp ((N:ℝ)*Real.log (tailF j)) := by
    rw [Real.exp_nat_mul,Real.exp_log hF]
  have hid : (Real.log a0-(j:ℝ)*Real.log (tailX j))/((j:ℝ)/L)+(N:ℝ)*Real.log (tailF j) =
      -(L:ℝ)*Real.log (tailX j)+(N:ℝ)*Real.log (tailF j)+Real.log a0*(1/((j:ℝ)/L)) := by
    field_simp
    ring
  rw [tailEpsilon,Real.rpow_def_of_pos (by norm_num [a0]),pow_add,heL,heN,hid,Real.exp_add,Real.exp_add]
  ring

lemma ratio_le_L (j L d N : ℕ) (hL : 0 < L) (hd : 1 ≤ d) : countRatio j L d N ≤ L := by
  have hL0 : (0:ℝ)<L := by exact_mod_cast hL
  have hd0 : (1:ℝ)≤d := by exact_mod_cast hd
  have hden : 0 < max ((d:ℝ)/L) ((N:ℝ)*j/L-1) := (div_pos (by linarith) hL0).trans_le (le_max_left _ _)
  have hn : max (1-max 0 ((N:ℝ)*j/L-1-d/L)/K) 0 ≤ 1 := by
    apply max_le _ (by norm_num)
    have hp : 0 ≤ max 0 ((N:ℝ)*j/L-1-d/L)/K := by unfold K; positivity
    linarith
  apply (div_le_div_of_nonneg_right hn hden.le).trans
  apply (div_le_iff₀ hden).mpr
  have hh := mul_le_mul_of_nonneg_left (le_max_left ((d:ℝ)/L) ((N:ℝ)*j/L-1)) hL0.le
  have he : (L:ℝ)*((d:ℝ)/L)=d := by field_simp
  rw [he] at hh
  linarith

lemma ratio_high (j L d N : ℕ) (hL : 0 < L) (hd : 1 ≤ d) (hdj : d ≤ j)
    (hθ : (j:ℝ)/L < 4/3) (hy : (4/3:ℝ)<(N:ℝ)*j/L-1) :
    countRatio j L d N ≤ max (K+(j:ℝ)/L-((N:ℝ)*j/L-1)) 0/(K*(4/3)) := by
  have hL0 : (0:ℝ)<L := by exact_mod_cast hL
  have hk : 0<K := by norm_num [K]
  have hdd : (d:ℝ)/L ≤ (j:ℝ)/L := div_le_div_of_nonneg_right (by exact_mod_cast hdj) hL0.le
  have hpos : 0 ≤ (N:ℝ)*j/L-1-d/L := by linarith
  have hden : (4/3:ℝ) ≤ max ((d:ℝ)/L) ((N:ℝ)*j/L-1) := hy.le.trans (le_max_right _ _)
  have hn : max (1-max 0 ((N:ℝ)*j/L-1-d/L)/K) 0 ≤
      max (K+(j:ℝ)/L-((N:ℝ)*j/L-1)) 0/K := by
    rw [max_eq_right hpos,← max_div_div_right hk.le _ _,zero_div]
    apply max_le_max _ le_rfl
    apply (le_div_iff₀ hk).mpr
    have he : (1-((N:ℝ)*j/L-1-d/L)/K)*K = K-((N:ℝ)*j/L-1-d/L) := by field_simp
    rw [he]
    linarith
  calc
    _ ≤ (max (K+(j:ℝ)/L-((N:ℝ)*j/L-1)) 0/K) / max ((d:ℝ)/L) ((N:ℝ)*j/L-1) :=
      div_le_div_of_nonneg_right hn (by linarith)
    _ ≤ (max (K+(j:ℝ)/L-((N:ℝ)*j/L-1)) 0/K) / (4/3) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = _ := by ring

lemma exp_low (j L N : ℕ) (hj : j ∈ Icc 4 7) (hL : 0 < L)
    (hy : (N:ℝ)*j/L-1 ≤ 4/3) :
    Real.exp ((Real.log a0-(j:ℝ)*Real.log (tailX j))/((j:ℝ)/L)+(N:ℝ)*Real.log (tailF j)) ≤
      (3/4:ℝ)^((L:ℝ)/j) := by
  have hj0 : (0:ℝ)<j := by exact_mod_cast (show 0<j by have := (mem_Icc.mp hj).1; omega)
  have hL0 : (0:ℝ)<L := by exact_mod_cast hL
  have hθ : 0 < (j:ℝ)/L := div_pos hj0 hL0
  have hf : 0 < Real.log (tailF j) := lt_trans (by norm_num : (0:ℝ)<2/9) (log_F_lower j hj)
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3/4)]
  apply Real.exp_le_exp.mpr
  have hn : (N:ℝ)*((j:ℝ)/L) ≤ 7/3 := by rw [← mul_div_assoc]; linarith
  have hnf := mul_le_mul_of_nonneg_right hn hf.le
  have hb := (tail_log_bases j hj).2
  apply (mul_le_mul_iff_of_pos_right hθ).mp
  have hid : ((Real.log a0-(j:ℝ)*Real.log (tailX j))/((j:ℝ)/L)+(N:ℝ)*Real.log (tailF j))*((j:ℝ)/L) =
      Real.log a0-(j:ℝ)*Real.log (tailX j)+(N:ℝ)*((j:ℝ)/L)*Real.log (tailF j) := by field_simp
  have hid2 : (Real.log (3/4)*((L:ℝ)/j))*((j:ℝ)/L)=Real.log (3/4) := by field_simp
  rw [hid,hid2]
  linarith

lemma tail_low (j L N : ℕ) (hj : j ∈ Icc 4 7) (hL : 0 < L)
    (hy : (N:ℝ)*j/L-1 ≤ 4/3) :
    tailScaleValue j L N ≤ (9*(j:ℝ)/8)*tailD j*(3/4:ℝ)^((L:ℝ)/j) := by
  have hL0 : (0:ℝ)<L := by exact_mod_cast hL
  have hx := (tail_parameters j hj).1
  have hpoint (d : ℕ) (hd : d ∈ Icc 1 j) :
      (carrierCount j L d N:ℝ)*tailEpsilon ((j:ℝ)/L)*countRatio j L d N ≤
      (9*(j:ℝ)/8)*(tailX j)⁻¹^d*(3/4:ℝ)^((L:ℝ)/j) := by
    calc
      _ ≤ ((9*((j:ℝ)/L)/8)*(tailX j)⁻¹^d*
          Real.exp ((Real.log a0-(j:ℝ)*Real.log (tailX j))/((j:ℝ)/L)+(N:ℝ)*Real.log (tailF j)))*(L:ℝ) := by
        apply mul_le_mul (envelope_exponential j L d N hj hL) (ratio_le_L j L d N hL (mem_Icc.mp hd).1)
          (countRatio_nonneg j L d N) (by positivity)
      _ ≤ ((9*((j:ℝ)/L)/8)*(tailX j)⁻¹^d*(3/4:ℝ)^((L:ℝ)/j))*(L:ℝ) := by
        gcongr
        exact exp_low j L N hj hL hy
      _ = _ := by field_simp
  apply (sum_le_sum hpoint).trans_eq
  simp only [tailD,mul_sum,sum_mul]

lemma high_exponential (θ b f y : ℝ) (hθ : 0 < θ) (hf : 0 < f)
    (hb : b+(11/3)*f ≤ 0) :
    max (K+θ-y) 0*Real.exp (b/θ+(y+1)/θ*f) ≤ θ/(Real.exp 1*f)*Real.exp f := by
  by_cases hw : 0 ≤ K+θ-y
  · rw [max_eq_left hw]
    let w := K+θ-y
    have hexp : b/θ+(y+1)/θ*f ≤ f-(f/θ)*w := by
      dsimp [w]
      apply (mul_le_mul_iff_of_pos_right hθ).mp
      have hid : (b/θ+(y+1)/θ*f)*θ = b+(y+1)*f := by field_simp
      have hid2 : (f-f/θ*(K+θ-y))*θ = f*θ-f*(K+θ-y) := by field_simp
      rw [hid,hid2]
      norm_num [K] at *
      nlinarith
    have hh := Real.mul_exp_neg_le_exp_neg_one ((f/θ)*w)
    have hh' : w*Real.exp (-(f/θ*w)) ≤ θ/(Real.exp 1*f) := by
      rw [Real.exp_neg] at hh
      rw [Real.exp_neg]
      apply (le_div_iff₀ (mul_pos (Real.exp_pos _) hf)).mpr
      have hmul := mul_le_mul_of_nonneg_left hh (mul_pos hθ (Real.exp_pos 1)).le
      rw [Real.exp_neg] at hmul
      have he : θ*Real.exp 1*((f/θ*w)*(Real.exp (f/θ*w))⁻¹) =
          (w*(Real.exp (f/θ*w))⁻¹)*(Real.exp 1*f) := by field_simp <;> ring
      rw [he] at hmul
      simpa only [mul_inv_cancel_right₀ (Real.exp_ne_zero 1)] using hmul
    calc
      _ ≤ w*Real.exp (f-(f/θ)*w) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hw
      _ = (w*Real.exp (-(f/θ*w)))*Real.exp f := by rw [sub_eq_add_neg,Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hh' (Real.exp_pos _).le
  · rw [max_eq_right (le_of_not_ge hw),zero_mul]
    positivity

lemma tail_high (j L N : ℕ) (hj : j ∈ Icc 4 7) (hL : 1024 ≤ L)
    (hy : (4/3:ℝ)<(N:ℝ)*j/L-1) :
    tailScaleValue j L N ≤ (2187/4096)*((j:ℝ)/L)^2*tailF j*tailD j := by
  have hLpos : 0<L := by omega
  have hL0 : (0:ℝ)<L := by exact_mod_cast hLpos
  have hj0 : (0:ℝ)<j := by exact_mod_cast (show 0<j by have := (mem_Icc.mp hj).1; omega)
  have hj7 : (j:ℝ)≤7 := by exact_mod_cast (mem_Icc.mp hj).2
  have hLL : (1024:ℝ)≤L := by exact_mod_cast hL
  have hθ : 0 < (j:ℝ)/L := div_pos hj0 hL0
  have hθh : (j:ℝ)/L<4/3 := (div_lt_iff₀ hL0).mpr (by linarith)
  have hf : 0 < Real.log (tailF j) := lt_trans (by norm_num : (0:ℝ)<2/9) (log_F_lower j hj)
  have hF : 0 < tailF j := lt_of_lt_of_le (by norm_num : (0:ℝ)<5/4) (tail_parameters j hj).2.2.1
  have hx := (tail_parameters j hj).1
  have hscalar : (9:ℝ)/(8*K*(4/3)*(Real.exp 1*Real.log (tailF j))) ≤ 2187/4096 := by
    have he := exp_one_bounds.1
    have hl := log_F_lower j hj
    have hp : (16/27:ℝ) ≤ Real.exp 1*Real.log (tailF j) := by nlinarith
    apply (div_le_iff₀ (by unfold K; positivity)).mpr
    norm_num [K]
    nlinarith
  have he := high_exponential ((j:ℝ)/L) (Real.log a0-(j:ℝ)*Real.log (tailX j))
    (Real.log (tailF j)) ((N:ℝ)*j/L-1) hθ hf (tail_log_bases j hj).1.le
  have hNid : (((N:ℝ)*j/L-1)+1)/((j:ℝ)/L) = N := by field_simp <;> ring
  rw [hNid,Real.exp_log hF] at he
  have hpoint (d : ℕ) (hd : d ∈ Icc 1 j) :
      (carrierCount j L d N:ℝ)*tailEpsilon ((j:ℝ)/L)*countRatio j L d N ≤
      (2187/4096)*((j:ℝ)/L)^2*tailF j*(tailX j)⁻¹^d := by
    calc
      _ ≤ ((9*((j:ℝ)/L)/8)*(tailX j)⁻¹^d*
          Real.exp ((Real.log a0-(j:ℝ)*Real.log (tailX j))/((j:ℝ)/L)+(N:ℝ)*Real.log (tailF j)))*
          (max (K+(j:ℝ)/L-((N:ℝ)*j/L-1)) 0/(K*(4/3))) := by
        apply mul_le_mul (envelope_exponential j L d N hj hLpos)
          (ratio_high j L d N hLpos (mem_Icc.mp hd).1 (mem_Icc.mp hd).2 hθh hy)
          (countRatio_nonneg j L d N) (by positivity)
      _ = (9*((j:ℝ)/L)/8)*(tailX j)⁻¹^d/(K*(4/3))*
          (max (K+(j:ℝ)/L-((N:ℝ)*j/L-1)) 0*
          Real.exp ((Real.log a0-(j:ℝ)*Real.log (tailX j))/((j:ℝ)/L)+(N:ℝ)*Real.log (tailF j))) := by ring
      _ ≤ (9*((j:ℝ)/L)/8)*(tailX j)⁻¹^d/(K*(4/3))*
          (((j:ℝ)/L)/(Real.exp 1*Real.log (tailF j))*tailF j) :=
        mul_le_mul_of_nonneg_left he (by unfold K; positivity)
      _ = (9/(8*K*(4/3)*(Real.exp 1*Real.log (tailF j))))*((j:ℝ)/L)^2*tailF j*(tailX j)⁻¹^d := by ring
      _ ≤ _ := by gcongr
  apply (sum_le_sum hpoint).trans_eq
  simp only [tailD,mul_sum]

lemma tail_scale_bound (j L : ℕ) (hj : j ∈ Icc 4 7) (hL : 1024 ≤ L) :
    tailAScale j L ≤ (9*(j:ℝ)/8)*tailD j*(3/4:ℝ)^((L:ℝ)/j)+
      (2187/4096)*((j:ℝ)/L)^2*tailF j*tailD j := by
  have hx := (tail_parameters j hj).1
  have hF : 0 < tailF j := lt_of_lt_of_le (by norm_num : (0:ℝ)<5/4) (tail_parameters j hj).2.2.1
  have hd : 0 ≤ tailD j := sum_nonneg (fun d hd => pow_nonneg (inv_nonneg.mpr hx.le) d)
  apply sup'_le
  intro N hN
  by_cases hy : (N:ℝ)*j/L-1 ≤ 4/3
  · exact (tail_low j L N hj (by omega) hy).trans (le_add_of_nonneg_right (by positivity))
  · exact (tail_high j L N hj hL (lt_of_not_ge hy)).trans (le_add_of_nonneg_left (by positivity))

#print axioms tail_scale_bound
end
end Erdos708H97.Proofs
