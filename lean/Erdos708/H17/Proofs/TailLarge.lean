import Erdos708.H17.Proofs.TailEstimates
open Finset BigOperators
namespace Erdos708H17.Proofs
noncomputable section
set_option maxHeartbeats 2000000

lemma tail_scales (j : ℕ) :
    2^(j+7) = 128*2^j ∧ momentOrder (j+7) = 576*2^j ∧ countLimit (j+7) = 408*2^j+1 := by
  have hp : 2^(j+7) = 128*2^j := by rw [pow_add]; norm_num; omega
  refine ⟨hp, ?_, ?_⟩
  · simp only [momentOrder,show j+7 ≠ 0 by omega,if_false,show j+7-1=j+6 by omega,pow_add]
    norm_num
    ring
  · unfold countLimit
    rw [hp]
    omega

lemma q_f_growth (N q : ℕ) : (q:ℝ)*tailF^N ≤ 2*tailF^(N+q) := by
  have hf : (0:ℝ) < tailF := by norm_num [tailF]
  have hi : 1/tailF ≤ (4/5:ℝ) := by norm_num [tailF]
  have hq : (q:ℝ)/tailF^q ≤ 2 := by
    calc
      _ = (q:ℝ)*(1/tailF)^q := by rw [div_pow]; simp [div_eq_mul_inv]
      _ ≤ (q:ℝ)*(4/5:ℝ)^q := by gcongr
      _ ≤ _ := q_decay q
  have hh : (q:ℝ) ≤ 2*tailF^q := (div_le_iff₀ (pow_pos hf q)).mp hq
  have hm := mul_le_mul_of_nonneg_right hh (pow_pos hf N).le
  simpa only [pow_add,mul_assoc,mul_comm,mul_left_comm] using hm

lemma countRatio_large (j N : ℕ) (hN0 : 2*2^(j+7) ≤ N) (hN1 : N ≤ countLimit (j+7)) :
    countRatio (j+7) N ≤ (carrierCount (j+7) N:ℝ)*((countLimit (j+7)-N:ℕ):ℝ)/(K*2^(j+7)) := by
  let ell : ℝ := 2^(j+7)
  have he : 0 < ell := by dsimp [ell]; positivity
  have he1 : 1 ≤ ell := by dsimp [ell]; exact one_le_pow₀ (by norm_num)
  have hn0 : 2*ell ≤ (N:ℝ) := by dsimp [ell]; exact_mod_cast hN0
  have hn1 : (N:ℝ) ≤ countLimit (j+7) := by exact_mod_cast hN1
  have hL : (countLimit (j+7):ℝ) = (K+1)*ell+1 := by
    rw [(tail_scales j).2.2]
    dsimp [ell]
    have hp := (tail_scales j).1
    have hpR : (2:ℝ)^(j+7)=128*(2:ℝ)^j := by exact_mod_cast hp
    rw [hpR]
    push_cast
    norm_num [K]
    ring
  have hk : 0 < K := by norm_num [K]
  have hsub : ((countLimit (j+7)-N:ℕ):ℝ) = countLimit (j+7)-(N:ℝ) := Nat.cast_sub hN1
  have hinner : 0 ≤ ((N:ℝ)-ell-1)/ell := by apply div_nonneg _ he.le; linarith
  have hclip : max (1-max 0 (((N:ℝ)-ell-1)/ell)/K) 0 = ((countLimit (j+7):ℝ)-N)/(K*ell) := by
    rw [max_eq_right hinner]
    have heq : 1-((N:ℝ)-ell-1)/ell/K = ((countLimit (j+7):ℝ)-N)/(K*ell) := by
      rw [hL]
      field_simp <;> ring
    rw [heq,max_eq_left (div_nonneg (sub_nonneg.mpr hn1) (mul_pos hk he).le)]
  have hden : 1 ≤ max (1/ell) (((N:ℝ)-ell)/ell) := by
    apply le_trans _ (le_max_right _ _)
    apply (le_div_iff₀ he).mpr
    linarith
  change (carrierCount (j+7) N:ℝ)*max (1-max 0 (((N:ℝ)-ell-1)/ell)/K) 0 /
    max (1/ell) (((N:ℝ)-ell)/ell) ≤ _
  rw [hclip,hsub]
  calc
    _ ≤ (carrierCount (j+7) N:ℝ)*(((countLimit (j+7):ℝ)-N)/(K*ell)) := by
      apply div_le_self
      · exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (sub_nonneg.mpr hn1) (mul_pos hk he).le)
      · exact hden
    _ = _ := by dsimp [ell]; ring

lemma large_scale_bound (j N : ℕ) (hN0 : 2*2^(j+7) ≤ N) (hN1 : N ≤ countLimit (j+7)) :
    24*epsilon (j+7)*countRatio (j+7) N ≤ 192*gamma*tailF/(K*((2:ℝ)^(j+7))^2) := by
  let q := countLimit (j+7)-N
  have hq : N+q = countLimit (j+7) := by dsimp [q]; omega
  have he : (0:ℝ) < 2^(j+7) := by positivity
  have hk : 0 < K := by norm_num [K]
  have hc := coefficient_envelope (j+7) N
  change (carrierCount (j+7) N:ℝ) ≤ (4:ℝ)^(2^(j+7)+1)*tailF^N at hc
  have hg := q_f_growth N q
  rw [hq] at hg
  have hr : countRatio (j+7) N ≤ 2*(4:ℝ)^(2^(j+7)+1)*tailF^(countLimit (j+7))/(K*2^(j+7)) := by
    apply (countRatio_large j N hN0 hN1).trans
    apply div_le_div_of_nonneg_right _ (mul_pos hk he).le
    calc
      _ ≤ ((4:ℝ)^(2^(j+7)+1)*tailF^N)*(q:ℝ) := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)
      _ = (4:ℝ)^(2^(j+7)+1)*((q:ℝ)*tailF^N) := by ring
      _ ≤ (4:ℝ)^(2^(j+7)+1)*(2*tailF^(countLimit (j+7))) := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by ring
  have hb : (4:ℝ)^(2^(j+7))*tailF^(countLimit (j+7))*tailBase^(momentOrder (j+7)) ≤ tailF := by
    obtain ⟨hp,hm,hL⟩ := tail_scales j
    rw [hp,hm,hL,pow_succ]
    have hb := large_base_power (8*2^j)
    norm_num [show 16*(8*2^j)=128*2^j by ring,
      show 51*(8*2^j)=408*2^j by ring,show 72*(8*2^j)=576*2^j by ring] at hb
    have hh := mul_le_mul_of_nonneg_right hb (show 0 ≤ tailF by norm_num [tailF])
    nlinarith
  calc
    _ ≤ 24*(gamma/(2:ℝ)^(j+7)*tailBase^(momentOrder (j+7))) *
        (2*(4:ℝ)^(2^(j+7)+1)*tailF^(countLimit (j+7))/(K*2^(j+7))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (epsilon_envelope (j+7) (by omega)) (by norm_num)
      · exact hr
      · exact countRatio_nonneg (j+7) N
      · unfold gamma tailBase; positivity
    _ = (192*gamma/(K*((2:ℝ)^(j+7))^2))*
        ((4:ℝ)^(2^(j+7))*tailF^(countLimit (j+7))*tailBase^(momentOrder (j+7))) := by
      rw [pow_succ]
      field_simp <;> ring
    _ ≤ (192*gamma/(K*((2:ℝ)^(j+7))^2))*tailF :=
      mul_le_mul_of_nonneg_left hb (by unfold gamma K; positivity)
    _ = _ := by ring

#print axioms tail_scales
#print axioms q_f_growth
#print axioms countRatio_large
#print axioms large_scale_bound
end
end Erdos708H17.Proofs
