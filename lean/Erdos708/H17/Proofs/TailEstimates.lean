import Erdos708.H17.Proofs.TailBasics
import Erdos708.H17.Proofs.TailCoefficient
open Finset BigOperators
namespace Erdos708H17.Proofs
noncomputable section
set_option maxHeartbeats 2000000

def tailBase : ℝ := 29725/49152

lemma moment_real (h : ℕ) (hh : 1 ≤ h) : (momentOrder h : ℝ) = (9/2:ℝ)*(2:ℝ)^h := by
  have he : h-1+1=h := by omega
  have he' : (2:ℝ)^h = 2^(h-1)*2 := by rw [← he,pow_succ]; congr 2 <;> omega
  rw [momentOrder,if_neg (by omega)]
  push_cast
  rw [he']
  ring

lemma epsilon_envelope (h : ℕ) (hh : 1 ≤ h) :
    epsilon h ≤ gamma/(2:ℝ)^h * tailBase^(momentOrder h) := by
  have he : (0:ℝ) < 2^h := by positivity
  have hr : 1 ≤ momentOrder h := moment_order_pos h
  have hrR := moment_real h hh
  have hfac := factorial_lower (momentOrder h) hr
  have hb : ((momentOrder h:ℝ)/(87/32)) = 2^h*Hstar/tailBase := by rw [hrR]; norm_num [Hstar,tailBase]; ring
  rw [hb] at hfac
  have hp : 0 < (2^h*Hstar/tailBase)^momentOrder h := by unfold Hstar tailBase; positivity
  unfold epsilon
  rw [if_neg (by omega)]
  calc
    _ ≤ gamma*((2:ℝ)^h)^(momentOrder h-1)*Hstar^(momentOrder h) /
        ((2^h*Hstar/tailBase)^momentOrder h) := by
      apply div_le_div_of_nonneg_left (by unfold gamma Hstar; positivity) hp hfac
    _ = _ := by
      have hpow : ((2:ℝ)^h)^(momentOrder h-1)*2^h = ((2:ℝ)^h)^(momentOrder h) := by
        rw [← pow_succ]; congr 1; omega
      rw [div_pow,mul_pow]
      have hs : Hstar ≠ 0 := by norm_num [Hstar]
      have hb0 : tailBase ≠ 0 := by norm_num [tailBase]
      field_simp
      linear_combination gamma*hpow

lemma q_decay (q : ℕ) : (q:ℝ)*(4/5:ℝ)^q ≤ 2 := by
  have hlarge : ∀ q : ℕ, 4 ≤ q → (q:ℝ)*(4/5:ℝ)^q ≤ (1024/625:ℝ) := by
    intro q hq
    induction q, hq using Nat.le_induction with
    | base => norm_num
    | succ q hq ih =>
      rw [pow_succ]
      push_cast
      have hp : 0 ≤ (4/5:ℝ)^q := by positivity
      have hqR : (4:ℝ) ≤ q := by exact_mod_cast hq
      nlinarith
  by_cases hq : q < 4
  · interval_cases q <;> norm_num
  · linarith [hlarge q (by omega)]

lemma small_base_power (t : ℕ) :
    (4:ℝ)^(2*t)*tailF^(4*t)*tailBase^(9*t) ≤ (3/4:ℝ)^(2*t) := by
  have hb := tail_base_bounds.2.le
  change (16:ℝ)*tailF^4*tailBase^9 ≤ 9/16 at hb
  have hp := pow_le_pow_left₀ (by unfold tailF tailBase; positivity) hb t
  simpa only [mul_pow,pow_mul,show (4:ℝ)^2=16 by norm_num,show (3/4:ℝ)^2=9/16 by norm_num] using hp

lemma large_base_power (t : ℕ) :
    (4:ℝ)^(16*t)*tailF^(51*t)*tailBase^(72*t) ≤ 1 := by
  have hb := tail_base_bounds.1.le
  change (4:ℝ)^16*tailF^51*tailBase^72 ≤ 1 at hb
  have hp := pow_le_pow_left₀ (by unfold tailF tailBase; positivity) hb t
  simpa only [mul_pow,pow_mul,one_pow] using hp

lemma countRatio_simple (h N : ℕ) : countRatio h N ≤ (carrierCount h N:ℝ)*(2:ℝ)^h := by
  have he : (0:ℝ) < 2^h := by positivity
  have hd : 0 < max (1/(2:ℝ)^h) (((N:ℝ)-2^h)/2^h) := (one_div_pos.mpr he).trans_le (le_max_left _ _)
  have hc : max (1-max 0 (((N:ℝ)-2^h-1)/2^h)/K) 0 ≤ 1 := by
    apply max_le _ (by norm_num)
    have : 0 ≤ max 0 (((N:ℝ)-2^h-1)/2^h)/K := by unfold K; positivity
    linarith
  calc
    _ ≤ (carrierCount h N:ℝ)/max (1/(2:ℝ)^h) (((N:ℝ)-2^h)/2^h) := by
      unfold countRatio
      apply div_le_div_of_nonneg_right _ hd.le
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) hc
    _ ≤ (carrierCount h N:ℝ)/(1/(2:ℝ)^h) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (one_div_pos.mpr he) (le_max_left _ _)
    _ = _ := by field_simp

lemma small_scale_bound (h : ℕ) (hh : 1 ≤ h) (N : ℕ) (hN : N < 2*2^h) :
    24*epsilon h*countRatio h N ≤ 96*gamma*(3/4:ℝ)^(2^h) := by
  have he : (0:ℝ) < 2^h := by positivity
  have hf : (1:ℝ) ≤ tailF := by norm_num [tailF]
  have hcount := coefficient_envelope h N
  change (carrierCount h N:ℝ) ≤ (4:ℝ)^(2^h+1)*tailF^N at hcount
  have hr : countRatio h N ≤ (4:ℝ)^(2^h+1)*tailF^(2*2^h)*2^h := by
    apply (countRatio_simple h N).trans
    gcongr
    exact hcount.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hf hN.le) (by positivity))
  have hb : (4:ℝ)^(2^h)*tailF^(2*2^h)*tailBase^(momentOrder h) ≤ (3/4:ℝ)^(2^h) := by
    have heq : 2^h = 2*2^(h-1) := by
      conv_lhs => rw [show h = (h-1)+1 by omega,pow_succ]
      omega
    have hrq : momentOrder h = 9*2^(h-1) := by simp [momentOrder,show h ≠ 0 by omega]
    rw [heq,hrq,show 2*(2*2^(h-1)) = 4*2^(h-1) by ring]
    exact small_base_power (2^(h-1))
  calc
    _ ≤ 24*(gamma/(2:ℝ)^h*tailBase^(momentOrder h))*((4:ℝ)^(2^h+1)*tailF^(2*2^h)*2^h) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (epsilon_envelope h hh) (by norm_num)
      · exact hr
      · exact countRatio_nonneg h N
      · unfold gamma tailBase; positivity
    _ = 96*gamma*((4:ℝ)^(2^h)*tailF^(2*2^h)*tailBase^(momentOrder h)) := by
      rw [pow_succ]
      field_simp <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by unfold gamma; positivity)

#print axioms countRatio_simple
#print axioms small_scale_bound
#print axioms small_base_power
#print axioms large_base_power
#print axioms epsilon_envelope
#print axioms q_decay
end
end Erdos708H17.Proofs
