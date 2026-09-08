import Erdos708.H97.Proofs.Numeric4_4
import Erdos708.H97.Proofs.Numeric4_8
import Erdos708.H97.Proofs.Numeric5_8
import Erdos708.H97.Proofs.Numeric6_8
import Erdos708.H97.Proofs.Numeric7_8
import Erdos708.H97.Proofs.Numeric4_16
import Erdos708.H97.Proofs.Numeric5_16
import Erdos708.H97.Proofs.Numeric6_16
import Erdos708.H97.Proofs.Numeric7_16
import Erdos708.H97.Proofs.Numeric4_32
import Erdos708.H97.Proofs.Numeric5_32
import Erdos708.H97.Proofs.Numeric6_32
import Erdos708.H97.Proofs.Numeric7_32
import Erdos708.H97.Proofs.Numeric4_64
import Erdos708.H97.Proofs.Numeric5_64
import Erdos708.H97.Proofs.Numeric6_64
import Erdos708.H97.Proofs.Numeric7_64
import Erdos708.H97.Proofs.Numeric4_128
import Erdos708.H97.Proofs.Numeric5_128
import Erdos708.H97.Proofs.Numeric6_128
import Erdos708.H97.Proofs.Numeric7_128
import Erdos708.H97.Proofs.Numeric4_256
import Erdos708.H97.Proofs.Numeric5_256
import Erdos708.H97.Proofs.Numeric6_256
import Erdos708.H97.Proofs.Numeric7_256
import Erdos708.H97.Proofs.Numeric4_512
import Erdos708.H97.Proofs.Numeric5_512
import Erdos708.H97.Proofs.Numeric6_512
import Erdos708.H97.Proofs.Numeric7_512
open Finset BigOperators
namespace Erdos708H97
namespace Proofs
lemma finite_group_2 : finiteGroup 2 < (24680/10^6:ℝ) := by
  have h4 := Numeric4_4.scale_bound
  norm_num [finiteGroup,sum_Icc_succ_top]
  linarith
lemma finite_group_3 : finiteGroup 3 < (128711/10^6:ℝ) := by
  have h4 := Numeric4_8.scale_bound
  have h5 := Numeric5_8.scale_bound
  have h6 := Numeric6_8.scale_bound
  have h7 := Numeric7_8.scale_bound
  norm_num [finiteGroup,sum_Icc_succ_top]
  linarith
lemma finite_group_4 : finiteGroup 4 < (25773/10^6:ℝ) := by
  have h4 := Numeric4_16.scale_bound
  have h5 := Numeric5_16.scale_bound
  have h6 := Numeric6_16.scale_bound
  have h7 := Numeric7_16.scale_bound
  norm_num [finiteGroup,sum_Icc_succ_top]
  linarith
lemma finite_group_5 : finiteGroup 5 < (5665/10^6:ℝ) := by
  have h4 := Numeric4_32.scale_bound
  have h5 := Numeric5_32.scale_bound
  have h6 := Numeric6_32.scale_bound
  have h7 := Numeric7_32.scale_bound
  norm_num [finiteGroup,sum_Icc_succ_top]
  linarith
lemma finite_group_6 : finiteGroup 6 < (1025/10^6:ℝ) := by
  have h4 := Numeric4_64.scale_bound
  have h5 := Numeric5_64.scale_bound
  have h6 := Numeric6_64.scale_bound
  have h7 := Numeric7_64.scale_bound
  norm_num [finiteGroup,sum_Icc_succ_top]
  linarith
lemma finite_group_7 : finiteGroup 7 < (150/10^6:ℝ) := by
  have h4 := Numeric4_128.scale_bound
  have h5 := Numeric5_128.scale_bound
  have h6 := Numeric6_128.scale_bound
  have h7 := Numeric7_128.scale_bound
  norm_num [finiteGroup,sum_Icc_succ_top]
  linarith
lemma finite_group_8 : finiteGroup 8 < (21/10^6:ℝ) := by
  have h4 := Numeric4_256.scale_bound
  have h5 := Numeric5_256.scale_bound
  have h6 := Numeric6_256.scale_bound
  have h7 := Numeric7_256.scale_bound
  norm_num [finiteGroup,sum_Icc_succ_top]
  linarith
lemma finite_group_9 : finiteGroup 9 < (3/10^6:ℝ) := by
  have h4 := Numeric4_512.scale_bound
  have h5 := Numeric5_512.scale_bound
  have h6 := Numeric6_512.scale_bound
  have h7 := Numeric7_512.scale_bound
  norm_num [finiteGroup,sum_Icc_succ_top]
  linarith
lemma finite_total_bound : finiteTotal < (187/1000:ℝ) := by
  have h2 := finite_group_2
  have h3 := finite_group_3
  have h4 := finite_group_4
  have h5 := finite_group_5
  have h6 := finite_group_6
  have h7 := finite_group_7
  have h8 := finite_group_8
  have h9 := finite_group_9
  norm_num [finiteTotal,sum_Icc_succ_top]
  linarith
end Proofs
theorem lemma7 :
    finiteGroup 2 < 24680/10^6 ∧ finiteGroup 3 < 128711/10^6 ∧
    finiteGroup 4 < 25773/10^6 ∧ finiteGroup 5 < 5665/10^6 ∧
    finiteGroup 6 < 1025/10^6 ∧ finiteGroup 7 < 150/10^6 ∧
    finiteGroup 8 < 21/10^6 ∧ finiteGroup 9 < 3/10^6 ∧
    finiteTotal < 187/1000 :=
  ⟨Proofs.finite_group_2,Proofs.finite_group_3,Proofs.finite_group_4,Proofs.finite_group_5,Proofs.finite_group_6,Proofs.finite_group_7,Proofs.finite_group_8,Proofs.finite_group_9,Proofs.finite_total_bound⟩
#print axioms lemma7
end Erdos708H97
