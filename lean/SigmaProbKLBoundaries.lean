import SigmaProbExpEntropy
import SigmaProbGaussianEntropy
import Mathlib.Data.Complex.ExponentialBounds

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal NNReal

theorem poisson_relative_entropy_slice (t : ℝ≥0) (ht : 0 < t) :
    finiteRelativeEntropy (poissonMeasure 1) (poissonMeasure t) = SigmaBase.potential (t:ℝ) := by
  simpa using poisson_relative_entropy 1 t (by norm_num) ht

theorem exponential_relative_entropy_slice (t : ℝ) (ht : 0 < t) :
    finiteRelativeEntropy (rateExpProbability 1) (rateExpProbability t) = SigmaBase.potential t := by
  simpa using exponential_relative_entropy 1 t (by norm_num) ht

theorem gaussian_relative_entropy_slice (t : ℝ≥0) (ht : 0 < t) :
    2*finiteRelativeEntropy (gaussianReal 0 t) (gaussianReal 0 1) = SigmaBase.potential (t:ℝ) := by
  simpa using gaussian_relative_entropy t 1 ht (by norm_num)

theorem poisson_relative_entropy_bregman (a b : ℝ≥0) (ha : 0 < a) (hb : 0 < b) :
    finiteRelativeEntropy (poissonMeasure a) (poissonMeasure b) =
      SigmaBase.bregman SigmaPresentations.poissonPotential Real.log (a:ℝ) (b:ℝ) := by
  rw [poisson_relative_entropy a b ha hb,
    SigmaPresentations.poisson_mean_bregman (show (0:ℝ)<a from ha) (show (0:ℝ)<b from hb)]
  exact (SigmaPresentations.poisson_KL_orientation (show (0:ℝ)<a from ha) (show (0:ℝ)<b from hb)).symm

theorem reversed_poisson_entropy_slice (t : ℝ≥0) (ht : 0 < t) :
    finiteRelativeEntropy (poissonMeasure t) (poissonMeasure 1) =
      (t:ℝ)*Real.log (t:ℝ)-(t:ℝ)+1 := by
  rw [poisson_relative_entropy t 1 ht (by norm_num)]
  have h := SigmaPresentations.poisson_KL_orientation (show (0:ℝ)<t from ht) (show (0:ℝ)<1 by norm_num)
  simpa using h.symm

theorem reversed_exponential_entropy_slice (t : ℝ) (ht : 0 < t) :
    finiteRelativeEntropy (rateExpProbability t) (rateExpProbability 1) =
      SigmaBase.potential (1/t) := by
  exact exponential_relative_entropy t 1 ht (by norm_num)

theorem reversed_gaussian_entropy_slice (t : ℝ≥0) (ht : 0 < t) :
    2*finiteRelativeEntropy (gaussianReal 0 1) (gaussianReal 0 t) =
      SigmaBase.potential (1/(t:ℝ)) := by
  simpa using gaussian_relative_entropy 1 t (by norm_num) ht

theorem poisson_entropy_reversal_distinct :
    finiteRelativeEntropy (poissonMeasure 1) (poissonMeasure 2) ≠
      finiteRelativeEntropy (poissonMeasure 2) (poissonMeasure 1) := by
  rw [poisson_relative_entropy_slice 2 (by norm_num),reversed_poisson_entropy_slice 2 (by norm_num)]
  norm_num only [NNReal.coe_ofNat]
  unfold SigmaBase.potential
  intro he
  have hl := Real.log_two_gt_d9
  linarith

theorem reciprocal_potential_distinct_at_two :
    SigmaBase.potential (2:ℝ) ≠ SigmaBase.potential (1/2:ℝ) := by
  unfold SigmaBase.potential
  rw [one_div,Real.log_inv]
  intro he
  have hl := Real.log_two_lt_d9
  linarith

theorem exponential_entropy_reversal_distinct :
    finiteRelativeEntropy (rateExpProbability 1) (rateExpProbability 2) ≠
      finiteRelativeEntropy (rateExpProbability 2) (rateExpProbability 1) := by
  rw [exponential_relative_entropy_slice 2 (by norm_num),
    reversed_exponential_entropy_slice 2 (by norm_num)]
  exact reciprocal_potential_distinct_at_two

theorem gaussian_entropy_reversal_distinct :
    finiteRelativeEntropy (gaussianReal 0 2) (gaussianReal 0 1) ≠
      finiteRelativeEntropy (gaussianReal 0 1) (gaussianReal 0 2) := by
  intro he
  have hh := congrArg (fun x:ℝ => 2*x) he
  dsimp only at hh
  rw [gaussian_relative_entropy_slice 2 (by norm_num),
    reversed_gaussian_entropy_slice 2 (by norm_num)] at hh
  exact reciprocal_potential_distinct_at_two hh


theorem poisson_potential_derivative (t : ℝ) (ht : 0 < t) :
    HasDerivAt SigmaPresentations.poissonPotential (Real.log t) t := by
  have hh := (((hasDerivAt_id t).mul (Real.hasDerivAt_log ht.ne')).sub
    (hasDerivAt_id t)).add_const 1
  convert hh using 1
  simp only [id_eq,one_mul,mul_inv_cancel₀ ht.ne',add_sub_cancel_right]

theorem poisson_relative_entropy_actual_bregman (a b : ℝ≥0) (ha : 0 < a) (hb : 0 < b) :
    finiteRelativeEntropy (poissonMeasure a) (poissonMeasure b) =
      SigmaPresentations.poissonPotential (a:ℝ)-SigmaPresentations.poissonPotential (b:ℝ)-
        deriv SigmaPresentations.poissonPotential (b:ℝ)*((a:ℝ)-(b:ℝ)) := by
  rw [poisson_relative_entropy_bregman a b ha hb,
    (poisson_potential_derivative (b:ℝ) hb).deriv]
  rfl

theorem centered_poisson_potential_in_log_coordinate (u : ℝ) :
    SigmaPresentations.centeredCGF u = SigmaBase.potential (Real.exp u) := by
  simp [SigmaPresentations.centeredCGF,SigmaBase.potential]

theorem centered_poisson_reconstructs_potential (t : ℝ) (ht : 0 < t) :
    SigmaBase.potential t = SigmaPresentations.centeredCGF (Real.log t) := by
  rw [centered_poisson_potential_in_log_coordinate,Real.exp_log ht]

end
end Sigma
