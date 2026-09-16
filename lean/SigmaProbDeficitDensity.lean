import SigmaProbDeficitDerivative
import Mathlib.Probability.CDF

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem gamma_deficit_cdf_native : gammaDeficitCDF = ProbabilityTheory.cdf gammaDeficitProbability := by
  funext v
  exact (ProbabilityTheory.cdf_eq_toReal gammaDeficitProbability v).symm

theorem gamma_deficit_cdf_right_continuous (v : ℝ) :
    ContinuousWithinAt gammaDeficitCDF (Ici v) v := by
  rw [gamma_deficit_cdf_native]
  exact (ProbabilityTheory.cdf gammaDeficitProbability).right_continuous v

theorem gamma_deficit_cdf_tendsto_one : Tendsto gammaDeficitCDF atTop (𝓝 1) := by
  rw [gamma_deficit_cdf_native]
  exact ProbabilityTheory.tendsto_cdf_atTop gammaDeficitProbability

theorem gamma_deficit_cdf_real_zero : gammaDeficitCDF 0 = 0 := by
  simp [gammaDeficitCDF,gamma_deficit_cdf_zero_at_zero]

theorem gamma_deficit_density_nonpositive (v : ℝ) (hv : v ≤ 0) : gammaDeficitDensity v = 0 := by
  rcases hv.lt_or_eq with hv | rfl
  · simp [gammaDeficitDensity,deficitLowerRoot,deficitUpperRoot,canonicalDeficitRoots,
      not_le_of_gt hv]
  · simp [gammaDeficitDensity,deficitLowerRoot,deficitUpperRoot,canonical_deficit_roots_zero]

theorem gamma_deficit_density_positive (v : ℝ) (hv : 0 < v) : 0 < gammaDeficitDensity v := by
  have hs := deficit_roots_strict v hv
  unfold gammaDeficitDensity
  exact mul_pos (Real.exp_pos _) (add_pos
    (div_pos hs.1 (by linarith [hs.2.1]))
    (div_pos (by linarith [hs.2.2]) (by linarith [hs.2.2])))

theorem gamma_deficit_density_nonnegative (v : ℝ) : 0 ≤ gammaDeficitDensity v := by
  rcases lt_or_ge 0 v with hv | hv
  · exact (gamma_deficit_density_positive v hv).le
  · rw [gamma_deficit_density_nonpositive v hv]

theorem gamma_deficit_density_integrable_on_positive :
    IntegrableOn gammaDeficitDensity (Ioi (0 : ℝ)) :=
  integrableOn_Ioi_deriv_of_nonneg (gamma_deficit_cdf_right_continuous 0)
    (fun v hv => gamma_deficit_cdf_derivative v hv)
    (fun v _ => gamma_deficit_density_nonnegative v) gamma_deficit_cdf_tendsto_one

theorem gamma_deficit_density_indicator :
    (Ioi (0 : ℝ)).indicator gammaDeficitDensity = gammaDeficitDensity := by
  funext v
  by_cases hv : 0 < v
  · simp [hv]
  · simp [hv,gamma_deficit_density_nonpositive v (le_of_not_gt hv)]

theorem gamma_deficit_density_integrable : Integrable gammaDeficitDensity := by
  rw [← gamma_deficit_density_indicator]
  exact gamma_deficit_density_integrable_on_positive.integrable_indicator measurableSet_Ioi

theorem gamma_deficit_density_integral_one : (∫ v : ℝ, gammaDeficitDensity v) = 1 := by
  have he := integral_Ioi_of_hasDerivAt_of_nonneg (gamma_deficit_cdf_right_continuous 0)
    (fun v hv => gamma_deficit_cdf_derivative v hv)
    (fun v _ => gamma_deficit_density_nonnegative v) gamma_deficit_cdf_tendsto_one
  rw [gamma_deficit_cdf_real_zero,sub_zero] at he
  rw [← integral_indicator measurableSet_Ioi,gamma_deficit_density_indicator] at he
  exact he

theorem gamma_deficit_density_tail (a : ℝ) (ha : 0 ≤ a) :
    (∫ v : ℝ in Ioi a, gammaDeficitDensity v) = 1-gammaDeficitCDF a := by
  exact integral_Ioi_of_hasDerivAt_of_nonneg (gamma_deficit_cdf_right_continuous a)
    (fun v hv => gamma_deficit_cdf_derivative v (ha.trans_lt hv))
    (fun v _ => gamma_deficit_density_nonnegative v) gamma_deficit_cdf_tendsto_one

theorem gamma_deficit_density_Iic (a : ℝ) :
    (∫ v : ℝ in Iic a, gammaDeficitDensity v) = gammaDeficitCDF a := by
  rcases le_or_gt 0 a with ha | ha
  · have he := integral_add_compl (s := Iic a) measurableSet_Iic gamma_deficit_density_integrable
    rw [compl_Iic,gamma_deficit_density_tail a ha,gamma_deficit_density_integral_one] at he
    linarith
  · have he : (∫ v : ℝ in Iic a, gammaDeficitDensity v) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Iic] with v hv
      exact gamma_deficit_density_nonpositive v (hv.trans ha.le)
    rw [he,gammaDeficitCDF,gamma_deficit_cdf_negative a ha]
    rfl

/-- The displayed deficit density is an actual Radon--Nikodym density of the
canonical deficit probability, including its singular endpoint. -/
theorem gamma_deficit_probability_density :
    gammaDeficitProbability = volume.withDensity (fun v => ENNReal.ofReal (gammaDeficitDensity v)) := by
  apply Measure.ext_of_Iic
  intro v
  rw [← ProbabilityTheory.ofReal_cdf gammaDeficitProbability v,
    ← gamma_deficit_cdf_native,
    withDensity_apply _ measurableSet_Iic,
    ← ofReal_integral_eq_lintegral_ofReal gamma_deficit_density_integrable.integrableOn
      (Eventually.of_forall gamma_deficit_density_nonnegative),gamma_deficit_density_Iic]

end
end Sigma
