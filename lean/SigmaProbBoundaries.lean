import SigmaProbGammaTransforms

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

theorem gamma_with_zero_atom_positive_moments (n : ℕ) (hn : 0 < n) :
    (∫ t : ℝ, t^n ∂(gammaProbability + Measure.dirac 0)) =
      ((n+1).factorial : ℝ) := by
  have hd : Integrable (fun t : ℝ => t^n) (Measure.dirac 0) :=
    ⟨(continuous_id.pow n).aestronglyMeasurable, by
      rw [HasFiniteIntegral, lintegral_dirac]
      simp [zero_pow (Nat.ne_of_gt hn)]⟩
  rw [integral_add_measure (gamma_probability_monomial_integrable n)
    hd, gamma_probability_moments, integral_dirac]
  simp [zero_pow (Nat.ne_of_gt hn)]

theorem gamma_with_zero_atom_mass :
    (gammaProbability + Measure.dirac (0 : ℝ)) univ = 2 := by norm_num

theorem gamma_with_zero_atom_distinct :
    gammaProbability + Measure.dirac (0 : ℝ) ≠ gammaProbability := by
  intro he
  have hm := congrArg (fun μ : Measure ℝ => μ univ) he
  dsimp only at hm
  rw [gamma_with_zero_atom_mass, gamma_probability_normalized] at hm
  norm_num at hm

theorem residual_endpoint_one : gammaResidualProbability 1 = Measure.dirac (0 : ℝ) := by
  have hm : atomExpMixture 1 = Measure.dirac (0 : ℝ) := by simp [atomExpMixture]
  rw [gammaResidualProbability, hm, independentAffineSum, Measure.dirac_prod_dirac,
    Measure.map_dirac (by fun_prop)]
  norm_num

theorem residual_endpoint_one_every_law (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    independentAffineSum μ (gammaResidualProbability 1) 1 = μ := by
  rw [residual_endpoint_one, independentAffineSum, Measure.prod_dirac,
    Measure.map_map (by fun_prop) (by fun_prop)]
  simpa only [Function.comp_def, mul_one, one_mul, add_zero] using (Measure.map_id (μ := μ))

theorem atom_exp_weighted_coordinate (c : ℝ) :
    (atomExpMixture c).withDensity sizeBiasWeight =
      ENNReal.ofReal (1-c) • gammaProbability := by
  classical
  rw [atomExpMixture, withDensity_add_measure, withDensity_smul_measure,
    withDensity_smul_measure, unit_exp_weighted_by_coordinate]
  have hd : (Measure.dirac (0 : ℝ)).withDensity sizeBiasWeight = 0 := by
    ext s hs
    rw [withDensity_apply _ hs]
    rw [setLIntegral_dirac]
    simp [sizeBiasWeight]
  rw [hd]
  simp

theorem atom_exp_coordinate_mean (c : ℝ) :
    (∫⁻ t, sizeBiasWeight t ∂atomExpMixture c) = ENNReal.ofReal (1-c) := by
  have he := congrArg (fun μ : Measure ℝ => μ univ) (atom_exp_weighted_coordinate c)
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    Measure.smul_apply, gamma_probability_normalized, smul_eq_mul, mul_one] using he

theorem zero_atom_size_bias_counterexample (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    IsProbabilityMeasure (atomExpMixture c) ∧
    normalizedWeight (atomExpMixture c) sizeBiasWeight = gammaProbability ∧
    atomExpMixture c ≠ unitExpProbability := by
  refine ⟨atom_exp_mixture_probability c hc0.le hc1.le, ?_, ?_⟩
  · rw [normalizedWeight, atom_exp_coordinate_mean, atom_exp_weighted_coordinate, smul_smul,
      ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hc1)))
        ENNReal.ofReal_ne_top, one_smul]
  · intro he
    have hz := congrArg (fun μ : Measure ℝ => μ {0}) he
    dsimp only at hz
    rw [atom_exp_mixture_zero_atom, unit_exp_no_atom] at hz
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr hc0)) hz

end
end Sigma
