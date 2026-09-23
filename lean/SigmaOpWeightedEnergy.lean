import SigmaOpGradientCompletion

namespace Sigma
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

/-- Integrability is transported through the actual Gamma density, including
the positive support restriction; this is not inferred from an integral value. -/
theorem gamma_integrable_positive_density (f : ℝ → ℝ) (hf : Integrable f gammaProbability) :
    IntegrableOn (fun t => SigmaPresentations.density t*f t) (Ioi 0) volume := by
  change Integrable f (volume.withDensity
    (fun t => ((Real.toNNReal (gammaPDFReal 2 1 t):ℝ≥0):ℝ≥0∞))) at hf
  have hi := (integrable_withDensity_iff_integrable_smul
    ((measurable_gammaPDFReal 2 1).real_toNNReal)).mp hf
  have he : (fun t => Real.toNNReal (gammaPDFReal 2 1 t) • f t) =
      (Ici (0:ℝ)).indicator (fun t => SigmaPresentations.density t*f t) := by
    funext t
    rw [NNReal.smul_def, smul_eq_mul,
      Real.coe_toNNReal _ (gammaPDFReal_nonneg (by norm_num) (by norm_num) t), gamma_pdf_intrinsic]
    by_cases ht : 0 ≤ t <;> simp [ht]
  rw [he, integrable_indicator_iff measurableSet_Ici] at hi
  exact hi.mono_set Ioi_subset_Ici_self

def weightedDerivativeRepresentative (g : LaguerreWeightedHilbert) (t : ℝ) : ℂ :=
  g t/Complex.ofReal (Real.sqrt t)

theorem weighted_derivative_energy_pointwise (g : LaguerreWeightedHilbert)
    (t : ℝ) (ht : 0 < t) :
    steinFlux t*‖weightedDerivativeRepresentative g t‖^2 =
      SigmaPresentations.density t*‖g t‖^2 := by
  simp only [weightedDerivativeRepresentative, norm_div, div_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt ht.le, steinFlux, SigmaPresentations.density]
  field_simp
  ring

theorem weighted_derivative_energy_integrable (g : LaguerreWeightedHilbert) :
    IntegrableOn (fun t => steinFlux t*‖weightedDerivativeRepresentative g t‖^2)
      (Ioi 0) volume := by
  have hi : Integrable (fun t : ℝ => ‖g t‖^2) gammaProbability :=
    (Lp.memℒp g).norm.integrable_sq
  apply (gamma_integrable_positive_density _ hi).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (weighted_derivative_energy_pointwise g t ht).symm

theorem weighted_derivative_energy_integral (g : LaguerreWeightedHilbert) :
    (∫ t : ℝ in Ioi 0, steinFlux t*‖weightedDerivativeRepresentative g t‖^2) = ‖g‖^2 := by
  rw [laguerre_l2_norm_sq_integral, gamma_probability_integral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact weighted_derivative_energy_pointwise g t ht

/-- Once the locally absolutely continuous representative's derivative has
been derived, its literal weighted derivative energy is finite and equals
the norm of the completed gradient. -/
theorem regular_representative_weighted_energy (g : LaguerreWeightedHilbert)
    (H : ℝ → ℂ)
    (hH : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      HasDerivAt H (weightedDerivativeRepresentative g t) t) :
    IntegrableOn (fun t => steinFlux t*‖deriv H t‖^2) (Ioi 0) volume ∧
      (∫ t : ℝ in Ioi 0, steinFlux t*‖deriv H t‖^2) = ‖g‖^2 := by
  have he : (fun t => steinFlux t*‖weightedDerivativeRepresentative g t‖^2) =ᵐ[volume.restrict (Ioi 0)]
      (fun t => steinFlux t*‖deriv H t‖^2) := by
    filter_upwards [hH] with t ht
    rw [ht.deriv]
  exact ⟨(weighted_derivative_energy_integrable g).congr he,
    (integral_congr_ae he.symm).trans (weighted_derivative_energy_integral g)⟩

end
end Sigma
