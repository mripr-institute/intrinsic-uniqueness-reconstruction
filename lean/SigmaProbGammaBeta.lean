import SigmaProbGammaBetaDensity

namespace Sigma
noncomputable section
open MeasureTheory Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal

/-- Normalization follows from the proved Gamma–Beta joint change of
variables and the normalization of both Gamma laws. -/
theorem gamma_beta_measure_probability (a : ℝ) (ha : 0 < a) :
    IsProbabilityMeasure (gammaBetaMeasure a) := by
  letI : IsProbabilityMeasure (gammaMeasure a 1) := isProbabilityMeasureGamma ha (by norm_num)
  letI : IsProbabilityMeasure (gammaMeasure (2*a) 1) :=
    isProbabilityMeasureGamma (by positivity) (by norm_num)
  letI : SFinite (gammaBetaMeasure a) := by unfold gammaBetaMeasure; infer_instance
  have h := congrArg (fun μ : Measure (ℝ × ℝ) => μ univ) (gamma_beta_split_measure a ha)
  dsimp only at h
  rw [Measure.map_apply gamma_beta_split_measurable MeasurableSet.univ, preimage_univ] at h
  rw [← Set.univ_prod_univ, Measure.prod_prod, Measure.prod_prod,
    measure_univ (μ := gammaMeasure (2*a) 1), measure_univ (μ := gammaMeasure a 1),
    one_mul, one_mul] at h
  exact ⟨h⟩

theorem gamma_beta_measure_support (a : ℝ) :
    ∀ᵐ b ∂gammaBetaMeasure a, b ∈ Ioo (0 : ℝ) 1 :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)

/-- The symmetric Beta(r,r) splitting probability. At duration zero the total
is identically zero, so a deterministic fraction is sufficient. -/
def gammaProcessBetaProbability (r : ℝ≥0) : Measure ℝ :=
  if r = 0 then Measure.dirac (1/2) else gammaBetaMeasure (r : ℝ)

instance gammaProcessBetaProbability_probability (r : ℝ≥0) :
    IsProbabilityMeasure (gammaProcessBetaProbability r) := by
  by_cases hr : r = 0
  · simp [gammaProcessBetaProbability, hr]
    infer_instance
  · rw [gammaProcessBetaProbability, if_neg hr]
    exact gamma_beta_measure_probability _ (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr))

theorem gamma_process_beta_support (r : ℝ≥0) :
    ∀ᵐ b ∂gammaProcessBetaProbability r, 0 ≤ b ∧ b ≤ 1 := by
  by_cases hr : r = 0
  · simp [gammaProcessBetaProbability, hr]
    norm_num
  · rw [gammaProcessBetaProbability, if_neg hr]
    exact (gamma_beta_measure_support _).mono fun _ hb => ⟨hb.1.le,hb.2.le⟩

/-- Splitting a Gamma(2r,1) total by an independent Beta(r,r) fraction produces
two independent Gamma(r,1) increments. This is equality of native measures. -/
theorem gamma_process_beta_split_law (r : ℝ≥0) :
    ((gammaCompletion r).prod (gammaProcessBetaProbability r)).map
      (fun p : ℝ × ℝ => (p.1*p.2,p.1*(1-p.2))) =
      (gammaCompletion (r/2)).prod (gammaCompletion (r/2)) := by
  change ((gammaCompletion r).prod (gammaProcessBetaProbability r)).map gammaBetaSplit = _
  by_cases hr : r = 0
  · subst r
    simp [gamma_completion_zero, gammaProcessBetaProbability, Measure.dirac_prod_dirac,
      Measure.map_dirac gamma_beta_split_measurable, gammaBetaSplit]
  · have hrp : 0 < r := pos_iff_ne_zero.mpr hr
    have hhalf : 0 < r/2 := by positivity
    rw [gamma_completion_positive r hrp, gamma_completion_positive (r/2) hhalf,
      gammaProcessBetaProbability, if_neg hr]
    have he : 2*((r/2 : ℝ≥0) : ℝ) = (r : ℝ) := by push_cast; ring
    rw [he]
    exact gamma_beta_split_measure _ (NNReal.coe_pos.mpr hrp)

end
end Sigma
