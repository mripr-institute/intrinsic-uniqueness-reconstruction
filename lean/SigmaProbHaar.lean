import SigmaProbCDF
import SigmaProbWeights
import SigmaProbDeficit
import Mathlib.MeasureTheory.Function.Jacobian

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal

/-- Multiplicative Haar measure on the positive ray, extended by zero to ℝ. -/
def positiveHaar : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t : ℝ => ENNReal.ofReal t⁻¹)

theorem positive_haar_log : Measure.map Real.log positiveHaar = volume := by
  have him : Real.log '' Ioi 0 = univ := by
    ext x
    simp only [mem_image, mem_Ioi, mem_univ, iff_true]
    exact ⟨Real.exp x, Real.exp_pos x, Real.log_exp x⟩
  have hd (x : ℝ) (hx : x ∈ Ioi (0:ℝ)) :=
    (Real.hasDerivAt_log (ne_of_gt hx)).hasDerivWithinAt (s := Ioi 0)
  have he := map_withDensity_abs_det_fderiv_eq_addHaar volume measurableSet_Ioi
    (fun x hx => (hd x hx).hasFDerivWithinAt) Real.log_injOn_pos Real.measurable_log
  rw [him, Measure.restrict_univ] at he
  convert he using 2
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp only [det_one_smulRight, abs_of_pos (inv_pos.mpr hx)]

theorem positive_haar_positive : ∀ᵐ t ∂positiveHaar, 0 < t :=
  (withDensity_absolutelyContinuous _ _) (ae_restrict_mem measurableSet_Ioi)

theorem positive_haar_exp : Measure.map Real.exp volume = positiveHaar := by
  rw [← positive_haar_log, Measure.map_map Real.measurable_exp Real.measurable_log]
  calc
    Measure.map (Real.exp ∘ Real.log) positiveHaar = Measure.map id positiveHaar := by
      apply Measure.map_congr
      filter_upwards [positive_haar_positive] with t ht
      exact Real.exp_log ht
    _ = positiveHaar := Measure.map_id

theorem positive_haar_scale (a : ℝ) (ha : 0 < a) :
    Measure.map (fun t : ℝ => a*t) positiveHaar = positiveHaar := by
  rw [← positive_haar_exp, Measure.map_map (by fun_prop) Real.measurable_exp]
  have hf : (fun t : ℝ => a*t) ∘ Real.exp = Real.exp ∘ (fun x => Real.log a+x) := by
    funext x
    simp [Function.comp_def, Real.exp_add, Real.exp_log ha]
  rw [hf, ← Measure.map_map Real.measurable_exp (by fun_prop), map_add_left_eq_self]

theorem positive_haar_infinite : positiveHaar univ = ∞ := by
  rw [← positive_haar_exp, Measure.map_apply Real.measurable_exp MeasurableSet.univ]
  simp

theorem positive_haar_upper_infinite (a : ℝ) (ha : 0 < a) :
    positiveHaar (Ioi a) = ∞ := by
  rw [← positive_haar_exp, Measure.map_apply Real.measurable_exp measurableSet_Ioi]
  have he : Real.exp ⁻¹' Ioi a = Ioi (Real.log a) := by
    ext x
    exact (Real.log_lt_iff_lt_exp ha).symm
  rw [he, Real.volume_Ioi]

theorem positive_haar_lower_infinite (a : ℝ) (ha : 0 < a) :
    positiveHaar (Ioo 0 a) = ∞ := by
  rw [← positive_haar_exp, Measure.map_apply Real.measurable_exp measurableSet_Ioo]
  have he : Real.exp ⁻¹' Ioo 0 a = Iio (Real.log a) := by
    ext x
    simp only [mem_preimage, mem_Ioo, Real.exp_pos, true_and, mem_Iio]
    exact (Real.lt_log_iff_exp_lt ha).symm
  rw [he, Real.volume_Iio]

/-- The marked logarithmic coordinate of the paper. -/
def gumbelCoordinate (x : ℝ) : ℝ := Real.exp (-x)

theorem gumbel_coordinate_haar : Measure.map gumbelCoordinate volume = positiveHaar := by
  change Measure.map (Real.exp ∘ Neg.neg) volume = _
  rw [← Measure.map_map Real.measurable_exp measurable_neg, Measure.map_neg_eq_self, positive_haar_exp]

theorem positive_haar_weighted_density :
    positiveHaar.withDensity (fun t => ENNReal.ofReal (SigmaPresentations.density t)) =
      (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (Real.exp (-t))) := by
  rw [positiveHaar, ← withDensity_mul _ measurable_inv.ennreal_ofReal
    (by unfold SigmaPresentations.density; fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ENNReal.ofReal t⁻¹ * ENNReal.ofReal (SigmaPresentations.density t) = _
  rw [← ENNReal.ofReal_mul (inv_pos.mpr ht).le]
  congr 1
  unfold SigmaPresentations.density
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt ht), one_mul]

theorem unit_exp_density_on_positive :
    unitExpProbability =
      (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (Real.exp (-t))) := by
  calc
    unitExpProbability = unitExpProbability.restrict (Ioi 0) :=
      (Measure.restrict_eq_self_of_ae_mem unit_exp_positive).symm
    _ = (volume.restrict (Ioi 0)).withDensity (gammaPDF 1 1) :=
      restrict_withDensity measurableSet_Ioi _
    _ = _ := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [gammaPDF, ← ENNReal.ofReal_eq_coe_nnreal, unit_exp_pdf, if_pos (le_of_lt ht)]

theorem gumbel_coordinate_pushforward :
    Measure.map gumbelCoordinate gumbelProbability = unitExpProbability := by
  rw [gumbel_probability_density]
  have hg : (fun t => ENNReal.ofReal (gumbelDensity t)) =
      (fun t => ENNReal.ofReal (SigmaPresentations.density t)) ∘ gumbelCoordinate := by
    funext x
    exact congrArg ENNReal.ofReal (gumbel_density_intrinsic x)
  rw [hg, ← map_with_linked_density _ _ (by unfold gumbelCoordinate; fun_prop)
    _ (by unfold SigmaPresentations.density; fun_prop), gumbel_coordinate_haar,
    positive_haar_weighted_density, ← unit_exp_density_on_positive]

theorem positive_haar_weighted_probability :
    positiveHaar.withDensity (fun t => ENNReal.ofReal (SigmaPresentations.density t)) =
      unitExpProbability := by
  rw [positive_haar_weighted_density, ← unit_exp_density_on_positive]

theorem positive_haar_weighted_normalized :
    (∫⁻ t, ENNReal.ofReal (SigmaPresentations.density t) ∂positiveHaar) = 1 := by
  have he := congrArg (fun μ : Measure ℝ => μ univ) positive_haar_weighted_probability
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, measure_univ] using he

theorem positive_haar_density_integral :
    (∫ t : ℝ in Ioi 0, SigmaPresentations.density t / t) = 1 := by
  have he := unit_exp_integral (fun _ => 1)
  simp only [integral_const, measure_univ, smul_eq_mul, mul_one] at he
  norm_num at he
  rw [he]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  unfold SigmaPresentations.density
  field_simp [ne_of_gt ht]

/-- Undoing the Haar weight recovers the original Gamma probability. -/
theorem positive_haar_recovers_gamma :
    (positiveHaar.withDensity (fun t => ENNReal.ofReal (SigmaPresentations.density t))).withDensity
      sizeBiasWeight = gammaProbability := by
  rw [positive_haar_weighted_probability, unit_exp_weighted_by_coordinate]

/-- The complete density in the marked logarithmic coordinate recovers p pointwise. -/
theorem marked_gumbel_density_identifies (q : ℝ → ℝ)
    (hq : ∀ x, q (gumbelCoordinate x) = gumbelDensity x) :
    EqOn q SigmaPresentations.density (Ioi 0) := by
  intro t ht
  have he := hq (-Real.log t)
  simpa only [gumbelCoordinate, neg_neg, Real.exp_log ht, gumbel_density_reconstructs t ht] using he

/-- A full Haar-weighted law identifies its continuous nonnegative density on
the positive ray. Continuity upgrades almost-everywhere recovery to pointwise recovery. -/
theorem positive_haar_probability_identifies (q : ℝ → ℝ)
    (hq : ContinuousOn q (Ioi 0)) (hq0 : ∀ t ∈ Ioi (0:ℝ), 0 ≤ q t)
    (he : positiveHaar.withDensity (fun t => ENNReal.ofReal (q t)) = unitExpProbability) :
    EqOn q SigmaPresentations.density (Ioi 0) := by
  have hm := (hq.aemeasurable (μ := volume) measurableSet_Ioi).ennreal_ofReal
  have hp : Continuous SigmaPresentations.density := by unfold SigmaPresentations.density; fun_prop
  rw [← positive_haar_weighted_probability, positiveHaar,
    ← withDensity_mul₀ measurable_inv.ennreal_ofReal.aemeasurable hm,
    ← withDensity_mul₀ measurable_inv.ennreal_ofReal.aemeasurable
      hp.measurable.ennreal_ofReal.aemeasurable] at he
  have hae := (withDensity_eq_iff_of_sigmaFinite
    (measurable_inv.ennreal_ofReal.aemeasurable.mul hm)
    (measurable_inv.ennreal_ofReal.aemeasurable.mul hp.measurable.ennreal_ofReal.aemeasurable)).mp he
  apply Measure.eqOn_open_of_ae_eq (μ := volume) _ isOpen_Ioi hq hp.continuousOn
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with t ht htpos
  change ENNReal.ofReal t⁻¹ * ENNReal.ofReal (q t) =
    ENNReal.ofReal t⁻¹ * ENNReal.ofReal (SigmaPresentations.density t) at ht
  rw [← ENNReal.ofReal_mul (inv_pos.mpr htpos).le,
    ← ENNReal.ofReal_mul (inv_pos.mpr htpos).le] at ht
  have hr := congrArg ENNReal.toReal ht
  rw [ENNReal.toReal_ofReal (mul_nonneg (inv_pos.mpr htpos).le (hq0 t htpos)),
    ENNReal.toReal_ofReal (mul_nonneg (inv_pos.mpr htpos).le (SigmaPresentations.density_pos htpos).le)] at hr
  exact mul_left_cancel₀ (inv_ne_zero (ne_of_gt htpos)) hr

theorem gamma_probability_ne_haar_weighted :
    gammaProbability ≠ positiveHaar.withDensity (fun t => ENNReal.ofReal (SigmaPresentations.density t)) := by
  rw [positive_haar_weighted_probability]
  intro he
  have hg := gamma_probability_laplace (s := 1) (by norm_num)
  have hu := unit_exp_laplace 1 (by norm_num)
  rw [he] at hg
  change (∫ t : ℝ, Real.exp (-(1*t)) ∂unitExpProbability) = _ at hu
  rw [hu] at hg
  norm_num at hg

theorem gumbel_coordinate_pullback :
    Measure.map (fun t : ℝ => -Real.log t) unitExpProbability = gumbelProbability := by
  rw [← gumbel_coordinate_pushforward,
    Measure.map_map Real.measurable_log.neg (by unfold gumbelCoordinate; fun_prop)]
  have he : (fun t : ℝ => -Real.log t) ∘ gumbelCoordinate = id := by
    funext x
    simp [Function.comp_def, gumbelCoordinate]
  rw [he, Measure.map_id]

/-- The interval formula also verifies finite Haar mass locally inside the positive ray. -/
theorem positive_haar_interval (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    positiveHaar (Ioc a b) = ENNReal.ofReal (Real.log b - Real.log a) := by
  rw [← positive_haar_exp, Measure.map_apply Real.measurable_exp measurableSet_Ioc]
  have he : Real.exp ⁻¹' Ioc a b = Ioc (Real.log a) (Real.log b) := by
    ext x
    simp only [mem_preimage, mem_Ioc]
    rw [← Real.exp_log ha, ← Real.exp_log hb, Real.exp_lt_exp, Real.exp_le_exp,
      Real.log_exp, Real.log_exp]
  rw [he, Real.volume_Ioc]

end
end Sigma
