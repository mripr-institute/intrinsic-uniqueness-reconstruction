import SigmaProbDeficitDomain
import SigmaProbSupport

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

theorem gamma_probability_measure_positive_set (A : Set ℝ) (hA : MeasurableSet A)
    (hpos : A ⊆ Ioi 0) :
    gammaProbability A = ENNReal.ofReal (∫ t : ℝ in A, SigmaPresentations.density t) := by
  rw [gammaProbability, ProbabilityTheory.gammaMeasure, withDensity_apply _ hA]
  have he : (∫⁻ t in A, ProbabilityTheory.gammaPDF 2 1 t) =
      ∫⁻ t in A, ENNReal.ofReal (SigmaPresentations.density t) := by
    apply setLIntegral_congr_fun hA
    filter_upwards with t ht
    simp only [ProbabilityTheory.gammaPDF, gamma_pdf_intrinsic,
      if_pos (hpos ht).le]
  rw [he, ← ofReal_integral_eq_lintegral_ofReal
    (intrinsic_density_integrable.mono_set hpos)]
  filter_upwards [ae_restrict_mem hA] with t ht
  exact (SigmaPresentations.density_pos (hpos ht)).le

theorem gamma_probability_tail (a : ℝ) (ha : 0 ≤ a) :
    gammaProbability (Ioi a) = ENNReal.ofReal (gammaSurvival a) := by
  rw [gamma_probability_measure_positive_set _ measurableSet_Ioi
    (Ioi_subset_Ioi ha), gamma_survival_tail_integral a ha]

theorem gamma_density_interval (a b : ℝ) (hab : a ≤ b) :
    (∫ t : ℝ in Icc a b, SigmaPresentations.density t) = gammaSurvival a-gammaSurvival b := by
  have hd (t : ℝ) : HasDerivAt (fun u => -gammaSurvival u) (SigmaPresentations.density t) t := by
    simpa using (gamma_survival_derivative t).neg
  have hp : Continuous SigmaPresentations.density := by unfold SigmaPresentations.density; fun_prop
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      (hp.intervalIntegrable a b)]
  ring

theorem gamma_probability_interval (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    gammaProbability (Icc a b) = ENNReal.ofReal (gammaSurvival a-gammaSurvival b) := by
  rw [gamma_probability_measure_positive_set _ measurableSet_Icc
    (fun t ht => lt_of_lt_of_le ha ht.1), gamma_density_interval a b hab]

/-- The canonical target CDF is evaluated on its actual inverse roots. -/
theorem gamma_deficit_cdf_from_roots (v a b : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hb1 : 1 ≤ b) (ha : SigmaBase.potential a = v) (hb : SigmaBase.potential b = v) :
    gammaDeficitProbability (Iic v) =
      ENNReal.ofReal (gammaSurvival a-gammaSurvival b) := by
  rw [gammaDeficitProbability, Measure.map_apply intrinsic_potential_measurable measurableSet_Iic]
  have hconull : gammaProbability (Ioi (0 : ℝ))ᶜ = 0 := by
    change gammaProbability {t : ℝ | ¬ 0 < t} = 0
    exact ae_iff.mp (operator_integer_samples_ae_pos gammaProbability
      operator_gamma_probability_integer_samples)
  rw [← measure_inter_conull hconull,
    intrinsic_potential_two_branch.sublevel_interval a b v ha0 ha1 hb1 ha hb,
    gamma_probability_interval a b ha0 (ha1.trans hb1)]

theorem gamma_deficit_cdf_zero_at_zero : gammaDeficitProbability (Iic 0) = 0 := by
  have he := gamma_deficit_cdf_from_roots 0 1 1 (by norm_num) le_rfl le_rfl
    (by simp [SigmaBase.potential]) (by simp [SigmaBase.potential])
  simpa using he

theorem gamma_deficit_no_atom_at_zero : gammaDeficitProbability {0} = 0 := by
  exact measure_mono_null (by intro t ht; simpa only [mem_singleton_iff.mp ht] using (show (0 : ℝ) ≤ 0 from le_rfl)) gamma_deficit_cdf_zero_at_zero

theorem gamma_deficit_cdf_negative (v : ℝ) (hv : v < 0) :
    gammaDeficitProbability (Iic v) = 0 :=
  measure_mono_null (Iic_subset_Iic.mpr hv.le) gamma_deficit_cdf_zero_at_zero

end
end Sigma
