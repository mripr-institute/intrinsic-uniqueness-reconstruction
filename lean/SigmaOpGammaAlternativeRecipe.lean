import SigmaProbGammaTransforms

namespace Sigma
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

/-- The alternative shape-a recipe is the actual Gamma probability measure. -/
def alternativeGammaMixingMeasure (a : ℝ) : Measure ℝ := gammaMeasure a 1

instance alternative_gamma_probability (a : ℝ) (ha : 0 < a) :
    IsProbabilityMeasure (alternativeGammaMixingMeasure a) :=
  isProbabilityMeasureGamma ha (by norm_num)

theorem alternative_gamma_density_integral (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ) :
    (∫ t, f t ∂alternativeGammaMixingMeasure a) =
      ∫ t : ℝ in Ioi 0, (t ^ (a - 1) * Real.exp (-t) / Real.Gamma a) * f t := by
  change (∫ t, f t ∂volume.withDensity
    (fun t => ((Real.toNNReal (gammaPDFReal a 1 t) : ℝ≥0) : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul
    ((measurable_gammaPDFReal a 1).real_toNNReal)]
  have hfun : (fun t => Real.toNNReal (gammaPDFReal a 1 t) • f t) =
      (Ici (0 : ℝ)).indicator
        (fun t => (t ^ (a - 1) * Real.exp (-t) / Real.Gamma a) * f t) := by
    funext t
    rw [NNReal.smul_def, smul_eq_mul,
      Real.coe_toNNReal _ (gammaPDFReal_nonneg ha (by norm_num) t)]
    by_cases ht : 0 ≤ t
    · simp only [gammaPDFReal, if_pos ht,
        Set.indicator_of_mem (mem_Ici.mpr ht)]
      rw [show (1 : ℝ) ^ a = 1 by simp]
      ring
    · have hnot : t ∉ Ici (0 : ℝ) := ht
      simp [gammaPDFReal, ht, hnot]
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

/-- Every positive shape gives the paper's different, fully normalized
mixing measure, with its exact real Laplace transform on the closed ray. -/
theorem alternative_gamma_laplace (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    (∫ t : ℝ, Real.exp (-(b * t)) ∂alternativeGammaMixingMeasure a) =
      (1 + b) ^ (-a) := by
  rw [alternative_gamma_density_integral a ha]
  have hr : 0 < 1 + b := by linarith
  have hΓ : Real.Gamma a ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos ha)
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr
  calc
    (∫ t : ℝ in Ioi 0,
        (t ^ (a - 1) * Real.exp (-t) / Real.Gamma a) * Real.exp (-(b * t))) =
        (1 / Real.Gamma a) *
          (∫ t : ℝ in Ioi 0, t ^ (a - 1) * Real.exp (-((1 + b) * t))) := by
      rw [← integral_mul_left]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have he : Real.exp (-t) * Real.exp (-(b * t)) =
          Real.exp (-((1 + b) * t)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      dsimp only
      rw [← he]
      ring
    _ = (1 / Real.Gamma a) * ((1 / (1 + b)) ^ a * Real.Gamma a) := by rw [hi]
    _ = (1 + b) ^ (-a) := by
      rw [Real.rpow_neg hr.le]
      simp only [one_div, Real.inv_rpow hr.le]
      field_simp [hΓ]

theorem alternative_gamma_measure_ne_canonical (a : ℝ) (ha : 0 < a)
    (ha2 : a ≠ 2) : alternativeGammaMixingMeasure a ≠ gammaProbability := by
  intro h
  have hleft := alternative_gamma_laplace a 1 ha (by norm_num)
  have hright := alternative_gamma_laplace 2 1 (by norm_num) (by norm_num)
  have heq : (2 : ℝ) ^ (-a) = (2 : ℝ) ^ (-(2 : ℝ)) := by
    calc
      (2 : ℝ) ^ (-a) =
          ∫ t : ℝ, Real.exp (-(1 * t)) ∂alternativeGammaMixingMeasure a := by
            simpa only [show (1 + 1 : ℝ) = 2 by norm_num] using hleft.symm
      _ = ∫ t : ℝ, Real.exp (-(1 * t)) ∂alternativeGammaMixingMeasure 2 := by
            rw [h]
            rfl
      _ = (2 : ℝ) ^ (-(2 : ℝ)) := by
            simpa only [show (1 + 1 : ℝ) = 2 by norm_num] using hright
  exact ha2 (neg_inj.mp ((Real.strictMono_rpow_of_base_gt_one
    (by norm_num : (1 : ℝ) < 2)).injective heq))

end
end Sigma
