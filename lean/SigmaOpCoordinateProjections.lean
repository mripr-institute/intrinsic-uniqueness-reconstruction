import SigmaOpCoordinateRecovery
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

namespace Sigma
noncomputable section
open MeasureTheory Set
open scoped ENNReal

private theorem recovery_power_bound (a t : ℝ) (n : ℕ) :
    ‖coordinateRecoveryKernel a t ^ n‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (coordinate_recovery_kernel_pos a t).le n)]
  exact pow_le_one₀ (coordinate_recovery_kernel_pos a t).le
    (coordinate_recovery_kernel_le_one a t)

/-- Vanishing against the bounded determining probes forces an integrable
real density to vanish. Positive densities allow reuse of measure uniqueness. -/
theorem coordinate_recovery_real_annihilator
    (μ : Measure ℝ) [IsFiniteMeasure μ] (f : ℝ → ℝ) (hf : Integrable f μ)
    (hz : ∀ a : ℝ, ∀ n : ℕ, (∫ t, coordinateRecoveryKernel a t ^ n * f t ∂μ) = 0) :
    f =ᵐ[μ] 0 := by
  let p := fun t => |f t| + f t
  let q := fun t => |f t|
  have hp : Integrable p μ := hf.abs.add hf
  have hq : Integrable q μ := hf.abs
  have hpn (t) : 0 ≤ p t := by dsimp [p]; linarith [neg_abs_le (f t)]
  have hqn (t) : 0 ≤ q t := abs_nonneg _
  letI := isFiniteMeasure_withDensity_ofReal hp.2
  letI := isFiniteMeasure_withDensity_ofReal hq.2
  have hmoment (g : ℝ → ℝ) (hg : Integrable g μ) (hgn : ∀ t, 0 ≤ g t)
      (a : ℝ) (n : ℕ) :
      (∫ t, coordinateRecoveryKernel a t ^ n ∂μ.withDensity (fun t => ENNReal.ofReal (g t))) =
        ∫ t, coordinateRecoveryKernel a t ^ n * g t ∂μ := by
    change (∫ t, coordinateRecoveryKernel a t ^ n
      ∂μ.withDensity (fun t => (Real.toNNReal (g t) : ℝ≥0∞))) = _
    rw [integral_withDensity_eq_integral_smul₀ hg.aestronglyMeasurable.aemeasurable.real_toNNReal]
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (hgn _), smul_eq_mul, mul_comm]
  have he : μ.withDensity (fun t => ENNReal.ofReal (p t)) =
      μ.withDensity (fun t => ENNReal.ofReal (q t)) := by
    apply coordinate_recovery_measures_unique
    intro a n
    rw [hmoment p hp hpn, hmoment q hq hqn]
    have hb : AEStronglyMeasurable (fun t => coordinateRecoveryKernel a t ^ n) μ :=
      (by unfold coordinateRecoveryKernel; fun_prop : Measurable
        (fun t => coordinateRecoveryKernel a t ^ n)).aestronglyMeasurable
    have hip := hf.abs.bdd_mul hb ⟨1, fun t => recovery_power_bound a t n⟩
    have hif := hf.bdd_mul hb ⟨1, fun t => recovery_power_bound a t n⟩
    simp only [p, mul_add]
    rw [integral_add hip hif, hz a n, add_zero]
  have hae := (withDensity_eq_iff_of_sigmaFinite
    hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    hq.aestronglyMeasurable.aemeasurable.ennreal_ofReal).mp he
  filter_upwards [hae] with t ht
  have h := (ENNReal.ofReal_eq_ofReal_iff (hpn t) (hqn t)).mp ht
  change f t = 0
  dsimp [p, q] at h
  linarith

theorem coordinate_recovery_complex_annihilator
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : Lp ℂ 2 μ)
    (hz : ∀ a : ℝ, ∀ n : ℕ,
      @inner ℂ (Lp ℂ 2 μ) _ (coordinateRecoveryPower μ a n) f = 0) : f = 0 := by
  have hf : Integrable (f : ℝ → ℂ) μ := (Lp.memℒp f).integrable (by norm_num)
  have hb (a : ℝ) (n : ℕ) :
      Integrable (fun t => (coordinateRecoveryKernel a t ^ n : ℂ) * (f : ℝ → ℂ) t) μ := by
    apply hf.bdd_mul
    · exact ((Complex.measurable_ofReal.comp
        (show Measurable (coordinateRecoveryKernel a) by
          unfold coordinateRecoveryKernel; fun_prop)).pow_const n).aestronglyMeasurable
    · refine ⟨1, fun t => ?_⟩
      simpa only [← Complex.ofReal_pow, Complex.norm_real] using recovery_power_bound a t n
  have hi (a : ℝ) (n : ℕ) :
      (∫ t, (coordinateRecoveryKernel a t ^ n : ℂ) * (f : ℝ → ℂ) t ∂μ) = 0 := by
    rw [← hz a n, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coordinate_recovery_power_coe μ a n] with t ht
    simp [RCLike.inner_apply, ht, mul_comm]
  have hr : (fun t => ((f : ℝ → ℂ) t).re) =ᵐ[μ] 0 := by
    apply coordinate_recovery_real_annihilator μ _ (Complex.reCLM.integrable_comp hf)
    intro a n
    have h := integral_re (hb a n)
    rw [hi, map_zero] at h
    simp only [← Complex.ofReal_pow] at h
    simpa only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using h
  have hm : (fun t => ((f : ℝ → ℂ) t).im) =ᵐ[μ] 0 := by
    apply coordinate_recovery_real_annihilator μ _ (Complex.imCLM.integrable_comp hf)
    intro a n
    have h := integral_im (hb a n)
    rw [hi, map_zero] at h
    simp only [← Complex.ofReal_pow] at h
    simpa only [RCLike.im_to_complex, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] using h
  apply Lp.ext
  filter_upwards [hr, hm, Lp.coeFn_zero ℂ 2 μ] with t ht hi hz
  rw [hz]
  exact Complex.ext ht hi

/-- A unitary fixing the coordinate probes fixes every L² vector. -/
theorem coordinate_marked_unitary_eq_refl
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (hU : CoordinateMultiplicationIntertwines μ μ U)
    (hone : U (coordinateConstantOne μ) = coordinateConstantOne μ) (f : Lp ℂ 2 μ) :
    U f = f := by
  apply sub_eq_zero.mp
  apply coordinate_recovery_complex_annihilator
  intro a n
  rw [inner_sub_right]
  have he := U.inner_map_map (coordinateRecoveryPower μ a n) f
  rw [coordinate_recovery_power_intertwines μ μ U hU hone] at he
  exact sub_eq_zero.mpr he

/-- Every actual Borel multiplication projection is recovered from the
maximal multiplication operator together with one. -/
theorem marked_multiplication_unitary_intertwines_projections
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : CoordinateMultiplicationIntertwines μ ν U)
    (hone : U (coordinateConstantOne μ) = coordinateConstantOne ν)
    (E : Set ℝ) (hE : MeasurableSet E) (f : Lp ℂ 2 μ) :
    U (coordinateIndicatorOperator μ E hE f) = coordinateIndicatorOperator ν E hE (U f) := by
  have he := marked_multiplication_unitary_preserves_probability μ ν U hU hone
  subst ν
  rw [coordinate_marked_unitary_eq_refl μ U hU hone,
    coordinate_marked_unitary_eq_refl μ U hU hone]

end
end Sigma
