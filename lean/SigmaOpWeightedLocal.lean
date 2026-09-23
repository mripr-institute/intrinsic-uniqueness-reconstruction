import SigmaOpLaguerreL2
import SigmaProbSupport
import SigmaOpSobolevLimit

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal NNReal

theorem gamma_ae_iff_positive_volume_ae {P : ℝ → Prop} :
    (∀ᵐ t ∂gammaProbability, P t) ↔ ∀ᵐ t ∂volume.restrict (Ioi 0), P t := by
  change (∀ᵐ t ∂volume.withDensity (gammaPDF 2 1), P t) ↔ _
  have hm : Measurable (gammaPDF 2 1) := (measurable_gammaPDFReal 2 1).ennreal_ofReal
  rw [ae_withDensity_iff_ae_restrict hm]
  change (∀ᵐ t ∂volume.restrict (Function.support (gammaPDF 2 1)), P t) ↔ _
  rw [gamma_pdf_function_support]

theorem gamma_compact_volume_comparison {a b : ℝ} (ha : 0 < a) :
    volume.restrict (Icc a b) ≤ ENNReal.ofReal ((a*Real.exp (-b))⁻¹) • gammaProbability := by
  let d := a*Real.exp (-b)
  have hd : 0 < d := mul_pos ha (Real.exp_pos _)
  have hle : ENNReal.ofReal d • volume.restrict (Icc a b) ≤ gammaProbability := by
    rw [← withDensity_const, ← withDensity_indicator measurableSet_Icc]
    apply withDensity_mono
    apply Eventually.of_forall
    intro t
    by_cases ht : t ∈ Icc a b
    · rw [indicator_of_mem ht]
      simp only [gammaPDF, gamma_pdf_intrinsic, if_pos (ha.trans_le ht.1).le]
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul ht.1 (Real.exp_le_exp.mpr (neg_le_neg ht.2))
        (Real.exp_pos _).le (ha.trans_le ht.1).le
    · simp only [indicator_of_not_mem ht, zero_le]
  apply Measure.le_iff.mpr
  intro s hs
  have hls := (Measure.le_iff.mp hle) s hs
  rw [Measure.smul_apply] at hls ⊢
  change volume.restrict (Icc a b) s ≤ ENNReal.ofReal d⁻¹ * gammaProbability s
  rw [ENNReal.ofReal_inv_of_pos hd]
  calc
    volume.restrict (Icc a b) s = (ENNReal.ofReal d)⁻¹ *
        (ENNReal.ofReal d * volume.restrict (Icc a b) s) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hd).ne'
        ENNReal.ofReal_ne_top, one_mul]
    _ ≤ _ := mul_le_mul_left' hls _

theorem gamma_l2_integral_norm_le (x : LaguerreWeightedHilbert) :
    (∫ t, ‖x t‖ ∂gammaProbability) ≤ ‖x‖ := by
  have h := ENNReal.toReal_mono (Lp.eLpNorm_ne_top x)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Lp.aestronglyMeasurable x))
  rw [Lp.norm_def]
  convert h using 1
  rw [eLpNorm_one_eq_lintegral_nnnorm, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun t => norm_nonneg (x t))) (Lp.aestronglyMeasurable x).norm]
  congr 1
  apply lintegral_congr
  intro t
  exact ofReal_norm_eq_coe_nnnorm (x t)

theorem gamma_l2_locally_integrable (x : LaguerreWeightedHilbert) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (x : ℝ → ℂ) (Icc a b) volume := by
  have hi : Integrable (x : ℝ → ℂ) gammaProbability :=
    (Lp.memℒp x).integrable (by norm_num)
  exact (hi.smul_measure ENNReal.ofReal_ne_top).mono_measure (gamma_compact_volume_comparison ha)

theorem gamma_l2_local_norm_bound (x : LaguerreWeightedHilbert) {a b : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Icc a b, ‖x t‖) ≤ ((a*Real.exp (-b))⁻¹)*‖x‖ := by
  have hi : Integrable (fun t => ‖x t‖) gammaProbability :=
    ((Lp.memℒp x).integrable (by norm_num)).norm
  have hm := integral_mono_measure (gamma_compact_volume_comparison (b := b) ha)
    (Eventually.of_forall (fun t => norm_nonneg (x t)))
    (hi.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left (gamma_l2_integral_norm_le x) (by positivity))

theorem inverse_sqrt_complex_norm_bound {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    ‖((Real.sqrt t : ℂ)⁻¹)‖ ≤ (Real.sqrt a)⁻¹ := by
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  simpa only [one_div] using
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr ha) (Real.sqrt_le_sqrt hat)

theorem gamma_l2_div_sqrt_integrableOn (x : LaguerreWeightedHilbert)
    {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => x t / (Real.sqrt t : ℂ)) (Icc a b) volume := by
  have hm : Measurable (fun t : ℝ => ((Real.sqrt t : ℂ)⁻¹)) := by fun_prop
  have h := (gamma_l2_locally_integrable x (b := b) ha).bdd_mul'
    hm.aestronglyMeasurable (c := (Real.sqrt a)⁻¹) ?_
  · simpa only [div_eq_mul_inv, mul_comm] using h
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact inverse_sqrt_complex_norm_bound ha ht.1

theorem gamma_l2_div_sqrt_locally_integrable (x : LaguerreWeightedHilbert) :
    LocallyIntegrableOn (fun t : ℝ => x t / (Real.sqrt t : ℂ)) (Ioi 0) volume := by
  intro t ht
  change 0 < t at ht
  refine ⟨Icc (t/2) (t+1), ?_, gamma_l2_div_sqrt_integrableOn x (by linarith)⟩
  exact mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))

theorem gamma_l2_div_sqrt_local_norm_bound (x : LaguerreWeightedHilbert)
    {a b : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Icc a b, ‖x t / (Real.sqrt t : ℂ)‖) ≤
      (Real.sqrt a)⁻¹ * (a*Real.exp (-b))⁻¹ * ‖x‖ := by
  have hx := gamma_l2_locally_integrable x (b := b) ha
  have hq := gamma_l2_div_sqrt_integrableOn x (b := b) ha
  calc
    _ ≤ ∫ t : ℝ in Icc a b, (Real.sqrt a)⁻¹ * ‖x t‖ := by
      apply setIntegral_mono_on hq.norm (hx.norm.const_mul _) measurableSet_Icc
      intro t ht
      rw [div_eq_mul_inv, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (inverse_sqrt_complex_norm_bound ha ht.1) (norm_nonneg _)
    _ = (Real.sqrt a)⁻¹ * ∫ t : ℝ in Icc a b, ‖x t‖ := integral_mul_left _ _
    _ ≤ (Real.sqrt a)⁻¹ * (a*Real.exp (-b))⁻¹ * ‖x‖ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (gamma_l2_local_norm_bound x ha) (by positivity)

theorem gamma_l2_div_sqrt_local_L1_tendsto (x : ℕ → LaguerreWeightedHilbert)
    (y : LaguerreWeightedHilbert) (hxy : Tendsto x atTop (𝓝 y))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun k => ∫ t : ℝ in uIcc a b,
      ‖x k t / (Real.sqrt t : ℂ) - y t / (Real.sqrt t : ℂ)‖) atTop (𝓝 0) := by
  have hn := (tendsto_iff_norm_sub_tendsto_zero.mp hxy).const_mul
    ((Real.sqrt (min a b))⁻¹ * (min a b*Real.exp (-max a b))⁻¹)
  simp only [mul_zero] at hn
  apply squeeze_zero (fun k => integral_nonneg (fun t => norm_nonneg _)) (fun k => ?_) hn
  have he : (∫ t : ℝ in uIcc a b,
      ‖x k t / (Real.sqrt t : ℂ) - y t / (Real.sqrt t : ℂ)‖) =
      ∫ t : ℝ in uIcc a b, ‖(x k-y) t / (Real.sqrt t : ℂ)‖ := by
    apply integral_congr_ae
    have hsub := gamma_ae_iff_positive_volume_ae.mp (Lp.coeFn_sub (x k) y)
    have hm : volume.restrict (uIcc a b) ≤ volume.restrict (Ioi 0) :=
      Measure.restrict_mono (fun t ht => (lt_min ha hb).trans_le ht.1) le_rfl
    filter_upwards [hm.absolutelyContinuous hsub] with t ht
    simp only [Pi.sub_apply] at ht
    rw [ht, sub_div]
  rw [he]
  exact gamma_l2_div_sqrt_local_norm_bound (x k-y) (lt_min ha hb)

end
end Sigma
