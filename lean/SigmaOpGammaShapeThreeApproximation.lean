import SigmaOpGammaShapeThreeDifferential
import SigmaOpLogCutoffApproximation
import SigmaOpUpperApproximation

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff ENNReal NNReal
set_option maxHeartbeats 800000

theorem gamma_shape_three_ae_pos : ∀ᵐ t ∂gammaShapeThreeProbability, 0 < t := by
  have hm : gammaShapeThreeProbability (Iic 0) = 0 := by
    rw [gammaShapeThreeProbability, gammaMeasure, withDensity_apply _ measurableSet_Iic]
    have he : ∫⁻ t : ℝ in Iic 0, gammaPDF 3 1 t = 0 := by
      rw [setLIntegral_congr_fun measurableSet_Iic
        (ae_of_all _ (fun t ht => ?_)), lintegral_zero]
      rw [gammaPDF, gamma_shape_three_pdf]
      by_cases hp : 0 ≤ t
      · have hz : t = 0 := le_antisymm ht hp
        simp [hz]
      · simp [hp]
    exact he
  rw [ae_iff]
  simpa only [not_lt] using hm

theorem gamma_shape_three_inv_square_integral :
    (∫ t : ℝ, (t⁻¹)^2 ∂gammaShapeThreeProbability) = 1/2 := by
  rw [gamma_shape_three_integral]
  calc
    (∫ t : ℝ in Ioi 0, (t^2 * Real.exp (-t) / 2) * (t⁻¹)^2) =
        (∫ t : ℝ in Ioi 0, Real.exp (-t)) / 2 := by
      rw [← integral_div]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      field_simp [ne_of_gt ht]
      ring
    _ = 1/2 := by
      have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi
        (a := 1) (r := 1) (by norm_num) (by norm_num)
      norm_num at hi
      rw [hi]

theorem gamma_shape_three_inv_mem_l2 :
    Memℒp (fun t : ℝ => t⁻¹) 2 gammaShapeThreeProbability := by
  apply (memℒp_two_iff_integrable_sq (by fun_prop)).mpr
  by_contra h
  have he := gamma_shape_three_inv_square_integral
  rw [integral_undef h] at he
  norm_num at he

theorem gamma_shape_three_l2_norm_sq_of_ae (x : GammaShapeThreeWeightedHilbert)
    (f : ℝ → ℂ) (hf : (x : ℝ → ℂ) =ᵐ[gammaShapeThreeProbability] f) :
    ‖x‖^2 = ∫ t : ℝ, ‖f t‖^2 ∂gammaShapeThreeProbability := by
  rw [norm_sq_eq_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner x x)]
  apply integral_congr_ae
  filter_upwards [hf] with t ht
  rw [ht]
  exact (norm_sq_eq_inner (𝕜 := ℂ) (f t)).symm

theorem gamma_shape_three_l2_dominated_limit (x : ℕ → GammaShapeThreeWeightedHilbert)
    (y : GammaShapeThreeWeightedHilbert) (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ)
    (hx : ∀ k, (x k : ℝ → ℂ) =ᵐ[gammaShapeThreeProbability] F k)
    (hy : (y : ℝ → ℂ) =ᵐ[gammaShapeThreeProbability] f)
    (hF : ∀ k, Continuous (F k)) (hf : Continuous f)
    (g : ℝ → ℝ) (hg : Memℒp g 2 gammaShapeThreeProbability)
    (hbound : ∀ k, ∀ᵐ t ∂gammaShapeThreeProbability, ‖F k t-f t‖ ≤ g t)
    (hlim : ∀ᵐ t ∂gammaShapeThreeProbability, Tendsto (fun k => F k t) atTop (𝓝 (f t))) :
    Tendsto x atTop (𝓝 y) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hi : Integrable (fun t => g t^2) gammaShapeThreeProbability :=
    (memℒp_two_iff_integrable_sq hg.1).mp hg
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := gammaShapeThreeProbability) (l := (atTop : Filter ℕ))
    (F := fun k t => ‖F k t-f t‖^2) (f := fun _ => (0 : ℝ))
    (fun t => g t^2) ?_ ?_ hi ?_
  · have he (k : ℕ) : ‖x k-y‖^2 = ∫ t, ‖F k t-f t‖^2 ∂gammaShapeThreeProbability := by
      apply gamma_shape_three_l2_norm_sq_of_ae
      filter_upwards [Lp.coeFn_sub (x k) y, hx k, hy] with t ht hxt hyt
      simpa only [Pi.sub_apply, hxt, hyt] using ht
    have hh : Tendsto (fun k => ‖x k-y‖^2) atTop (𝓝 0) := by
      simpa only [he, integral_zero] using h
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hh
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs
  · exact Eventually.of_forall fun k =>
      (((hF k).sub hf).norm.pow 2).aestronglyMeasurable
  · apply Eventually.of_forall
    intro k
    filter_upwards [hbound k] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) ht 2
  · filter_upwards [hlim] with t ht
    simpa using ((ht.sub_const (f t)).norm.pow 2)

theorem gamma_shape_three_expression_eq_shape_two (f : ℝ → ℂ) (t : ℝ) :
    gammaShapeThreeComplexExpression f t = opComplexLaguerreExpression f t - deriv f t := by
  dsimp [gammaShapeThreeComplexExpression, opComplexLaguerreExpression]
  ring

theorem gamma_shape_three_expression_product (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (t : ℝ) :
    gammaShapeThreeComplexExpression (fun u => f u*g u) t =
      f t * gammaShapeThreeComplexExpression g t + g t * gammaShapeThreeComplexExpression f t -
        2*(t : ℂ)*deriv f t*deriv g t := by
  simp only [gamma_shape_three_expression_eq_shape_two]
  rw [op_complex_laguerre_product f g hf hg t,
    deriv_mul (hf.differentiable (by simp) t) (hg.differentiable (by simp) t)]
  ring

theorem gamma_shape_three_expression_ofReal (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    gammaShapeThreeComplexExpression (fun u => (f u : ℂ)) t =
      ((-t*deriv (deriv f) t - (3-t)*deriv f t : ℝ) : ℂ) := by
  rw [gamma_shape_three_expression_eq_shape_two, op_complex_laguerre_ofReal f hf t]
  have hd : deriv (fun u => (f u : ℂ)) t = Complex.ofReal (deriv f t) := by
    simpa only [Function.comp_apply] using
      (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
        (hf.differentiable (by simp) t).hasDerivAt).deriv
  rw [hd]
  push_cast
  ring

theorem gamma_shape_three_log_cutoff_error_formula (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    gammaShapeThreeComplexExpression (fun u => (operatorLogCutoff R u : ℂ)*f u) t -
      gammaShapeThreeComplexExpression f t =
        ((operatorLogCutoff R t-1 : ℝ) : ℂ)*gammaShapeThreeComplexExpression f t +
        f t*gammaShapeThreeComplexExpression (fun u => (operatorLogCutoff R u : ℂ)) t -
        2*(t : ℂ)*deriv (fun u => (operatorLogCutoff R u : ℂ)) t*deriv f t := by
  rw [gamma_shape_three_expression_product (fun u => (operatorLogCutoff R u : ℂ)) f
    (Complex.ofRealCLM.contDiff.comp (operator_log_cutoff_contDiff hR)) hf]
  push_cast
  ring

theorem gamma_shape_three_log_cutoff_scalar_bound {R t C : ℝ}
    (hR : 1 ≤ R) (ht : 0 < t) (hC0 : 0 ≤ C)
    (hC : ∀ u : ℝ, |deriv Real.smoothTransition u| ≤ C)
    (hC₂ : ∀ u : ℝ, |deriv (deriv Real.smoothTransition) u| ≤ C) :
    ‖gammaShapeThreeComplexExpression (fun u => (operatorLogCutoff R u : ℂ)) t‖ ≤
      5*C/t+C := by
  have hr : 0 < R := by linarith
  have hd := operator_log_cutoff_deriv_bound hr ht hC
  have hdd := operator_log_cutoff_second_deriv_bound hr ht hC hC₂
  have hd' : |deriv (operatorLogCutoff R) t| ≤ C/t := by
    exact hd.trans (div_le_div_of_nonneg_left hC0 ht (by nlinarith))
  have hdd' : |deriv (deriv (operatorLogCutoff R)) t| ≤ 2*C/t^2 := by
    have h1 : C/(R^2*t^2) ≤ C/t^2 :=
      div_le_div_of_nonneg_left hC0 (sq_pos_of_pos ht) (by nlinarith [sq_nonneg (R-1)])
    have h2 : C/(R*t^2) ≤ C/t^2 :=
      div_le_div_of_nonneg_left hC0 (sq_pos_of_pos ht) (by nlinarith [sq_nonneg t])
    convert hdd.trans (add_le_add h1 h2) using 1
    ring
  rw [gamma_shape_three_expression_ofReal _ (operator_log_cutoff_contDiff hr),
    Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ t*|deriv (deriv (operatorLogCutoff R)) t| +
        |3-t| * |deriv (operatorLogCutoff R) t| := by
      simpa only [abs_mul, abs_neg, abs_of_pos ht] using
        abs_sub (-t*deriv (deriv (operatorLogCutoff R)) t)
          ((3-t)*deriv (operatorLogCutoff R) t)
    _ ≤ t*(2*C/t^2)+(3+t)*(C/t) := by
      have hab : |3-t| ≤ 3+t := by
        exact (abs_sub 3 t).trans_eq (by simp [abs_of_pos ht])
      gcongr
    _ = 5*C/t+C := by field_simp; ring

theorem gamma_shape_three_log_cutoff_error_bound (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) {R t C M : ℝ} (hR : 1 ≤ R) (ht : 0 < t)
    (hC0 : 0 ≤ C) (hM0 : 0 ≤ M)
    (hC : ∀ u : ℝ, |deriv Real.smoothTransition u| ≤ C)
    (hC₂ : ∀ u : ℝ, |deriv (deriv Real.smoothTransition) u| ≤ C)
    (hfM : ‖f t‖ ≤ M) (hdM : ‖deriv f t‖ ≤ M) :
    ‖gammaShapeThreeComplexExpression (fun u => (operatorLogCutoff R u : ℂ)*f u) t -
        gammaShapeThreeComplexExpression f t‖ ≤
      ‖gammaShapeThreeComplexExpression f t‖+(5*C*M)*t⁻¹+3*C*M := by
  have hr : 0 < R := by linarith
  rw [gamma_shape_three_log_cutoff_error_formula f hf hr t]
  have hc : |operatorLogCutoff R t-1| ≤ 1 := abs_le.mpr
    ⟨by linarith [(operator_log_cutoff_bounds R t).1],
      by linarith [(operator_log_cutoff_bounds R t).2]⟩
  have hd : |deriv (operatorLogCutoff R) t| ≤ C/t :=
    (operator_log_cutoff_deriv_bound hr ht hC).trans
      (div_le_div_of_nonneg_left hC0 ht (by nlinarith))
  have hdc : deriv (fun u => (operatorLogCutoff R u : ℂ)) t =
      Complex.ofReal (deriv (operatorLogCutoff R) t) := by
    simpa only [Function.comp_apply] using
      (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
        ((operator_log_cutoff_contDiff hr).differentiable (by simp) t).hasDerivAt).deriv
  apply (norm_sub_le _ _).trans
  apply (add_le_add_right (norm_add_le _ _) _).trans
  simp only [norm_mul, hdc, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_ofNat, abs_of_pos ht]
  calc
    _ ≤ ‖gammaShapeThreeComplexExpression f t‖+M*(5*C/t+C)+2*t*(C/t)*M := by
      have he := gamma_shape_three_log_cutoff_scalar_bound hR ht hC0 hC hC₂
      have h1 := mul_le_mul_of_nonneg_right hc (norm_nonneg (gammaShapeThreeComplexExpression f t))
      have h2 := mul_le_mul hfM he (norm_nonneg _) hM0
      have h3 : 2*t*|deriv (operatorLogCutoff R) t| * ‖deriv f t‖ ≤ 2*t*(C/t)*M := by
        gcongr
      nlinarith
    _ = _ := by simp only [div_eq_mul_inv]; field_simp; ring

theorem gamma_shape_three_log_cutoff_derivatives_tendsto (t : ℝ) (ht : 0 < t) :
    Tendsto (fun k : ℕ => deriv (operatorLogCutoff (k+1 : ℝ)) t) atTop (𝓝 0) ∧
      Tendsto (fun k : ℕ => deriv (deriv (operatorLogCutoff (k+1 : ℝ))) t) atTop (𝓝 0) := by
  obtain ⟨C,hC0,hC,hC₂⟩ := smooth_transition_derivatives_bounded
  have hR : Tendsto (fun k : ℕ => (k+1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp hR
  constructor
  · apply squeeze_zero_norm
      (fun k => by simpa only [Real.norm_eq_abs] using
        operator_log_cutoff_deriv_bound (by positivity : 0 < (k+1 : ℝ)) ht hC)
    simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc] using (hi.const_mul (C*t⁻¹))
  · apply squeeze_zero_norm
      (fun k => by simpa only [Real.norm_eq_abs] using
        operator_log_cutoff_second_deriv_bound (by positivity : 0 < (k+1 : ℝ)) ht hC hC₂)
    have h1 := (hi.pow 2).const_mul (C*(t^2)⁻¹)
    have h2 := hi.const_mul (C*(t^2)⁻¹)
    simpa [div_eq_mul_inv, mul_inv_rev, inv_pow, mul_assoc] using h1.add h2

theorem gamma_shape_three_log_cutoff_image_pointwise (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun k : ℕ => gammaShapeThreeComplexExpression (operatorLogCutoffTest k f) t)
      atTop (𝓝 (gammaShapeThreeComplexExpression f t)) := by
  have hR : Tendsto (fun k : ℕ => (k+1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hc := (operator_log_cutoff_tendsto ht).comp hR
  have hd := (gamma_shape_three_log_cutoff_derivatives_tendsto t ht).1
  have hdd := (gamma_shape_three_log_cutoff_derivatives_tendsto t ht).2
  have he : Tendsto (fun k : ℕ =>
      gammaShapeThreeComplexExpression (fun u => (operatorLogCutoff (k+1 : ℝ) u : ℂ)) t)
      atTop (𝓝 0) := by
    have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((hdd.const_mul (-t)).sub (hd.const_mul (3-t)))
    have heq : (fun k : ℕ => gammaShapeThreeComplexExpression
        (fun u => (operatorLogCutoff (k+1 : ℝ) u : ℂ)) t) =
        fun k : ℕ => Complex.ofReal (-t*deriv (deriv (operatorLogCutoff (k+1 : ℝ))) t -
          (3-t)*deriv (operatorLogCutoff (k+1 : ℝ)) t) := by
      funext k
      exact gamma_shape_three_expression_ofReal _
        (operator_log_cutoff_contDiff (by positivity)) t
    rw [heq]
    simpa only [mul_zero, sub_zero, Complex.ofReal_zero, Function.comp_def] using hh
  have hdc : ∀ k : ℕ, deriv (fun u => (operatorLogCutoff (k+1 : ℝ) u : ℂ)) t =
      Complex.ofReal (deriv (operatorLogCutoff (k+1 : ℝ)) t) := by
    intro k
    simpa only [Function.comp_apply] using
      (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
        ((operator_log_cutoff_contDiff (by positivity : 0 < (k+1 : ℝ))).differentiable
          (by simp) t).hasDerivAt).deriv
  have hh := ((Complex.continuous_ofReal.continuousAt.tendsto.comp hc).mul_const
    (gammaShapeThreeComplexExpression f t)).add (he.const_mul (f t))
  have hj := ((Complex.continuous_ofReal.continuousAt.tendsto.comp hd).const_mul
    (2*(t : ℂ))).mul_const (deriv f t)
  have h := hh.sub hj
  convert h using 1
  · funext k
    change gammaShapeThreeComplexExpression
      (fun u => (operatorLogCutoff (k+1 : ℝ) u : ℂ)*f u) t = _
    rw [gamma_shape_three_expression_product
      (fun u => (operatorLogCutoff (k+1 : ℝ) u : ℂ)) f
      (Complex.ofRealCLM.contDiff.comp
        (operator_log_cutoff_contDiff (by positivity : 0 < (k+1 : ℝ)))) hf, hdc]
    dsimp only [Function.comp_apply]
  · simp

theorem gamma_shape_three_log_cutoff_vector_tendsto (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    Tendsto (fun k => gammaShapeThreeCompactVector (operatorLogCutoffTest k f)
      (operator_log_cutoff_test_smooth k f hf) (operator_log_cutoff_test_compact k f hs))
      atTop (𝓝 (gammaShapeThreeCompactVector f hf hs)) := by
  apply gamma_shape_three_l2_dominated_limit _ _ (operatorLogCutoffTest · f) f
    (fun k => gamma_shape_three_compact_vector_coe _ _ _)
    (gamma_shape_three_compact_vector_coe _ _ _)
    (fun k => (operator_log_cutoff_test_smooth k f hf).continuous) hf.continuous
    (fun t => ‖f t‖) (hf.continuous.memℒp_of_hasCompactSupport hs).norm
  · intro k
    apply Eventually.of_forall
    intro t
    change ‖(operatorLogCutoff (k+1 : ℝ) t : ℂ)*f t-f t‖ ≤ ‖f t‖
    rw [←sub_one_mul, norm_mul, ←Complex.ofReal_one, ←Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    have hb : |operatorLogCutoff (k+1 : ℝ) t-1| ≤ 1 := abs_le.mpr
      ⟨by linarith [(operator_log_cutoff_bounds (k+1 : ℝ) t).1],
        by linarith [(operator_log_cutoff_bounds (k+1 : ℝ) t).2]⟩
    exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq (one_mul _)
  · filter_upwards [gamma_shape_three_ae_pos] with t ht
    have hc := (operator_log_cutoff_tendsto ht).comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    simpa [operatorLogCutoffTest] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hc).mul_const (f t)

theorem gamma_shape_three_log_cutoff_image_tendsto (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    Tendsto (fun k => gammaShapeThreeCompactImage (operatorLogCutoffTest k f)
      (operator_log_cutoff_test_smooth k f hf) (operator_log_cutoff_test_compact k f hs))
      atTop (𝓝 (gammaShapeThreeCompactImage f hf hs)) := by
  obtain ⟨C,hC0,hC,hC₂⟩ := smooth_transition_derivatives_bounded
  obtain ⟨M,hM0,hfM,hdM⟩ := smooth_compact_function_derivative_bounded f hf hs
  have hD : Memℒp (gammaShapeThreeComplexExpression f) 2 gammaShapeThreeProbability :=
    (gamma_shape_three_expression_contDiff f hf).continuous.memℒp_of_hasCompactSupport
      (gamma_shape_three_expression_compact f hs)
  apply gamma_shape_three_l2_dominated_limit _ _
    (fun k => gammaShapeThreeComplexExpression (operatorLogCutoffTest k f))
    (gammaShapeThreeComplexExpression f)
    (fun k => gamma_shape_three_compact_image_coe _ _ _)
    (gamma_shape_three_compact_image_coe _ _ _)
    (fun k => (gamma_shape_three_expression_contDiff _
      (operator_log_cutoff_test_smooth k f hf)).continuous)
    (gamma_shape_three_expression_contDiff f hf).continuous
    (fun t => ‖gammaShapeThreeComplexExpression f t‖+(5*C*M)*t⁻¹+3*C*M)
    ((hD.norm.add (gamma_shape_three_inv_mem_l2.const_mul (5*C*M))).add (memℒp_const _))
  · intro k
    filter_upwards [gamma_shape_three_ae_pos] with t ht
    exact gamma_shape_three_log_cutoff_error_bound f hf
      (by norm_cast; omega : (1 : ℝ) ≤ (k+1 : ℝ)) ht hC0.le hM0.le hC hC₂ (hfM t) (hdM t)
  · filter_upwards [gamma_shape_three_ae_pos] with t ht
    exact gamma_shape_three_log_cutoff_image_pointwise f hf t ht

theorem gamma_shape_three_upper_error_formula (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (k : ℕ) (t : ℝ) :
    gammaShapeThreeComplexExpression (upperCutoffTest f k) t-gammaShapeThreeComplexExpression f t =
      ((steinCutoff (upperCutoffRadius k) t-1 : ℝ) : ℂ)*gammaShapeThreeComplexExpression f t +
      (-deriv (deriv (steinCutoff (upperCutoffRadius k))) t : ℂ)*((t : ℂ)*f t) +
      (-deriv (steinCutoff (upperCutoffRadius k)) t : ℂ)*((3-(t : ℂ))*f t) +
      (-2*deriv (steinCutoff (upperCutoffRadius k)) t : ℂ)*((t : ℂ)*deriv f t) := by
  unfold upperCutoffTest
  rw [gamma_shape_three_expression_product
    (fun u : ℝ => (steinCutoff (upperCutoffRadius k) u : ℂ)) f
    (Complex.ofRealCLM.contDiff.comp (steinCutoff_contDiff _)) hf,
    gamma_shape_three_expression_ofReal _ (steinCutoff_contDiff _)]
  have hd : deriv (fun u : ℝ => (steinCutoff (upperCutoffRadius k) u : ℂ)) t =
      Complex.ofReal (deriv (steinCutoff (upperCutoffRadius k)) t) := by
    simpa only [Function.comp_apply] using
      (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
        (((steinCutoff_contDiff _).differentiable (by simp) t).hasDerivAt)).deriv
  rw [hd]
  push_cast
  ring

theorem gamma_shape_three_upper_error_bound (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t : ℝ, |deriv (steinBump : ℝ → ℝ) t| ≤ C ∧
      |deriv (deriv (steinBump : ℝ → ℝ)) t| ≤ C) (k : ℕ) (t : ℝ) :
    ‖gammaShapeThreeComplexExpression (upperCutoffTest f k) t-gammaShapeThreeComplexExpression f t‖ ≤
      ‖gammaShapeThreeComplexExpression f t‖+C*‖(t:ℂ)*f t‖+
        C*‖(3-(t:ℂ))*f t‖+(2*C)*‖(t:ℂ)*deriv f t‖ := by
  rw [gamma_shape_three_upper_error_formula f hf k t]
  have hder := stein_cutoff_derivatives_bound C hC hb _ (upper_cutoff_radius_one_le k) t
  have hc : |steinCutoff (upperCutoffRadius k) t-1| ≤ 1 :=
    abs_le.mpr ⟨by linarith [(steinCutoff_bounds (upperCutoffRadius k) t).1],
      by linarith [(steinCutoff_bounds (upperCutoffRadius k) t).2]⟩
  apply (norm_add_le _ _).trans
  apply (add_le_add_right ((norm_add_le _ _).trans
    (add_le_add_right (norm_add_le _ _) _)) _).trans
  have h1 := mul_le_mul_of_nonneg_right hc (norm_nonneg (gammaShapeThreeComplexExpression f t))
  have h2 := mul_le_mul_of_nonneg_right hder.1 (norm_nonneg ((3-(t:ℂ))*f t))
  have h3 := mul_le_mul_of_nonneg_right hder.1 (norm_nonneg ((t:ℂ)*deriv f t))
  have h4 := mul_le_mul_of_nonneg_right hder.2 (norm_nonneg ((t:ℂ)*f t))
  simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs] at h1 h2 h3 h4 ⊢
  norm_num only [Complex.norm_ofNat]
  nlinarith

theorem gamma_shape_three_upper_image_pointwise (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    Tendsto (fun k => gammaShapeThreeComplexExpression (upperCutoffTest f k) t) atTop
      (𝓝 (gammaShapeThreeComplexExpression f t)) := by
  have hc := (steinCutoff_tendsto t).comp upper_cutoff_radius_tendsto
  have hd := (stein_cutoff_derivatives_tendsto t).1.comp upper_cutoff_radius_tendsto
  have hdd := (stein_cutoff_derivatives_tendsto t).2.comp upper_cutoff_radius_tendsto
  have h1 := (Complex.continuous_ofReal.continuousAt.tendsto.comp (hc.sub_const 1)).mul_const
    (gammaShapeThreeComplexExpression f t)
  have h2 := (Complex.continuous_ofReal.continuousAt.tendsto.comp hdd.neg).mul_const ((t:ℂ)*f t)
  have h3 := (Complex.continuous_ofReal.continuousAt.tendsto.comp hd.neg).mul_const ((3-(t:ℂ))*f t)
  have h4 := (Complex.continuous_ofReal.continuousAt.tendsto.comp (hd.const_mul (-2))).mul_const
    ((t:ℂ)*deriv f t)
  have he : Tendsto (fun k => gammaShapeThreeComplexExpression (upperCutoffTest f k) t-
      gammaShapeThreeComplexExpression f t) atTop (𝓝 0) := by
    simpa only [gamma_shape_three_upper_error_formula f hf, sub_self, neg_zero, mul_zero,
      Complex.ofReal_zero, zero_mul, add_zero, Function.comp_def,
      Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat] using ((h1.add h2).add h3).add h4
  simpa only [sub_add_cancel, zero_add] using he.add_const (gammaShapeThreeComplexExpression f t)

theorem gamma_shape_three_upper_vector_tendsto (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (y : GammaShapeThreeWeightedHilbert)
    (hy : (y : ℝ → ℂ) =ᵐ[gammaShapeThreeProbability] f)
    (hmem : Memℒp f 2 gammaShapeThreeProbability) :
    Tendsto (fun k => gammaShapeThreeCompactVector (upperCutoffTest f k)
      (upper_cutoff_test_smooth f hf k) (upper_cutoff_test_compact f k)) atTop (𝓝 y) := by
  apply gamma_shape_three_l2_dominated_limit _ y (upperCutoffTest f) f
    (fun k => gamma_shape_three_compact_vector_coe _ _ _) hy
    (fun k => (upper_cutoff_test_smooth f hf k).continuous) hf.continuous
    (fun t => ‖f t‖) hmem.norm
  · intro k
    apply Eventually.of_forall
    intro t
    change ‖(steinCutoff (upperCutoffRadius k) t:ℂ)*f t-f t‖ ≤ ‖f t‖
    rw [← sub_one_mul, norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    have hc : |steinCutoff (upperCutoffRadius k) t-1| ≤ 1 :=
      abs_le.mpr ⟨by linarith [(steinCutoff_bounds (upperCutoffRadius k) t).1],
        by linarith [(steinCutoff_bounds (upperCutoffRadius k) t).2]⟩
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _)
  · apply Eventually.of_forall
    intro t
    have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((steinCutoff_tendsto t).comp upper_cutoff_radius_tendsto)).mul_const (f t)
    simpa [upperCutoffTest] using h

theorem gamma_shape_three_upper_image_tendsto (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (y : GammaShapeThreeWeightedHilbert)
    (hy : (y : ℝ → ℂ) =ᵐ[gammaShapeThreeProbability] gammaShapeThreeComplexExpression f)
    (hD : Memℒp (gammaShapeThreeComplexExpression f) 2 gammaShapeThreeProbability)
    (htf : Memℒp (fun t : ℝ => (t:ℂ)*f t) 2 gammaShapeThreeProbability)
    (h3f : Memℒp (fun t : ℝ => (3-(t:ℂ))*f t) 2 gammaShapeThreeProbability)
    (htd : Memℒp (fun t : ℝ => (t:ℂ)*deriv f t) 2 gammaShapeThreeProbability) :
    Tendsto (fun k => gammaShapeThreeCompactImage (upperCutoffTest f k)
      (upper_cutoff_test_smooth f hf k) (upper_cutoff_test_compact f k)) atTop (𝓝 y) := by
  obtain ⟨C,hC,hb⟩ := stein_bump_derivatives_bounded
  apply gamma_shape_three_l2_dominated_limit _ y
    (fun k => gammaShapeThreeComplexExpression (upperCutoffTest f k)) (gammaShapeThreeComplexExpression f)
    (fun k => gamma_shape_three_compact_image_coe _ _ _) hy
    (fun k => (gamma_shape_three_expression_contDiff _ (upper_cutoff_test_smooth f hf k)).continuous)
    (gamma_shape_three_expression_contDiff f hf).continuous
    (fun t => ‖gammaShapeThreeComplexExpression f t‖+C*‖(t:ℂ)*f t‖+
      C*‖(3-(t:ℂ))*f t‖+(2*C)*‖(t:ℂ)*deriv f t‖)
    (((hD.norm.add (htf.norm.const_mul C)).add (h3f.norm.const_mul C)).add (htd.norm.const_mul (2*C)))
    (fun k => Eventually.of_forall (gamma_shape_three_upper_error_bound f hf C hC.le hb k))
    (Eventually.of_forall (gamma_shape_three_upper_image_pointwise f hf))

def gammaShapeThreeUpperVector (n k : ℕ) : GammaShapeThreeWeightedHilbert :=
  gammaShapeThreeCompactVector (upperCutoffTest (fun t => (gammaShapeThreeLaguerre n t : ℂ)) k)
    (upper_cutoff_test_smooth _ (gamma_shape_three_laguerre_complex_contDiff n) k)
    (upper_cutoff_test_compact _ k)

def gammaShapeThreeUpperImage (n k : ℕ) : GammaShapeThreeWeightedHilbert :=
  gammaShapeThreeCompactImage (upperCutoffTest (fun t => (gammaShapeThreeLaguerre n t : ℂ)) k)
    (upper_cutoff_test_smooth _ (gamma_shape_three_laguerre_complex_contDiff n) k)
    (upper_cutoff_test_compact _ k)

theorem gamma_shape_three_upper_laguerre_vector_tendsto (n : ℕ) :
    Tendsto (gammaShapeThreeUpperVector n) atTop (𝓝 (gammaShapeThreeL2Vector n)) :=
  gamma_shape_three_upper_vector_tendsto _ (gamma_shape_three_laguerre_complex_contDiff n) _
    (gamma_shape_three_complex_polynomial_mem_l2 (gammaShapeThreeLaguerrePolynomial n)).coeFn_toLp
    (gamma_shape_three_complex_polynomial_mem_l2 (gammaShapeThreeLaguerrePolynomial n))

theorem gamma_shape_three_upper_laguerre_image_tendsto (n : ℕ) :
    Tendsto (gammaShapeThreeUpperImage n) atTop (𝓝 ((n : ℂ) • gammaShapeThreeL2Vector n)) := by
  let f : ℝ → ℂ := fun t => (gammaShapeThreeLaguerre n t : ℂ)
  have hpoly : f = fun t : ℝ => Complex.ofReal ((gammaShapeThreeLaguerrePolynomial n).eval t) := rfl
  have hder : deriv f = fun t : ℝ =>
      Complex.ofReal ((gammaShapeThreeLaguerrePolynomial n).derivative.eval t) := by
    rw [hpoly]
    exact funext (complex_polynomial_eval_deriv _)
  have hD : Memℒp (gammaShapeThreeComplexExpression f) 2 gammaShapeThreeProbability := by
    have he : gammaShapeThreeComplexExpression f = fun t => (n : ℂ)*f t := by
      funext t
      exact gamma_shape_three_laguerre_complex_eigenvalue n t
    rw [he]
    exact (gamma_shape_three_complex_polynomial_mem_l2
      (gammaShapeThreeLaguerrePolynomial n)).const_mul (n : ℂ)
  have htf : Memℒp (fun t : ℝ => (t : ℂ)*f t) 2 gammaShapeThreeProbability := by
    rw [hpoly]
    have hp := gamma_shape_three_complex_polynomial_mem_l2
      (Polynomial.X*gammaShapeThreeLaguerrePolynomial n)
    have he : (fun t : ℝ => Complex.ofReal
        ((Polynomial.X*gammaShapeThreeLaguerrePolynomial n).eval t)) =
        fun t : ℝ => (t : ℂ)*Complex.ofReal ((gammaShapeThreeLaguerrePolynomial n).eval t) := by
      funext t
      simp only [Polynomial.eval_mul, Polynomial.eval_X, Complex.ofReal_mul]
    rw [he] at hp
    exact hp
  have h3f : Memℒp (fun t : ℝ => (3-(t : ℂ))*f t) 2 gammaShapeThreeProbability := by
    rw [hpoly]
    have hp := gamma_shape_three_complex_polynomial_mem_l2
      ((Polynomial.C 3-Polynomial.X)*gammaShapeThreeLaguerrePolynomial n)
    have he : (fun t : ℝ => Complex.ofReal
        (((Polynomial.C 3-Polynomial.X)*gammaShapeThreeLaguerrePolynomial n).eval t)) =
        fun t : ℝ => (3-(t : ℂ))*Complex.ofReal ((gammaShapeThreeLaguerrePolynomial n).eval t) := by
      funext t
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
        Polynomial.eval_X, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_ofNat]
    rw [he] at hp
    exact hp
  have htd : Memℒp (fun t : ℝ => (t : ℂ)*deriv f t) 2 gammaShapeThreeProbability := by
    rw [hder]
    have hp := gamma_shape_three_complex_polynomial_mem_l2
      (Polynomial.X*(gammaShapeThreeLaguerrePolynomial n).derivative)
    have he : (fun t : ℝ => Complex.ofReal
        ((Polynomial.X*(gammaShapeThreeLaguerrePolynomial n).derivative).eval t)) =
        fun t : ℝ => (t : ℂ)*Complex.ofReal
          ((gammaShapeThreeLaguerrePolynomial n).derivative.eval t) := by
      funext t
      simp only [Polynomial.eval_mul, Polynomial.eval_X, Complex.ofReal_mul]
    rw [he] at hp
    exact hp
  apply gamma_shape_three_upper_image_tendsto f
    (gamma_shape_three_laguerre_complex_contDiff n) _ _ hD htf h3f htd
  filter_upwards [Lp.coeFn_smul (n : ℂ) (gammaShapeThreeL2Vector n),
    (gamma_shape_three_complex_polynomial_mem_l2
      (gammaShapeThreeLaguerrePolynomial n)).coeFn_toLp] with t ht hf
  rw [gamma_shape_three_laguerre_complex_eigenvalue]
  simpa only [Pi.smul_apply, smul_eq_mul, gammaShapeThreeL2Vector] using
    ht.trans (congrArg ((n : ℂ)*·) hf)

theorem gamma_shape_three_upper_laguerre_graph_tendsto (n : ℕ) :
    Tendsto (fun k => (gammaShapeThreeUpperVector n k, gammaShapeThreeUpperImage n k)) atTop
      (𝓝 (gammaShapeThreeL2Vector n, (n : ℂ) • gammaShapeThreeL2Vector n)) :=
  (gamma_shape_three_upper_laguerre_vector_tendsto n).prod_mk_nhds
    (gamma_shape_three_upper_laguerre_image_tendsto n)

end
end Sigma
