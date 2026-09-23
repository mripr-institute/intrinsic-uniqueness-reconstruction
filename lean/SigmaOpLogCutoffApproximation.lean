import SigmaOpCutoffApproximation
import SigmaOpMinimalOperator
import SigmaOpMixing

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal NNReal

def operatorLogCutoffTest (k : ℕ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (operatorLogCutoff (k+1 : ℝ) t : ℂ)*f t

theorem operator_log_cutoff_test_smooth (k : ℕ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (operatorLogCutoffTest k f) :=
  (Complex.ofRealCLM.contDiff.comp (operator_log_cutoff_contDiff (by positivity))).mul hf

theorem operator_log_cutoff_test_compact (k : ℕ) (f : ℝ → ℂ)
    (hs : HasCompactSupport f) : HasCompactSupport (operatorLogCutoffTest k f) := hs.mul_left

theorem operator_log_cutoff_test_positive_support (k : ℕ) (f : ℝ → ℂ) :
    tsupport (operatorLogCutoffTest k f) ⊆ Ioi 0 := by
  have hh : Function.support (operatorLogCutoffTest k f) ⊆
      Ici (Real.exp (-2*(k+1 : ℝ))) := by
    intro t ht
    by_contra hn
    have hz := operator_log_cutoff_zero (by positivity : 0 < (k+1 : ℝ)) (le_of_not_ge hn)
    exact ht (by simp [operatorLogCutoffTest, hz])
  exact (closure_minimal hh isClosed_Ici).trans
    (fun t ht => (Real.exp_pos _).trans_le ht)

theorem operator_log_cutoff_deriv_compact {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (deriv (operatorLogCutoff R)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc (Real.exp (-2*R)) (Real.exp (-R))))
  intro t ht
  by_contra hm
  have he : ∃ c : ℝ, operatorLogCutoff R =ᶠ[𝓝 t] (fun _ => c) := by
    rcases not_and_or.mp hm with hn | hn
    · refine ⟨0, ?_⟩
      filter_upwards [eventually_lt_nhds (lt_of_not_ge hn)] with u hu
      exact operator_log_cutoff_zero hR hu.le
    · refine ⟨1, ?_⟩
      filter_upwards [eventually_gt_nhds (lt_of_not_ge hn)] with u hu
      exact operator_log_cutoff_one hR hu.le
  obtain ⟨c, hc⟩ := he
  exact ht (hc.deriv_eq.trans (deriv_const _ _))

set_option maxHeartbeats 800000 in
theorem operator_log_cutoff_expression_compact {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (opComplexLaguerreExpression (fun t => (operatorLogCutoff R t : ℂ))) := by
  have hh := operator_log_cutoff_deriv_compact hR
  have he : opComplexLaguerreExpression (fun t => (operatorLogCutoff R t : ℂ)) =
      fun t => ((-t*deriv (deriv (operatorLogCutoff R)) t -
        (2-t)*deriv (operatorLogCutoff R) t : ℝ) : ℂ) := by
    funext t
    exact op_complex_laguerre_ofReal _ (operator_log_cutoff_contDiff hR) t
  rw [he]
  have hc : HasCompactSupport (fun t : ℝ => -t*deriv (deriv (operatorLogCutoff R)) t -
      (2-t)*deriv (operatorLogCutoff R) t) := by
    simp only [sub_eq_add_neg]
    exact hh.deriv.mul_left.add hh.mul_left.neg'
  exact hc.comp_left (g := Complex.ofReal) (by simp)

theorem operator_log_cutoff_expression_sq_integral {R : ℝ} (hR : 0 < R) :
    (∫ t, ‖opComplexLaguerreExpression (fun u => (operatorLogCutoff R u : ℂ)) t‖^2
      ∂gammaProbability) = ∫ t : ℝ in Ioi 0, operatorLogCutoffGraphError R t := by
  rw [gamma_probability_integral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [op_complex_laguerre_ofReal _ (operator_log_cutoff_contDiff hR)]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, operatorLogCutoffGraphError,
    SigmaPresentations.density]
  ring

theorem operator_log_cutoff_test_vector_tendsto (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    Tendsto (fun k : ℕ => smoothCompactL2Vector (operatorLogCutoffTest k f)
      (operator_log_cutoff_test_smooth k f hf) (operator_log_cutoff_test_compact k f hs))
      atTop (𝓝 (smoothCompactL2Vector f hf hs)) := by
  apply laguerre_l2_tendsto_of_sq_error
  have hmem : Memℒp f 2 gammaProbability := hf.continuous.memℒp_of_hasCompactSupport hs
  have h := laguerre_bounded_cutoff_error_tendsto f hmem
    (fun k t => operatorLogCutoff (k+1 : ℝ) t)
    (fun k => (operator_log_cutoff_contDiff (by positivity : 0 < (k+1 : ℝ))).continuous)
    (fun k t => operator_log_cutoff_bounds _ _) ?_
  · convert h using 1
    funext k
    apply laguerre_l2_norm_sq_of_ae
    filter_upwards [Lp.coeFn_sub
      (smoothCompactL2Vector (operatorLogCutoffTest k f)
        (operator_log_cutoff_test_smooth k f hf) (operator_log_cutoff_test_compact k f hs))
      (smoothCompactL2Vector f hf hs),
      smooth_compact_l2_coe (operatorLogCutoffTest k f)
        (operator_log_cutoff_test_smooth k f hf) (operator_log_cutoff_test_compact k f hs),
      smooth_compact_l2_coe f hf hs] with t hsub hx hy
    simp only [Pi.sub_apply, hx, hy] at hsub
    rw [hsub]
    simp only [operatorLogCutoffTest, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  · filter_upwards [operator_integer_samples_ae_pos gammaProbability
      operator_gamma_probability_integer_samples] with t ht
    exact (operator_log_cutoff_tendsto ht).comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

private theorem norm_add_sub_sq_le (a b c : ℂ) :
    ‖a+b-c‖^2 ≤ 3*(‖a‖^2+‖b‖^2+‖c‖^2) := by
  have hn : ‖a+b-c‖ ≤ ‖a‖+‖b‖+‖c‖ :=
    (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
  have hsq := mul_self_le_mul_self (norm_nonneg _) hn
  nlinarith [sq_nonneg (‖a‖-‖b‖), sq_nonneg (‖a‖-‖c‖), sq_nonneg (‖b‖-‖c‖)]

theorem operator_log_cutoff_product_error_bound (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    {R t C M : ℝ} (hR : 0 < R) (ht : 0 < t) (hC0 : 0 ≤ C)
    (hC : ∀ u : ℝ, |deriv Real.smoothTransition u| ≤ C)
    (hfM : ‖f t‖ ≤ M) (hdM : ‖deriv f t‖ ≤ M) :
    ‖opComplexLaguerreExpression (fun u => (operatorLogCutoff R u : ℂ)*f u) t -
        opComplexLaguerreExpression f t‖^2 ≤
      3*(‖((operatorLogCutoff R t-1 : ℝ) : ℂ)*opComplexLaguerreExpression f t‖^2 +
        M^2*‖opComplexLaguerreExpression (fun u => (operatorLogCutoff R u : ℂ)) t‖^2 +
        (2*C*M/R)^2) := by
  let c : ℝ → ℂ := fun u => (operatorLogCutoff R u : ℂ)
  have hc : ContDiff ℝ ∞ c := Complex.ofRealCLM.contDiff.comp (operator_log_cutoff_contDiff hR)
  have hdc : deriv c t = Complex.ofReal (deriv (operatorLogCutoff R) t) :=
    (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      ((operator_log_cutoff_contDiff hR).differentiable (by simp) t).hasDerivAt).deriv
  have hid : opComplexLaguerreExpression (fun u => c u*f u) t - opComplexLaguerreExpression f t =
      ((operatorLogCutoff R t-1 : ℝ) : ℂ)*opComplexLaguerreExpression f t +
        f t*opComplexLaguerreExpression c t - 2*(t : ℂ)*deriv c t*deriv f t := by
    rw [op_complex_laguerre_product c f hc hf]
    dsimp only [c]
    push_cast
    ring
  rw [hid]
  apply (norm_add_sub_sq_le _ _ _).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
  apply add_le_add
  · apply add_le_add_left
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hfM 2) (sq_nonneg _)
  · apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    rw [norm_mul, norm_mul, norm_mul, hdc, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht, Complex.norm_real, Real.norm_eq_abs]
    have hb := operator_log_cutoff_deriv_bound hR ht hC
    calc
      2*t*|deriv (operatorLogCutoff R) t| * ‖deriv f t‖ ≤ 2*t*(C/(R*t))*M := by
        gcongr
      _ = 2*C*M/R := by field_simp; ring

theorem smooth_compact_function_derivative_bounded (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    ∃ M > 0, (∀ t, ‖f t‖ ≤ M) ∧ (∀ t, ‖deriv f t‖ ≤ M) := by
  obtain ⟨B, hB⟩ := (hs.norm.isCompact_range hf.continuous.norm).bddAbove
  obtain ⟨D, hD⟩ := (hs.deriv.norm.isCompact_range
    (hf.continuous_deriv (by simp)).norm).bddAbove
  refine ⟨|B|+|D|+1, by positivity, ?_, ?_⟩
  · intro t
    exact (hB (mem_range_self t)).trans (by linarith [le_abs_self B, abs_nonneg D])
  · intro t
    exact (hD (mem_range_self t)).trans (by linarith [le_abs_self D, abs_nonneg B])

private theorem compact_sq_integrable (f : ℝ → ℂ) (hf : Continuous f)
    (hs : HasCompactSupport f) : Integrable (fun t => ‖f t‖^2) gammaProbability :=
  (memℒp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp
    (hf.memℒp_of_hasCompactSupport hs)

theorem operator_log_cutoff_product_integral_bound (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) {R C M : ℝ} (hR : 0 < R) (hC0 : 0 ≤ C)
    (hC : ∀ u : ℝ, |deriv Real.smoothTransition u| ≤ C)
    (hfM : ∀ t, ‖f t‖ ≤ M) (hdM : ∀ t, ‖deriv f t‖ ≤ M) :
    (∫ t, ‖opComplexLaguerreExpression (fun u => (operatorLogCutoff R u : ℂ)*f u) t -
        opComplexLaguerreExpression f t‖^2 ∂gammaProbability) ≤
      3*((∫ t, ‖((operatorLogCutoff R t-1 : ℝ) : ℂ)*opComplexLaguerreExpression f t‖^2
        ∂gammaProbability) + M^2*(∫ t : ℝ in Ioi 0, operatorLogCutoffGraphError R t) +
        (2*C*M/R)^2) := by
  let c : ℝ → ℂ := fun t => (operatorLogCutoff R t : ℂ)
  have hc : ContDiff ℝ ∞ c := Complex.ofRealCLM.contDiff.comp (operator_log_cutoff_contDiff hR)
  have hdf := op_complex_laguerre_expression_contDiff f hf
  have hds := op_complex_laguerre_expression_compact f hs
  have hA : Integrable (fun t => ‖((operatorLogCutoff R t-1 : ℝ) : ℂ)*
      opComplexLaguerreExpression f t‖^2) gammaProbability := by
    apply compact_sq_integrable
    · exact (Complex.continuous_ofReal.comp
        ((operator_log_cutoff_contDiff hR).continuous.sub continuous_const)).mul hdf.continuous
    · exact hds.mul_left
  have hB : Integrable (fun t => ‖opComplexLaguerreExpression c t‖^2) gammaProbability :=
    compact_sq_integrable _ (op_complex_laguerre_expression_contDiff c hc).continuous
      (operator_log_cutoff_expression_compact hR)
  have hE : Integrable (fun t => ‖opComplexLaguerreExpression (fun u => c u*f u) t -
      opComplexLaguerreExpression f t‖^2) gammaProbability := by
    apply compact_sq_integrable
    · exact (op_complex_laguerre_expression_contDiff _ (hc.mul hf)).continuous.sub hdf.continuous
    · simp only [sub_eq_add_neg]
      exact (op_complex_laguerre_expression_compact _ hs.mul_left).add hds.neg'
  have hmaj := integral_mono_ae hE (((hA.add (hB.const_mul (M^2))).add
      (integrable_const ((2*C*M/R)^2))).const_mul 3) ?_
  · simp only [Pi.add_apply] at hmaj
    have hi₁ := integral_add hA (hB.const_mul (M^2))
    have hi₂ := integral_add (hA.add (hB.const_mul (M^2))) (integrable_const ((2*C*M/R)^2))
    dsimp only [Pi.add_apply] at hi₁ hi₂
    rw [integral_mul_left, hi₂, hi₁, integral_mul_left] at hmaj
    dsimp only [c] at hmaj
    rw [operator_log_cutoff_expression_sq_integral hR] at hmaj
    simpa using hmaj
  · filter_upwards [operator_integer_samples_ae_pos gammaProbability
      operator_gamma_probability_integer_samples] with t ht
    exact operator_log_cutoff_product_error_bound f hf hR ht hC0 hC (hfM t) (hdM t)

theorem operator_log_cutoff_product_sq_error_tendsto (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    Tendsto (fun k : ℕ => ∫ t,
      ‖opComplexLaguerreExpression (operatorLogCutoffTest k f) t -
        opComplexLaguerreExpression f t‖^2 ∂gammaProbability) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC, hC₂⟩ := smooth_transition_derivatives_bounded
  obtain ⟨M, hM0, hfM, hdM⟩ := smooth_compact_function_derivative_bounded f hf hs
  have hR : Tendsto (fun k : ℕ => (k+1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hA := laguerre_bounded_cutoff_error_tendsto (opComplexLaguerreExpression f)
    ((op_complex_laguerre_expression_contDiff f hf).continuous.memℒp_of_hasCompactSupport
      (op_complex_laguerre_expression_compact f hs))
    (fun k t => operatorLogCutoff (k+1 : ℝ) t)
    (fun k => (operator_log_cutoff_contDiff (by positivity : 0 < (k+1 : ℝ))).continuous)
    (fun k t => operator_log_cutoff_bounds _ _) ?_
  · have hB := (operator_log_cutoff_graph_error_tendsto.comp hR).const_mul (M^2)
    have hCterm : Tendsto (fun k : ℕ => (2*C*M/(k+1 : ℝ))^2) atTop (𝓝 0) := by
      have hh := ((tendsto_inv_atTop_zero.comp hR).const_mul (2*C*M)).pow 2
      simpa only [Function.comp_def, div_eq_mul_inv, mul_zero, zero_pow (by decide : 2 ≠ 0)] using hh
    have hb := ((hA.add hB).add hCterm).const_mul 3
    simp only [mul_zero, add_zero] at hb
    apply squeeze_zero (fun k : ℕ => integral_nonneg (fun t => sq_nonneg _))
      (fun k : ℕ => operator_log_cutoff_product_integral_bound f hf hs
        (by positivity : 0 < (k+1 : ℝ)) hC0.le hC hfM hdM) hb
  · filter_upwards [operator_integer_samples_ae_pos gammaProbability
      operator_gamma_probability_integer_samples] with t ht
    exact (operator_log_cutoff_tendsto ht).comp hR

theorem operator_log_cutoff_test_image_tendsto (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    Tendsto (fun k : ℕ => smoothCompactL2Image (operatorLogCutoffTest k f)
      (operator_log_cutoff_test_smooth k f hf) (operator_log_cutoff_test_compact k f hs))
      atTop (𝓝 (smoothCompactL2Image f hf hs)) := by
  apply laguerre_l2_tendsto_of_sq_error
  convert operator_log_cutoff_product_sq_error_tendsto f hf hs using 1
  funext k
  apply laguerre_l2_norm_sq_of_ae
  filter_upwards [Lp.coeFn_sub
    (smoothCompactL2Image (operatorLogCutoffTest k f)
      (operator_log_cutoff_test_smooth k f hf) (operator_log_cutoff_test_compact k f hs))
    (smoothCompactL2Image f hf hs),
    smooth_compact_image_coe (operatorLogCutoffTest k f)
      (operator_log_cutoff_test_smooth k f hf) (operator_log_cutoff_test_compact k f hs),
    smooth_compact_image_coe f hf hs] with t hsub hx hy
  simpa only [Pi.sub_apply, hx, hy] using hsub

/-- Every globally smooth compactly supported function, including one nonzero
at the singular endpoint, lies in the actual compact-interior graph closure.
Both components are limits of the literal differential graph, not merely of
spectral coefficients. -/
theorem smooth_compact_pair_mem_minimal_graph_closure (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    (smoothCompactL2Vector f hf hs, smoothCompactL2Image f hf hs) ∈
      laguerreMinimalOperator.graph.topologicalClosure := by
  have hx := operator_log_cutoff_test_vector_tendsto f hf hs
  have hy := operator_log_cutoff_test_image_tendsto f hf hs
  change (smoothCompactL2Vector f hf hs, smoothCompactL2Image f hf hs) ∈
    closure (laguerreMinimalOperator.graph : Set (LaguerreWeightedHilbert × LaguerreWeightedHilbert))
  apply mem_closure_of_tendsto (hx.prod_mk_nhds hy)
  apply Eventually.of_forall
  intro k
  have h := laguerreMinimalOperator.mem_graph
    ⟨smoothCompactL2Vector (operatorLogCutoffTest k f)
      (operator_log_cutoff_test_smooth k f hf) (operator_log_cutoff_test_compact k f hs),
      laguerre_compact_test_mem _ _ _ (operator_log_cutoff_test_positive_support k f)⟩
  rwa [laguerre_minimal_test_action _ _ _ (operator_log_cutoff_test_positive_support k f)] at h

end
end Sigma
