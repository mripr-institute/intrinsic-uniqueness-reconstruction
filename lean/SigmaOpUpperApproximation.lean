import SigmaOpCutoffApproximation
import SigmaOpGraphCore

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff

theorem stein_cutoff_derivative (R t : ℝ) :
    deriv (steinCutoff R) t = deriv (steinBump : ℝ → ℝ) (t/R)/R := by
  simpa only [steinCutoff, Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using
    (((steinBump.contDiff : ContDiff ℝ ∞ (steinBump : ℝ → ℝ)).differentiable
    (by simp) (t/R)).hasDerivAt.comp t ((hasDerivAt_id t).div_const R)).deriv

theorem stein_cutoff_second_derivative (R t : ℝ) :
    deriv (deriv (steinCutoff R)) t = deriv (deriv (steinBump : ℝ → ℝ)) (t/R)/R^2 := by
  have hd : ContDiff ℝ ∞ (deriv (steinBump : ℝ → ℝ)) :=
    (contDiff_infty_iff_deriv.mp steinBump.contDiff).2
  have he : deriv (steinCutoff R) = fun u => deriv (steinBump : ℝ → ℝ) (u/R)/R :=
    funext (stein_cutoff_derivative R)
  rw [he]
  simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_mul, mul_inv_rev,
    pow_two, mul_assoc] using
    (((hd.differentiable (by simp) (t/R)).hasDerivAt.comp t
      ((hasDerivAt_id t).div_const R)).div_const R).deriv

theorem stein_bump_derivatives_bounded : ∃ C > 0, ∀ t : ℝ,
    |deriv (steinBump : ℝ → ℝ) t| ≤ C ∧
      |deriv (deriv (steinBump : ℝ → ℝ)) t| ≤ C := by
  have hd : ContDiff ℝ ∞ (deriv (steinBump : ℝ → ℝ)) :=
    (contDiff_infty_iff_deriv.mp steinBump.contDiff).2
  obtain ⟨B,hB⟩ := (steinBump.hasCompactSupport.deriv.abs.isCompact_range hd.continuous.abs).bddAbove
  obtain ⟨D,hD⟩ := (steinBump.hasCompactSupport.deriv.deriv.abs.isCompact_range
    (hd.continuous_deriv (by simp)).abs).bddAbove
  refine ⟨|B|+|D|+1, by positivity, ?_⟩
  intro t
  constructor
  · exact (hB (mem_range_self t)).trans (by linarith [le_abs_self B, abs_nonneg D])
  · exact (hD (mem_range_self t)).trans (by linarith [le_abs_self D, abs_nonneg B])

theorem stein_cutoff_derivatives_bound (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t : ℝ, |deriv (steinBump : ℝ → ℝ) t| ≤ C ∧
      |deriv (deriv (steinBump : ℝ → ℝ)) t| ≤ C)
    (R : ℝ) (hR : 1 ≤ R) (t : ℝ) :
    |deriv (steinCutoff R) t| ≤ C ∧ |deriv (deriv (steinCutoff R)) t| ≤ C := by
  have hr : 0 < R := by linarith
  rw [stein_cutoff_derivative, stein_cutoff_second_derivative,
    abs_div, abs_div, abs_of_pos hr, abs_of_pos (sq_pos_of_pos hr)]
  constructor
  · exact (div_le_iff₀ hr).mpr ((hb _).1.trans (le_mul_of_one_le_right hC hR))
  · exact (div_le_iff₀ (sq_pos_of_pos hr)).mpr
      ((hb _).2.trans (le_mul_of_one_le_right hC (by nlinarith)))

theorem stein_cutoff_derivatives_tendsto (t : ℝ) :
    Tendsto (fun R : ℝ => deriv (steinCutoff R) t) atTop (𝓝 0) ∧
      Tendsto (fun R : ℝ => deriv (deriv (steinCutoff R)) t) atTop (𝓝 0) := by
  have hd : ContDiff ℝ ∞ (deriv (steinBump : ℝ → ℝ)) :=
    (contDiff_infty_iff_deriv.mp steinBump.contDiff).2
  have ht : Tendsto (fun R : ℝ => t/R) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul t
  constructor
  · have h := (hd.continuous.continuousAt.tendsto.comp ht).mul tendsto_inv_atTop_zero
    simpa [stein_cutoff_derivative, div_eq_mul_inv] using h
  · have h := ((hd.continuous_deriv (by simp)).continuousAt.tendsto.comp ht).mul
      (tendsto_inv_atTop_zero.pow 2)
    simpa [stein_cutoff_second_derivative, div_eq_mul_inv, inv_pow] using h

theorem norm_four_sum_sq_le (a b c d : ℂ) :
    ‖a+b+c+d‖^2 ≤ 4*(‖a‖^2+‖b‖^2+‖c‖^2+‖d‖^2) := by
  have h := (norm_add_le (a+b+c) d).trans
    (add_le_add_right ((norm_add_le (a+b) c).trans (add_le_add_right (norm_add_le a b) _)) _)
  have hp : 0 ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by positivity
  have hh := pow_le_pow_left₀ (norm_nonneg (a+b+c+d)) h 2
  nlinarith [sq_nonneg (‖a‖-‖b‖), sq_nonneg (‖a‖-‖c‖), sq_nonneg (‖a‖-‖d‖),
    sq_nonneg (‖b‖-‖c‖), sq_nonneg (‖b‖-‖d‖), sq_nonneg (‖c‖-‖d‖)]

/-- A dominated-convergence bridge for genuine weighted L2 vectors, with
representatives specified only almost everywhere. -/
theorem laguerre_l2_dominated_limit (x : ℕ → LaguerreWeightedHilbert)
    (y : LaguerreWeightedHilbert) (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ)
    (hx : ∀ k, (x k : ℝ → ℂ) =ᵐ[gammaProbability] F k)
    (hy : (y : ℝ → ℂ) =ᵐ[gammaProbability] f)
    (hF : ∀ k, Continuous (F k)) (hf : Continuous f)
    (g : ℝ → ℝ) (hg : Memℒp g 2 gammaProbability)
    (hbound : ∀ k t, ‖F k t-f t‖ ≤ g t)
    (hlim : ∀ᵐ t ∂gammaProbability, Tendsto (fun k => F k t) atTop (𝓝 (f t))) :
    Tendsto x atTop (𝓝 y) := by
  apply laguerre_l2_tendsto_of_sq_error
  have hi : Integrable (fun t => g t^2) gammaProbability :=
    (memℒp_two_iff_integrable_sq hg.1).mp hg
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := gammaProbability) (l := (atTop : Filter ℕ))
    (F := fun k t => ‖F k t-f t‖^2) (f := fun _ => (0 : ℝ))
    (fun t => g t^2) ?_ ?_ hi ?_
  · have he (k : ℕ) : ‖x k-y‖^2 = ∫ t, ‖F k t-f t‖^2 ∂gammaProbability := by
      apply laguerre_l2_norm_sq_of_ae
      filter_upwards [Lp.coeFn_sub (x k) y, hx k, hy] with t ht hxt hyt
      simpa only [Pi.sub_apply, hxt, hyt] using ht
    simpa only [he, integral_zero] using h
  · exact Eventually.of_forall fun k =>
      (((hF k).sub hf).norm.pow 2).aestronglyMeasurable
  · exact Eventually.of_forall fun k => Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound k t) 2
  · filter_upwards [hlim] with t ht
    simpa using ((ht.sub_const (f t)).norm.pow 2)

def upperCutoffRadius (k : ℕ) : ℝ := k+1

theorem upper_cutoff_radius_pos (k : ℕ) : 0 < upperCutoffRadius k := by
  unfold upperCutoffRadius
  positivity

theorem upper_cutoff_radius_one_le (k : ℕ) : 1 ≤ upperCutoffRadius k := by
  unfold upperCutoffRadius
  exact le_add_of_nonneg_left (Nat.cast_nonneg k)

theorem upper_cutoff_radius_tendsto : Tendsto upperCutoffRadius atTop atTop := by
  exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

def upperCutoffTest (f : ℝ → ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  (steinCutoff (upperCutoffRadius k) t : ℂ) * f t

theorem upper_cutoff_test_smooth (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (upperCutoffTest f k) :=
  (Complex.ofRealCLM.contDiff.comp (steinCutoff_contDiff _)).mul hf

theorem upper_cutoff_test_compact (f : ℝ → ℂ) (k : ℕ) :
    HasCompactSupport (upperCutoffTest f k) := by
  have h := steinCutoff_hasCompactSupport (upper_cutoff_radius_pos k)
  have hc : HasCompactSupport (fun t => (steinCutoff (upperCutoffRadius k) t : ℂ)) :=
    h.comp_left Complex.ofReal_zero
  exact hc.mul_right

theorem upper_cutoff_error_formula (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (k : ℕ) (t : ℝ) :
    opComplexLaguerreExpression (upperCutoffTest f k) t-opComplexLaguerreExpression f t =
      ((steinCutoff (upperCutoffRadius k) t-1 : ℝ) : ℂ)*opComplexLaguerreExpression f t +
      (-deriv (deriv (steinCutoff (upperCutoffRadius k))) t : ℂ)*((t : ℂ)*f t) +
      (-deriv (steinCutoff (upperCutoffRadius k)) t : ℂ)*((2-(t : ℂ))*f t) +
      (-2*deriv (steinCutoff (upperCutoffRadius k)) t : ℂ)*((t : ℂ)*deriv f t) := by
  unfold upperCutoffTest
  rw [op_complex_laguerre_product (fun u : ℝ => (steinCutoff (upperCutoffRadius k) u : ℂ)) f
    (Complex.ofRealCLM.contDiff.comp (steinCutoff_contDiff _)) hf,
    op_complex_laguerre_ofReal _ (steinCutoff_contDiff _)]
  have hd : deriv (fun u : ℝ => (steinCutoff (upperCutoffRadius k) u : ℂ)) t =
      Complex.ofReal (deriv (steinCutoff (upperCutoffRadius k)) t) :=
    (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      (((steinCutoff_contDiff _).differentiable (by simp) t).hasDerivAt)).deriv
  rw [hd]
  push_cast
  ring

theorem upper_cutoff_error_bound (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t : ℝ, |deriv (steinBump : ℝ → ℝ) t| ≤ C ∧
      |deriv (deriv (steinBump : ℝ → ℝ)) t| ≤ C) (k : ℕ) (t : ℝ) :
    ‖opComplexLaguerreExpression (upperCutoffTest f k) t-opComplexLaguerreExpression f t‖ ≤
      ‖opComplexLaguerreExpression f t‖+C*‖(t:ℂ)*f t‖+
        C*‖(2-(t:ℂ))*f t‖+(2*C)*‖(t:ℂ)*deriv f t‖ := by
  rw [upper_cutoff_error_formula f hf k t]
  have hder := stein_cutoff_derivatives_bound C hC hb _ (upper_cutoff_radius_one_le k) t
  have hc : |steinCutoff (upperCutoffRadius k) t-1| ≤ 1 :=
    abs_le.mpr ⟨by linarith [(steinCutoff_bounds (upperCutoffRadius k) t).1],
      by linarith [(steinCutoff_bounds (upperCutoffRadius k) t).2]⟩
  apply (norm_add_le _ _).trans
  apply (add_le_add_right ((norm_add_le _ _).trans
    (add_le_add_right (norm_add_le _ _) _)) _).trans
  have h1 := mul_le_mul_of_nonneg_right hc (norm_nonneg (opComplexLaguerreExpression f t))
  have h2 := mul_le_mul_of_nonneg_right hder.1 (norm_nonneg ((2-(t:ℂ))*f t))
  have h3 := mul_le_mul_of_nonneg_right hder.1 (norm_nonneg ((t:ℂ)*deriv f t))
  have h4 := mul_le_mul_of_nonneg_right hder.2 (norm_nonneg ((t:ℂ)*f t))
  simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs] at h1 h2 h3 h4 ⊢
  norm_num only [Complex.norm_ofNat]
  nlinarith

theorem upper_cutoff_image_pointwise (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    Tendsto (fun k => opComplexLaguerreExpression (upperCutoffTest f k) t) atTop
      (𝓝 (opComplexLaguerreExpression f t)) := by
  have hc := (steinCutoff_tendsto t).comp upper_cutoff_radius_tendsto
  have hd := (stein_cutoff_derivatives_tendsto t).1.comp upper_cutoff_radius_tendsto
  have hdd := (stein_cutoff_derivatives_tendsto t).2.comp upper_cutoff_radius_tendsto
  have h1 := (Complex.continuous_ofReal.continuousAt.tendsto.comp (hc.sub_const 1)).mul_const
    (opComplexLaguerreExpression f t)
  have h2 := (Complex.continuous_ofReal.continuousAt.tendsto.comp hdd.neg).mul_const ((t:ℂ)*f t)
  have h3 := (Complex.continuous_ofReal.continuousAt.tendsto.comp hd.neg).mul_const ((2-(t:ℂ))*f t)
  have h4 := (Complex.continuous_ofReal.continuousAt.tendsto.comp (hd.const_mul (-2))).mul_const
    ((t:ℂ)*deriv f t)
  have he : Tendsto (fun k => opComplexLaguerreExpression (upperCutoffTest f k) t-
      opComplexLaguerreExpression f t) atTop (𝓝 0) := by
    simpa only [upper_cutoff_error_formula f hf, sub_self, neg_zero, mul_zero,
      Complex.ofReal_zero, zero_mul, add_zero, Function.comp_def,
      Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat] using ((h1.add h2).add h3).add h4
  simpa only [sub_add_cancel, zero_add] using he.add_const (opComplexLaguerreExpression f t)

theorem upper_cutoff_vector_convergence (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (y : LaguerreWeightedHilbert) (hy : (y : ℝ → ℂ) =ᵐ[gammaProbability] f)
    (hmem : Memℒp f 2 gammaProbability) :
    Tendsto (fun k => smoothCompactL2Vector (upperCutoffTest f k)
      (upper_cutoff_test_smooth f hf k) (upper_cutoff_test_compact f k)) atTop (𝓝 y) := by
  apply laguerre_l2_dominated_limit _ y (upperCutoffTest f) f
    (fun k => smooth_compact_l2_coe _ _ _) hy
    (fun k => (upper_cutoff_test_smooth f hf k).continuous) hf.continuous
    (fun t => ‖f t‖) hmem.norm
  · intro k t
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

theorem upper_cutoff_image_convergence (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (y : LaguerreWeightedHilbert)
    (hy : (y : ℝ → ℂ) =ᵐ[gammaProbability] opComplexLaguerreExpression f)
    (hD : Memℒp (opComplexLaguerreExpression f) 2 gammaProbability)
    (htf : Memℒp (fun t : ℝ => (t:ℂ)*f t) 2 gammaProbability)
    (h2f : Memℒp (fun t : ℝ => (2-(t:ℂ))*f t) 2 gammaProbability)
    (htd : Memℒp (fun t : ℝ => (t:ℂ)*deriv f t) 2 gammaProbability) :
    Tendsto (fun k => smoothCompactL2Image (upperCutoffTest f k)
      (upper_cutoff_test_smooth f hf k) (upper_cutoff_test_compact f k)) atTop (𝓝 y) := by
  obtain ⟨C,hC,hb⟩ := stein_bump_derivatives_bounded
  apply laguerre_l2_dominated_limit _ y
    (fun k => opComplexLaguerreExpression (upperCutoffTest f k)) (opComplexLaguerreExpression f)
    (fun k => smooth_compact_image_coe _ _ _) hy
    (fun k => (op_complex_laguerre_expression_contDiff _ (upper_cutoff_test_smooth f hf k)).continuous)
    (op_complex_laguerre_expression_contDiff f hf).continuous
    (fun t => ‖opComplexLaguerreExpression f t‖+C*‖(t:ℂ)*f t‖+
      C*‖(2-(t:ℂ))*f t‖+(2*C)*‖(t:ℂ)*deriv f t‖)
    (((hD.norm.add (htf.norm.const_mul C)).add (h2f.norm.const_mul C)).add (htd.norm.const_mul (2*C)))
    (upper_cutoff_error_bound f hf C hC.le hb)
    (Eventually.of_forall (upper_cutoff_image_pointwise f hf))

theorem complex_polynomial_eval_deriv (P : Polynomial ℝ) (t : ℝ) :
    deriv (fun u : ℝ => Complex.ofReal (P.eval u)) t = Complex.ofReal (P.derivative.eval t) :=
  (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (P.hasDerivAt t)).deriv

def upperLaguerreVector (n k : ℕ) : LaguerreWeightedHilbert :=
  smoothCompactL2Vector (upperCutoffTest (fun t => (opLaguerre n t:ℂ)) k)
    (upper_cutoff_test_smooth _ (op_laguerre_complex_contDiff n) k)
    (upper_cutoff_test_compact _ k)

def upperLaguerreImage (n k : ℕ) : LaguerreWeightedHilbert :=
  smoothCompactL2Image (upperCutoffTest (fun t => (opLaguerre n t:ℂ)) k)
    (upper_cutoff_test_smooth _ (op_laguerre_complex_contDiff n) k)
    (upper_cutoff_test_compact _ k)

theorem upper_laguerre_vector_tendsto (n : ℕ) :
    Tendsto (upperLaguerreVector n) atTop (𝓝 (laguerreL2Vector n)) :=
  upper_cutoff_vector_convergence _ (op_laguerre_complex_contDiff n) _
    (op_laguerre_complex_mem_l2 n).coeFn_toLp (op_laguerre_complex_mem_l2 n)

theorem upper_laguerre_image_tendsto (n : ℕ) :
    Tendsto (upperLaguerreImage n) atTop (𝓝 ((n:ℂ) • laguerreL2Vector n)) := by
  let f : ℝ → ℂ := fun t => (opLaguerre n t:ℂ)
  have hpoly : f = fun t : ℝ => Complex.ofReal ((opLaguerrePolynomial n).eval t) := by
    funext t
    exact congrArg Complex.ofReal (op_laguerre_polynomial_eval n t).symm
  have hder : deriv f = fun t : ℝ => Complex.ofReal ((opLaguerrePolynomial n).derivative.eval t) := by
    rw [hpoly]
    exact funext (complex_polynomial_eval_deriv _)
  have hD : Memℒp (opComplexLaguerreExpression f) 2 gammaProbability := by
    have he : opComplexLaguerreExpression f = fun t => (n:ℂ)*f t := by
      funext t
      exact op_laguerre_native_complex_eigenvalue n t
    rw [he]
    exact (op_laguerre_complex_mem_l2 n).const_mul (n:ℂ)
  have htf : Memℒp (fun t : ℝ => (t:ℂ)*f t) 2 gammaProbability := by
    rw [hpoly]
    have hp := gamma_complex_polynomial_mem_l2 (Polynomial.X*opLaguerrePolynomial n)
    have he : (fun t : ℝ => Complex.ofReal ((Polynomial.X*opLaguerrePolynomial n).eval t)) =
        (fun t : ℝ => (t:ℂ)*Complex.ofReal ((opLaguerrePolynomial n).eval t)) := by
      funext t
      simp only [Polynomial.eval_mul, Polynomial.eval_X, Complex.ofReal_mul]
    rw [he] at hp
    exact hp
  have h2f : Memℒp (fun t : ℝ => (2-(t:ℂ))*f t) 2 gammaProbability := by
    rw [hpoly]
    have hp := gamma_complex_polynomial_mem_l2 ((Polynomial.C 2-Polynomial.X)*opLaguerrePolynomial n)
    have he : (fun t : ℝ => Complex.ofReal (((Polynomial.C 2-Polynomial.X)*opLaguerrePolynomial n).eval t)) =
        (fun t : ℝ => (2-(t:ℂ))*Complex.ofReal ((opLaguerrePolynomial n).eval t)) := by
      funext t
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
        Polynomial.eval_X, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_ofNat]
    rw [he] at hp
    exact hp
  have htd : Memℒp (fun t : ℝ => (t:ℂ)*deriv f t) 2 gammaProbability := by
    rw [hder]
    have hp := gamma_complex_polynomial_mem_l2 (Polynomial.X*(opLaguerrePolynomial n).derivative)
    have he : (fun t : ℝ => Complex.ofReal ((Polynomial.X*(opLaguerrePolynomial n).derivative).eval t)) =
        (fun t : ℝ => (t:ℂ)*Complex.ofReal ((opLaguerrePolynomial n).derivative.eval t)) := by
      funext t
      simp only [Polynomial.eval_mul, Polynomial.eval_X, Complex.ofReal_mul]
    rw [he] at hp
    exact hp
  apply upper_cutoff_image_convergence f (op_laguerre_complex_contDiff n) _ _ hD htf h2f htd
  filter_upwards [Lp.coeFn_smul (n:ℂ) (laguerreL2Vector n),
    (op_laguerre_complex_mem_l2 n).coeFn_toLp] with t ht hf
  rw [op_laguerre_native_complex_eigenvalue]
  simpa only [Pi.smul_apply, smul_eq_mul, laguerreL2Vector] using ht.trans (congrArg ((n:ℂ)*·) hf)

theorem upper_laguerre_graph_tendsto (n : ℕ) :
    Tendsto (fun k => (upperLaguerreVector n k, upperLaguerreImage n k)) atTop
      (𝓝 (laguerreL2Vector n, (n:ℂ) • laguerreL2Vector n)) :=
  (upper_laguerre_vector_tendsto n).prod_mk_nhds (upper_laguerre_image_tendsto n)

end
end Sigma
