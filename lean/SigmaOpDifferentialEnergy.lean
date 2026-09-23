import SigmaOpMinimalOperator
import SigmaOpLaguerreDomains

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal NNReal

theorem complex_conjugate_deriv (f : ℝ → ℂ) (hf : Differentiable ℝ f) (t : ℝ) :
    deriv (fun x => starRingEnd ℂ (f x)) t = starRingEnd ℂ (deriv f t) := by
  exact (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hf t).hasDerivAt).deriv

/-- Integration by parts against the conjugate, with the actual differential
expression and the actual Gamma probability measure. -/
theorem op_complex_laguerre_green_energy_gamma (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    (∫ t, starRingEnd ℂ (f t)*opComplexLaguerreExpression f t ∂gammaProbability) =
      ∫ t, (t:ℂ)*deriv f t*starRingEnd ℂ (deriv f t) ∂gammaProbability := by
  have hd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hc : ContDiff ℝ ∞ (fun t => starRingEnd ℂ (f t)) :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.comp hf
  let w := fun t => deriv f t*starRingEnd ℂ (f t)
  have hw : ContDiff ℝ ∞ w := hd.mul hc
  have hws : HasCompactSupport w := hs.deriv.mul_right
  have h := gamma_complex_stein w hw hws
  have he : (fun t : ℝ => (t:ℂ)*deriv w t+(2-(t:ℂ))*w t) =
      fun t : ℝ => (t:ℂ)*deriv f t*starRingEnd ℂ (deriv f t)-
        starRingEnd ℂ (f t)*opComplexLaguerreExpression f t := by
    funext t
    dsimp only [w]
    rw [deriv_mul (hd.differentiable (by simp) t) (hc.differentiable (by simp) t),
      complex_conjugate_deriv f (hf.differentiable (by simp))]
    simp only [opComplexLaguerreExpression]
    ring
  have hi : Integrable (fun t : ℝ => (t:ℂ)*deriv f t*starRingEnd ℂ (deriv f t)) gammaProbability :=
    ((Complex.continuous_ofReal.mul hd.continuous).mul
      (Complex.continuous_conj.comp hd.continuous)).integrable_of_hasCompactSupport
      hs.deriv.mul_left.mul_right
  have hj : Integrable (fun t => starRingEnd ℂ (f t)*opComplexLaguerreExpression f t)
      gammaProbability :=
    (hc.continuous.mul (op_complex_laguerre_expression_contDiff f hf).continuous).integrable_of_hasCompactSupport
      (op_complex_laguerre_expression_compact f hs).mul_left
  rw [he, integral_sub hi hj] at h
  exact (sub_eq_zero.mp h).symm

theorem smooth_compact_derivative_energy_integrable (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    Integrable (fun t : ℝ => steinFlux t*‖deriv f t‖^2) (volume : Measure ℝ) := by
  have hd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hds : HasCompactSupport (fun t : ℝ => ‖deriv f t‖^2) :=
    by
      rw [show (fun t : ℝ => ‖deriv f t‖^2) =
        (fun t => ‖deriv f t‖*‖deriv f t‖) by funext t; ring]
      exact hs.deriv.norm.mul_right
  have hc : Continuous (fun t : ℝ => steinFlux t*‖deriv f t‖^2) :=
    steinFlux_contDiff.continuous.mul (hd.continuous.norm.pow 2)
  have hs2 : HasCompactSupport (fun t : ℝ => steinFlux t*‖deriv f t‖^2) := hds.mul_left
  exact hc.integrable_of_hasCompactSupport hs2

/-- The Gamma-weighted expression is the literal Lebesgue integral of
`q(t) |f'(t)|²`, not an energy defined by its spectral answer. -/
theorem op_complex_laguerre_green_energy (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    (∫ t, starRingEnd ℂ (f t)*opComplexLaguerreExpression f t ∂gammaProbability) =
      ((∫ t : ℝ in Ioi 0, steinFlux t*‖deriv f t‖^2 : ℝ):ℂ) := by
  rw [op_complex_laguerre_green_energy_gamma f hf hs, gamma_probability_complex_integral]
  have he : (fun t : ℝ => (SigmaPresentations.density t:ℂ)*
      ((t:ℂ)*deriv f t*starRingEnd ℂ (deriv f t))) =
      fun t => ((steinFlux t*‖deriv f t‖^2 : ℝ):ℂ) := by
    funext t
    rw [mul_assoc (t:ℂ), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [steinFlux, SigmaPresentations.density]
    push_cast
    ring
  rw [he]
  exact Complex.ofRealCLM.integral_comp_comm
    (smooth_compact_derivative_energy_integrable f hf hs).integrableOn

theorem smooth_compact_inner_differential_energy (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    @inner ℂ LaguerreWeightedHilbert _ (smoothCompactL2Vector f hf hs)
      (smoothCompactL2Image f hf hs) =
      ((∫ t : ℝ in Ioi 0, steinFlux t*‖deriv f t‖^2 : ℝ):ℂ) := by
  rw [L2.inner_def]
  calc
    _ = ∫ t, starRingEnd ℂ (f t)*opComplexLaguerreExpression f t ∂gammaProbability := by
      apply integral_congr_ae
      filter_upwards [smooth_compact_l2_coe f hf hs, smooth_compact_image_coe f hf hs] with t ht hi
      simp only [ht, hi, RCLike.inner_apply, mul_comm]
    _ = _ := op_complex_laguerre_green_energy f hf hs

theorem smooth_compact_square_root_differential_energy (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    ‖laguerreSpectralOperator Real.sqrt ⟨smoothCompactL2Vector f hf hs,
      laguerre_integer_domain_le_square_root (smooth_compact_mem_laguerre_domain f hf hs)⟩‖^2 =
      ∫ t : ℝ in Ioi 0, steinFlux t*‖deriv f t‖^2 := by
  have h := laguerre_integer_inner_energy
    ⟨smoothCompactL2Vector f hf hs, smooth_compact_mem_laguerre_domain f hf hs⟩
  rw [laguerre_spectral_extends_differential_test, smooth_compact_inner_differential_energy] at h
  exact Complex.ofReal_injective h.symm

theorem laguerre_minimal_test_energy (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (hpos : tsupport f ⊆ Ioi 0) :
    @inner ℂ LaguerreWeightedHilbert _ (smoothCompactL2Vector f hf hs)
      (laguerreMinimalOperator ⟨smoothCompactL2Vector f hf hs,
        laguerre_compact_test_mem f hf hs hpos⟩) =
      ((∫ t : ℝ in Ioi 0, steinFlux t*‖deriv f t‖^2 : ℝ):ℂ) := by
  rw [laguerre_minimal_test_action f hf hs hpos]
  exact smooth_compact_inner_differential_energy f hf hs

end
end Sigma
