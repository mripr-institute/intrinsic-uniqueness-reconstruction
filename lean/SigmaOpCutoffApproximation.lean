import SigmaOpDifferentialBridge
import SigmaOpLogCutoff
import SigmaSteinMomentLimits
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal NNReal

theorem laguerre_l2_norm_sq_integral (x : LaguerreWeightedHilbert) :
    ‖x‖^2 = ∫ t : ℝ, ‖x t‖^2 ∂gammaProbability := by
  rw [norm_sq_eq_inner (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner x x)]
  congr 1
  funext t
  exact (norm_sq_eq_inner (𝕜 := ℂ) (x t)).symm

theorem laguerre_l2_norm_sq_of_ae (x : LaguerreWeightedHilbert) (f : ℝ → ℂ)
    (hf : (x : ℝ → ℂ) =ᵐ[gammaProbability] f) :
    ‖x‖^2 = ∫ t : ℝ, ‖f t‖^2 ∂gammaProbability := by
  rw [laguerre_l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [hf] with t ht
  rw [ht]

theorem laguerre_l2_tendsto_of_sq_error {ι : Type*} {l : Filter ι}
    (x : ι → LaguerreWeightedHilbert) (y : LaguerreWeightedHilbert)
    (h : Tendsto (fun i => ‖x i-y‖^2) l (𝓝 0)) : Tendsto x l (𝓝 y) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hh

theorem op_complex_laguerre_product (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (t : ℝ) :
    opComplexLaguerreExpression (fun u => f u*g u) t =
      f t * opComplexLaguerreExpression g t + g t * opComplexLaguerreExpression f t -
        2*(t : ℂ)*deriv f t*deriv g t := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have he : Differentiable ℝ g := hg.differentiable (by simp)
  have hdd : Differentiable ℝ (deriv f) :=
    (contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)
  have hed : Differentiable ℝ (deriv g) :=
    (contDiff_infty_iff_deriv.mp hg).2.differentiable (by simp)
  have hp : deriv (fun u => f u*g u) = fun u => deriv f u*g u+f u*deriv g u := by
    funext u
    exact deriv_mul (hd u) (he u)
  simp only [opComplexLaguerreExpression, hp]
  rw [deriv_add ((hdd t).mul (he t)) ((hd t).mul (hed t)),
    deriv_mul (hdd t) (he t), deriv_mul (hd t) (hed t)]
  ring

theorem op_complex_laguerre_ofReal (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    opComplexLaguerreExpression (fun u => (f u : ℂ)) t =
      ((-t*deriv (deriv f) t - (2-t)*deriv f t : ℝ) : ℂ) := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hdd : Differentiable ℝ (deriv f) :=
    (contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)
  have he : deriv (fun u : ℝ => (f u : ℂ)) = fun u : ℝ => Complex.ofReal (deriv f u) := by
    funext u
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u (hd u).hasDerivAt).deriv
  have he₂ : deriv (fun u => Complex.ofReal (deriv f u)) t = Complex.ofReal (deriv (deriv f) t) :=
    (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hdd t).hasDerivAt).deriv
  simp only [opComplexLaguerreExpression, he, he₂, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]

theorem laguerre_bounded_cutoff_error_tendsto (f : ℝ → ℂ)
    (hf : Memℒp f 2 gammaProbability) (c : ℕ → ℝ → ℝ)
    (hc : ∀ k, Continuous (c k)) (hcb : ∀ k t, 0 ≤ c k t ∧ c k t ≤ 1)
    (hcl : ∀ᵐ t ∂gammaProbability, Tendsto (fun k => c k t) atTop (𝓝 1)) :
    Tendsto (fun k => ∫ t, ‖((c k t-1 : ℝ) : ℂ)*f t‖^2 ∂gammaProbability)
      atTop (𝓝 0) := by
  have hi := (memℒp_two_iff_integrable_sq_norm hf.1).mp hf
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := gammaProbability) (l := (atTop : Filter ℕ))
    (F := fun k t => ‖((c k t-1 : ℝ) : ℂ)*f t‖^2)
    (f := fun _ => (0 : ℝ)) (fun t => ‖f t‖^2) ?_ ?_ hi ?_
  · simpa using h
  · exact Eventually.of_forall fun k =>
      (((Complex.continuous_ofReal.comp ((hc k).sub continuous_const)).aestronglyMeasurable.mul hf.1).norm.pow 2)
  · apply Eventually.of_forall
    intro k
    apply Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hb : |c k t-1| ≤ 1 := abs_le.mpr ⟨by linarith [(hcb k t).1], by linarith [(hcb k t).2]⟩
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (norm_nonneg (f t))
  · filter_upwards [hcl] with t ht
    have hh := ((Complex.continuous_ofReal.continuousAt.tendsto.comp
      (ht.sub_const 1)).mul_const (f t)).norm.pow 2
    simpa using hh

end
end Sigma
