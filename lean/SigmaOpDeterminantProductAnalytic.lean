import SigmaOpDeterminantProduct
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology BigOperators
variable {ι : Type*}

theorem determinant_factor_differentiable (regularized : Bool) (c : ℂ) :
    Differentiable ℂ (fun z => determinantFactor regularized (z*c)) := by
  cases regularized <;> simp only [determinantFactor, Bool.false_eq_true, if_false, if_true]
  · exact (differentiable_const _).add (differentiable_id.mul_const c)
  · exact ((differentiable_const _).add (differentiable_id.mul_const c)).mul
      (Complex.differentiable_exp.comp (differentiable_id.mul_const c).neg)

theorem determinant_log_differentiableAt (regularized : Bool) (c z : ℂ) (hz : ‖z*c‖ < 1) :
    DifferentiableAt ℂ (fun z => determinantLog regularized (z*c)) z := by
  have h := ((differentiableAt_const _).add (differentiableAt_id.mul_const c)).clog
    (Complex.mem_slitPlane_of_norm_lt_one hz)
  cases regularized
  · exact h
  · exact h.sub (differentiableAt_id.mul_const c)

theorem determinant_exists_finite_tail (regularized : Bool) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖^(determinantSummabilityPower regularized)))
    (R : ℝ) :
    ∃ S : Finset ι, ∀ i ∉ S, R*‖c i‖ ≤ 1/2 := by
  classical
  have ht := (determinant_coefficients_tendsto_zero regularized c hc).norm.const_mul R
  have hh : ∀ᶠ i in cofinite, R*‖c i‖ < (1/2 : ℝ) := by
    exact (show Tendsto (fun i => R*‖c i‖) cofinite (𝓝 0) by simpa using ht).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))
  have hf := eventually_cofinite.mp hh
  refine ⟨hf.toFinset, ?_⟩
  intro i hi
  have h : ¬ ¬ (R*‖c i‖ < (1/2 : ℝ)) := by simpa using hi
  exact (not_not.mp h).le

def spectralDeterminantTailLog (regularized : Bool) (c : ι → ℂ) (S : Finset ι) (z : ℂ) : ℂ :=
  ∑' i : {i // i ∉ S}, determinantLog regularized (z*c i)

theorem spectral_determinant_tail_log_differentiableOn (regularized : Bool) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖^(determinantSummabilityPower regularized)))
    (S : Finset ι) (R : ℝ) (hR : 0 < R) (hS : ∀ i ∉ S, R*‖c i‖ ≤ 1/2) :
    DifferentiableOn ℂ (spectralDeterminantTailLog regularized c S) (Metric.ball 0 R) := by
  have hu := (hc.subtype {i | i ∉ S}).mul_left (2*R^(determinantSummabilityPower regularized))
  refine Complex.differentiableOn_tsum_of_summable_norm hu ?_ Metric.isOpen_ball ?_
  · intro i z hz
    apply (determinant_log_differentiableAt regularized (c i) z _).differentiableWithinAt
    have hz' : ‖z‖ < R := by simpa using hz
    have hh : ‖z*c i‖ ≤ 1/2 := (norm_mul z (c i)).le.trans
      ((mul_le_mul_of_nonneg_right hz'.le (norm_nonneg _)).trans (hS i i.property))
    exact lt_of_le_of_lt hh (by norm_num)
  · intro i z hz
    have hz' : ‖z‖ < R := by simpa using hz
    have hh : ‖z*c i‖ ≤ 1/2 := (norm_mul z (c i)).le.trans
      ((mul_le_mul_of_nonneg_right hz'.le (norm_nonneg _)).trans (hS i i.property))
    calc
      _ ≤ 2*‖z*c i‖^(determinantSummabilityPower regularized) :=
        determinant_log_norm_bound regularized _ hh
      _ ≤ 2*(R*‖c i‖)^(determinantSummabilityPower regularized) := by rw [norm_mul]; gcongr
      _ = _ := by simp only [mul_pow, Function.comp_apply]; ring

theorem spectral_determinant_finite_exp (regularized : Bool) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖^(determinantSummabilityPower regularized)))
    (S : Finset ι) (z : ℂ) (hS : ∀ i ∉ S, ‖z*c i‖ < 1) :
    spectralDeterminant regularized c z =
      (∏ i ∈ S, determinantFactor regularized (z*c i)) *
        Complex.exp (spectralDeterminantTailLog regularized c S z) := by
  have ht := determinant_factors_hasProd_exp regularized (fun i : {i // i ∉ S} => c i)
    (hc.subtype {i | i ∉ S}) z (fun i =>
      Complex.slitPlane_ne_zero (Complex.mem_slitPlane_of_norm_lt_one (hS i i.property)))
  exact ((S.hasProd (fun i => determinantFactor regularized (z*c i))).mul_compl ht).tprod_eq

/-- Both infinite products are entire, as actual locally convergent spectral products. -/
theorem spectral_determinant_entire (regularized : Bool) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖^(determinantSummabilityPower regularized))) (z : ℂ) :
    AnalyticAt ℂ (spectralDeterminant regularized c) z := by
  classical
  let R := ‖z‖+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hz : z ∈ Metric.ball 0 R := by simp [R]
  obtain ⟨S, hS⟩ := determinant_exists_finite_tail regularized c hc R
  have hg := spectral_determinant_tail_log_differentiableOn regularized c hc S R hR hS
  have hp : Differentiable ℂ (fun w => ∏ i ∈ S, determinantFactor regularized (w*c i)) :=
    Differentiable.finset_prod (fun i _ => determinant_factor_differentiable regularized (c i))
  have han : AnalyticAt ℂ (fun w => (∏ i ∈ S, determinantFactor regularized (w*c i)) *
      Complex.exp (spectralDeterminantTailLog regularized c S w)) z := by
    apply DifferentiableOn.analyticAt _ (Metric.isOpen_ball.mem_nhds hz)
    exact hp.differentiableOn.mul (Complex.differentiable_exp.comp_differentiableOn hg)
  apply han.congr
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  symm
  apply spectral_determinant_finite_exp regularized c hc S w
  intro i hi
  have hw' : ‖w‖ < R := by simpa using hw
  have hh := (mul_le_mul_of_nonneg_right hw'.le (norm_nonneg (c i))).trans (hS i hi)
  exact lt_of_le_of_lt (by simpa only [norm_mul] using hh) (by norm_num)

end
end Sigma
