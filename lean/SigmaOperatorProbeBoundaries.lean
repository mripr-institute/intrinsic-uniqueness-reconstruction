import SigmaOperators
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace Sigma
noncomputable section
open scoped ContDiff

theorem operator_linear_only_smooth_positive_witness :
    ∃ a b : ℝ → ℝ, ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧
      (∀ t > 0, 0 < a t) ∧
      (∀ t > 0, opExpression a b opLinearProbe t = 2-t) ∧
      opExpression a b opQuadraticProbe 1 ≠ (1:ℝ)^2-6*1+6 := by
  refine ⟨fun t => 2*t, fun t => 2-t, by fun_prop, by fun_prop, ?_, ?_, ?_⟩
  · intro t ht
    positivity
  · intro t _
    exact operator_linear_probe_arbitrary_diffusion _ t
  · rw [opExpression_quadratic]
    norm_num

theorem operator_quadratic_only_smooth_positive_witness :
    ∃ a b : ℝ → ℝ, ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧
      (∀ t > 0, 0 < a t) ∧
      (∀ t > 0, opExpression a b opQuadraticProbe t = t^2-6*t+6) ∧
      opExpression a b opLinearProbe 1 ≠ 2-(1:ℝ) := by
  have hd : ∀ t : ℝ, 1+(t-3)^2 ≠ 0 := fun t => ne_of_gt (by positivity)
  have hden : ContDiff ℝ ∞ (fun t : ℝ => 1+(t-3)^2) := by fun_prop
  refine ⟨fun t => t/(1+(t-3)^2), fun t => 2-t+t*(t-3)/(1+(t-3)^2),
    contDiff_id.div hden hd, ?_, ?_, ?_, ?_⟩
  · exact (contDiff_const.sub contDiff_id).add
      ((contDiff_id.mul (contDiff_id.sub contDiff_const)).div hden hd)
  · intro t ht
    exact (operator_quadratic_positive_counterexample t ht).1
  · intro t ht
    exact (operator_quadratic_positive_counterexample t ht).2
  · rw [opExpression_linear]
    norm_num

/-- Both marked probes are independently necessary even in the globally
smooth positive-diffusion subclass. Each omitted identity fails at t=1. -/
theorem operator_marked_probe_irredundancy :
    (∃ a b : ℝ → ℝ, ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧
      (∀ t > 0, 0 < a t) ∧
      (∀ t > 0, opExpression a b opLinearProbe t = 2-t) ∧
      opExpression a b opQuadraticProbe 1 ≠ (1:ℝ)^2-6*1+6) ∧
    (∃ a b : ℝ → ℝ, ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧
      (∀ t > 0, 0 < a t) ∧
      (∀ t > 0, opExpression a b opQuadraticProbe t = t^2-6*t+6) ∧
      opExpression a b opLinearProbe 1 ≠ 2-(1:ℝ)) :=
  ⟨operator_linear_only_smooth_positive_witness, operator_quadratic_only_smooth_positive_witness⟩

end
end Sigma
