import SigmaPresentations
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-! Exact differential-expression results for the final operator chapter.
The coefficient category and the two actual derivatives are explicit.
This module does not replace the unbounded Hilbert realization by a matrix.
-/

namespace Sigma
noncomputable section

open SigmaPresentations

abbrev opLinearProbe : ℝ → ℝ := SigmaPresentations.linearEigenfunction
abbrev opQuadraticProbe : ℝ → ℝ := SigmaPresentations.quadraticEigenfunction
abbrev opExpression := SigmaPresentations.differentialExpression

theorem opExpression_linear (a b : ℝ → ℝ) (t : ℝ) :
    opExpression a b opLinearProbe t = b t := by
  simp [opExpression, SigmaPresentations.differentialExpression,
    SigmaPresentations.linearEigenfunction_deriv, SigmaPresentations.localExpression]

theorem opExpression_quadratic (a b : ℝ → ℝ) (t : ℝ) :
    opExpression a b opQuadraticProbe t = -a t - b t * (t - 3) := by
  have hd : deriv (fun x : ℝ => x - 3) t = 1 :=
    ((hasDerivAt_id t).sub_const 3).deriv
  simp [opExpression, SigmaPresentations.differentialExpression,
    SigmaPresentations.quadraticEigenfunction_deriv, SigmaPresentations.localExpression, hd]

/-- The exact pointwise iff in final:O2, before the separate Pearson realization. -/
theorem operator_two_probe_iff (a b : ℝ → ℝ) :
    ((∀ t > 0, opExpression a b opLinearProbe t = 2 - t) ∧
      (∀ t > 0, opExpression a b opQuadraticProbe t = t ^ 2 - 6 * t + 6)) ↔
    ∀ t > 0, a t = t ∧ b t = 2 - t := by
  constructor
  · rintro ⟨hl, hq⟩ t ht
    have hb : b t = 2 - t := by simpa [opExpression_linear] using hl t ht
    have h := hq t ht
    rw [opExpression_quadratic, hb] at h
    exact ⟨by nlinarith, hb⟩
  · intro h
    constructor
    · intro t ht
      rw [opExpression_linear, (h t ht).2]
    · intro t ht
      rw [opExpression_quadratic, (h t ht).1, (h t ht).2]
      ring

/-- The almost-everywhere version, applicable in particular to Lebesgue
measure restricted to the marked positive ray. -/
theorem operator_two_probe_ae_iff (μ : MeasureTheory.Measure ℝ) (a b : ℝ → ℝ) :
    ((∀ᵐ t ∂μ, opExpression a b opLinearProbe t = 2 - t) ∧
      (∀ᵐ t ∂μ, opExpression a b opQuadraticProbe t = t ^ 2 - 6 * t + 6)) ↔
    ∀ᵐ t ∂μ, a t = t ∧ b t = 2 - t := by
  constructor
  · rintro ⟨hl, hq⟩
    filter_upwards [hl, hq] with t hlt hqt
    rw [opExpression_linear] at hlt
    rw [opExpression_quadratic, hlt] at hqt
    exact ⟨by nlinarith, hlt⟩
  · intro h
    constructor
    · filter_upwards [h] with t ht
      rw [opExpression_linear, ht.2]
    · filter_upwards [h] with t ht
      rw [opExpression_quadratic, ht.1, ht.2]
      ring

theorem operator_canonical_probes (t : ℝ) :
    opExpression id (fun x => 2 - x) opLinearProbe t = 2 - t ∧
    opExpression id (fun x => 2 - x) opQuadraticProbe t = t ^ 2 - 6 * t + 6 := by
  rw [opExpression_linear, opExpression_quadratic]
  constructor
  · rfl
  · simp only [id_eq]
    ring

/-- Omitting the quadratic probe permits every positive diffusion coefficient. -/
theorem operator_linear_probe_arbitrary_diffusion (a : ℝ → ℝ) (t : ℝ) :
    opExpression a (fun x => 2 - x) opLinearProbe t = 2 - t := by
  rw [opExpression_linear]

/-- The exact counterfamily used in final:O2-boundaries. -/
theorem operator_quadratic_probe_counterfamily (k : ℝ → ℝ) (ε t : ℝ) :
    opExpression (fun x => x - ε * k x * (x - 3))
      (fun x => 2 - x + ε * k x) opQuadraticProbe t = t ^ 2 - 6 * t + 6 := by
  rw [opExpression_quadratic]
  ring

theorem operator_counterfamily_changes_linear {k : ℝ → ℝ} {ε t : ℝ}
    (h : ε * k t ≠ 0) :
    opExpression (fun x => x - ε * k x * (x - 3))
      (fun x => 2 - x + ε * k x) opLinearProbe t ≠ 2 - t := by
  rw [opExpression_linear]
  simpa using h

/-- A global positive rational diffusion supplies an explicit quadratic-only witness. -/
theorem operator_quadratic_positive_counterexample (t : ℝ) (ht : 0 < t) :
    0 < t / (1 + (t - 3) ^ 2) ∧
    opExpression (fun x => x / (1 + (x - 3) ^ 2))
      (fun x => 2 - x + x * (x - 3) / (1 + (x - 3) ^ 2))
      opQuadraticProbe t = t ^ 2 - 6 * t + 6 := by
  have hp : 0 < 1 + (t - 3) ^ 2 := by positivity
  refine ⟨div_pos ht hp, ?_⟩
  rw [opExpression_quadratic]
  field_simp
  ring

/-- Canonical zero-current flux, with an actual derivative of the stated density. -/
theorem operator_pearson_flux_derivative (t : ℝ) :
    HasDerivAt (fun x : ℝ => x * SigmaPresentations.density x)
      ((2 - t) * SigmaPresentations.density t) t := by
  have he := (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
  convert (hasDerivAt_id t).mul ((hasDerivAt_id t).mul he) using 1 ;
    simp [SigmaPresentations.density, Function.comp_def] ; ring

/-- Every constant-flux Stein family in final:O1-kernel satisfies the differential equation. -/
theorem operator_stein_flux_family (C t : ℝ) :
    HasDerivAt (fun x : ℝ => x * SigmaPresentations.density x + C)
      ((2 - t) * SigmaPresentations.density t) t :=
  (operator_pearson_flux_derivative t).add_const C

/-- The actual scalar heat-eigenvalue series, not an operator-trace definition. -/
theorem operator_heat_eigenvalue_hasSum {τ : ℝ} (hτ : 0 < τ) :
    HasSum (fun n : ℕ => Real.exp (-τ * n)) (1 / (1 - Real.exp (-τ))) := by
  have he : |Real.exp (-τ)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  convert hasSum_geometric_of_abs_lt_one he using 1
  · funext n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  · rw [one_div]

theorem operator_heat_eigenvalue_summable_iff (τ : ℝ) :
    Summable (fun n : ℕ => Real.exp (-τ * n)) ↔ 0 < τ := by
  have heq : (fun n : ℕ => Real.exp (-τ * n)) =
      (fun n : ℕ => (Real.exp (-τ)) ^ n) := by
    funext n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq, summable_geometric_iff_norm_lt_one]
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
  constructor <;> intro h <;> linarith

end
end Sigma
