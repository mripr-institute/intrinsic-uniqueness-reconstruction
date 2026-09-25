import SigmaOpHeatKernelPointwise
import SigmaOpLaguerreResolventTrace

namespace Sigma
noncomputable section
open MeasureTheory Set
attribute [local instance] Measure.Subtype.measureSpace

/-- The Laplace weight of the `n`th heat eigenvalue is the first resolvent
eigenvalue. -/
theorem laguerre_heat_laplace_eigenvalue (α : ℝ) (hα : 0 < α) (n : ℕ) :
    (∫ τ : ℝ in Ioi 0, Real.exp (-(((n : ℝ) + α) * τ))) =
      ((n : ℝ) + α)⁻¹ := by
  have hr : 0 < (n : ℝ) + α := by positivity
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 1) (r := (n : ℝ) + α) (by norm_num) hr
  simpa using h

/-- The time-weighted Laplace coefficient is the squared-resolvent
eigenvalue. -/
theorem laguerre_heat_time_laplace_eigenvalue (α : ℝ) (hα : 0 < α) (n : ℕ) :
    (∫ τ : ℝ in Ioi 0, τ * Real.exp (-(((n : ℝ) + α) * τ))) =
      (((n : ℝ) + α)⁻¹) ^ 2 := by
  have hr : 0 < (n : ℝ) + α := by positivity
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 2) (r := (n : ℝ) + α) (by norm_num) hr
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    Real.rpow_two, Real.Gamma_two, mul_one, one_div, inv_pow] using h

/-- The native heat operator acts diagonally on the actual weighted `L²`
Laguerre basis. -/
theorem laguerre_heat_basis_action (τ : ℝ) (hτ : 0 ≤ τ) (n : ℕ) :
    laguerreHeatOperator τ hτ (laguerreHilbertBasis n) =
      (Real.exp (-τ * (n : ℝ)) : ℂ) • laguerreHilbertBasis n := by
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext k
  rw [laguerre_heat_coordinate, _root_.map_smul, laguerreHilbertBasis.repr_self]
  change (Real.exp (-τ * (k : ℝ)) : ℂ) * markedIntegerEigenvector n k =
    (Real.exp (-τ * (n : ℝ)) : ℂ) * markedIntegerEigenvector n k
  by_cases h : k = n
  · subst k
    rfl
  · simp [markedIntegerEigenvector, lp.single_apply_ne, h]

/-- On each genuine weighted `L²` eigenvector, the Bochner Laplace integral
of the heat operator is the native resolvent. -/
theorem laguerre_heat_laplace_basis_action (α : ℝ) (hα : 0 < α) (n : ℕ) :
    (∫ τ : Ioi (0 : ℝ),
      (Real.exp (-α * (τ : ℝ)) : ℂ) •
        laguerreHeatOperator (τ : ℝ) τ.property.le (laguerreHilbertBasis n)) =
      laguerreResolvent α hα (laguerreHilbertBasis n) := by
  have hpoint (τ : Ioi (0 : ℝ)) :
      (Real.exp (-α * (τ : ℝ)) : ℂ) •
          laguerreHeatOperator (τ : ℝ) τ.property.le (laguerreHilbertBasis n) =
        (Real.exp (-(((n : ℝ) + α) * (τ : ℝ))) : ℂ) •
          laguerreHilbertBasis n := by
    rw [laguerre_heat_basis_action, smul_smul, ← Complex.ofReal_mul,
      ← Real.exp_add]
    congr 1
    ring
  simp_rw [hpoint]
  rw [integral_smul_const]
  have hcoe :
      (∫ τ : Ioi (0 : ℝ),
        (Real.exp (-(((n : ℝ) + α) * (τ : ℝ))) : ℂ)) =
      (↑(∫ τ : Ioi (0 : ℝ), Real.exp (-(((n : ℝ) + α) * (τ : ℝ)))) : ℂ) :=
    integral_ofReal
  rw [hcoe]
  have hsub :
      (∫ τ : Ioi (0 : ℝ), Real.exp (-(((n : ℝ) + α) * (τ : ℝ)))) =
      ∫ τ : ℝ in Ioi 0, Real.exp (-(((n : ℝ) + α) * τ)) :=
    integral_subtype (s := Ioi (0 : ℝ)) measurableSet_Ioi
      (fun τ : ℝ => Real.exp (-(((n : ℝ) + α) * τ)))
  rw [hsub]
  rw [laguerre_heat_laplace_eigenvalue α hα n]
  convert (laguerre_resolvent_basis_action α hα n).symm using 1
  push_cast
  ring

/-- The time-weighted heat integral agrees with the squared native resolvent
on every vector of the genuine weighted `L²` Laguerre basis. -/
theorem laguerre_heat_time_laplace_basis_action (α : ℝ) (hα : 0 < α) (n : ℕ) :
    (∫ τ : Ioi (0 : ℝ),
      (((τ : ℝ) * Real.exp (-α * (τ : ℝ))) : ℂ) •
        laguerreHeatOperator (τ : ℝ) τ.property.le (laguerreHilbertBasis n)) =
      laguerreSquaredResolvent α hα (laguerreHilbertBasis n) := by
  have hpoint (τ : Ioi (0 : ℝ)) :
      (((τ : ℝ) * Real.exp (-α * (τ : ℝ))) : ℂ) •
          laguerreHeatOperator (τ : ℝ) τ.property.le (laguerreHilbertBasis n) =
        (((τ : ℝ) * Real.exp (-(((n : ℝ) + α) * (τ : ℝ)))) : ℂ) •
          laguerreHilbertBasis n := by
    rw [laguerre_heat_basis_action, smul_smul]
    congr 1
    norm_cast
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hpoint]
  rw [integral_smul_const]
  have hcoe :
      (∫ τ : Ioi (0 : ℝ),
        (((τ : ℝ) * Real.exp (-(((n : ℝ) + α) * (τ : ℝ)))) : ℂ)) =
      (↑(∫ τ : Ioi (0 : ℝ),
        (τ : ℝ) * Real.exp (-(((n : ℝ) + α) * (τ : ℝ)))) : ℂ) :=
    by
      calc
        _ = ∫ τ : Ioi (0 : ℝ),
            (↑((τ : ℝ) * Real.exp (-(((n : ℝ) + α) * (τ : ℝ)))) : ℂ) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall (fun τ => by norm_cast)
        _ = _ := integral_ofReal
  rw [hcoe]
  have hsub :
      (∫ τ : Ioi (0 : ℝ),
        (τ : ℝ) * Real.exp (-(((n : ℝ) + α) * (τ : ℝ)))) =
      ∫ τ : ℝ in Ioi 0, τ * Real.exp (-(((n : ℝ) + α) * τ)) :=
    integral_subtype (s := Ioi (0 : ℝ)) measurableSet_Ioi
      (fun τ : ℝ => τ * Real.exp (-(((n : ℝ) + α) * τ)))
  rw [hsub, laguerre_heat_time_laplace_eigenvalue α hα n]
  convert (laguerre_squared_resolvent_basis_action α hα n).symm using 1
  push_cast
  ring

end
end Sigma
