import SigmaOpHeatKernelPointwise
import SigmaOpLaguerreResolventTrace

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
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

/-- Time dependence of the native heat action is strongly measurable on the
positive-time domain. -/
theorem laguerre_heat_action_stronglyMeasurable (f : LaguerreWeightedHilbert) :
    StronglyMeasurable (fun τ : Ioi (0 : ℝ) =>
      laguerreHeatOperator (τ : ℝ) τ.property.le f) := by
  let S : ℕ → Ioi (0 : ℝ) → LaguerreWeightedHilbert := fun N τ =>
    ∑ n ∈ Finset.range N,
      ((Real.exp (-(τ : ℝ) * (n : ℝ)) : ℂ) *
        laguerreHilbertBasis.repr f n) • laguerreHilbertBasis n
  have hS (N : ℕ) : Continuous (S N) := by
    dsimp [S]
    fun_prop
  apply stronglyMeasurable_of_tendsto atTop (fun N => (hS N).stronglyMeasurable)
  apply tendsto_pi_nhds.mpr
  intro τ
  have h := (laguerreHilbertBasis.hasSum_repr
    (laguerreHeatOperator (τ : ℝ) τ.property.le f)).tendsto_sum_nat
  convert h using 1
  funext N
  dsimp [S]
  congr 1
  funext n
  rw [laguerre_heat_coordinate]

private theorem laguerre_heat_laplace_weight_integrable (α : ℝ) (hα : 0 < α) :
    Integrable (fun τ : Ioi (0 : ℝ) => Real.exp (-α * (τ : ℝ))) := by
  have hbase : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
    convert Real.GammaIntegral_convergent (s := 1) (by norm_num) using 1
    funext t
    simp
  have hreal : IntegrableOn (fun t : ℝ => Real.exp (-(α * t))) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun t : ℝ => Real.exp (-t)) 0 hα).2
        (by simpa only [mul_zero] using hbase)
    simpa using h
  have hmeas := hreal.aestronglyMeasurable
  rw [IntegrableOn, ← map_comap_subtype_coe, integrable_map_measure] at hreal
  · change Integrable (fun τ : Ioi (0 : ℝ) => Real.exp (-α * (τ : ℝ)))
      (Measure.comap Subtype.val volume)
    simpa only [Function.comp_apply, neg_mul] using hreal
  · simpa only [map_comap_subtype_coe measurableSet_Ioi] using hmeas
  · exact measurable_subtype_coe.aemeasurable
  · exact measurableSet_Ioi

/-- The vector-valued Laplace integral of the actual heat action exists for
every input in the weighted Hilbert space. -/
theorem laguerre_heat_laplace_integrable (α : ℝ) (hα : 0 < α)
    (f : LaguerreWeightedHilbert) :
    Integrable (fun τ : Ioi (0 : ℝ) =>
      (Real.exp (-α * (τ : ℝ)) : ℂ) •
        laguerreHeatOperator (τ : ℝ) τ.property.le f) := by
  have hw : Continuous (fun τ : Ioi (0 : ℝ) =>
      (Real.exp (-α * (τ : ℝ)) : ℂ)) := by fun_prop
  have hsm := hw.stronglyMeasurable.smul (laguerre_heat_action_stronglyMeasurable f)
  have hbound := (laguerre_heat_laplace_weight_integrable α hα).mul_const ‖f‖
  apply hbound.mono' hsm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun τ => by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left
      (laguerre_heat_contracts (τ : ℝ) τ.property.le f)
      (Real.exp_pos _).le)

private theorem laguerre_heat_laplace_complex_coefficient
    (α : ℝ) (hα : 0 < α) (n : ℕ) :
    (∫ τ : Ioi (0 : ℝ),
      (Real.exp (-(((n : ℝ) + α) * (τ : ℝ))) : ℂ)) =
      (((n : ℝ) + α)⁻¹ : ℂ) := by
  calc
    _ = (↑(∫ τ : Ioi (0 : ℝ),
        Real.exp (-(((n : ℝ) + α) * (τ : ℝ)))) : ℂ) := integral_ofReal
    _ = (↑(∫ τ : ℝ in Ioi 0,
        Real.exp (-(((n : ℝ) + α) * τ))) : ℂ) := by
          rw [integral_subtype (s := Ioi (0 : ℝ)) measurableSet_Ioi
            (fun τ : ℝ => Real.exp (-(((n : ℝ) + α) * τ)))]
    _ = _ := by
      rw [laguerre_heat_laplace_eigenvalue α hα n]
      norm_cast

/-- The Bochner Laplace integral of the native heat operator is the full
resolvent on every vector in the Gamma-weighted Hilbert space. -/
theorem laguerre_heat_laplace_operator (α : ℝ) (hα : 0 < α)
    (f : LaguerreWeightedHilbert) :
    (∫ τ : Ioi (0 : ℝ),
      (Real.exp (-α * (τ : ℝ)) : ℂ) •
        laguerreHeatOperator (τ : ℝ) τ.property.le f) =
      laguerreResolvent α hα f := by
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext n
  rw [laguerre_resolvent_coordinate,
    laguerreHilbertBasis.repr_apply_apply]
  have hin := ((innerSL ℂ (laguerreHilbertBasis n)).integral_comp_comm
    (laguerre_heat_laplace_integrable α hα f))
  change (∫ τ : Ioi (0 : ℝ),
      @inner ℂ LaguerreWeightedHilbert _ (laguerreHilbertBasis n)
        ((Real.exp (-α * (τ : ℝ)) : ℂ) •
          laguerreHeatOperator (τ : ℝ) τ.property.le f)) =
    @inner ℂ LaguerreWeightedHilbert _ (laguerreHilbertBasis n)
      (∫ τ : Ioi (0 : ℝ),
        (Real.exp (-α * (τ : ℝ)) : ℂ) •
          laguerreHeatOperator (τ : ℝ) τ.property.le f) at hin
  rw [← hin]
  have hpoint (τ : Ioi (0 : ℝ)) :
      @inner ℂ LaguerreWeightedHilbert _ (laguerreHilbertBasis n)
        ((Real.exp (-α * (τ : ℝ)) : ℂ) •
          laguerreHeatOperator (τ : ℝ) τ.property.le f) =
        (Real.exp (-(((n : ℝ) + α) * (τ : ℝ))) : ℂ) *
          laguerreHilbertBasis.repr f n := by
    rw [inner_smul_right, ← laguerreHilbertBasis.repr_apply_apply,
      laguerre_heat_coordinate, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.exp_add]
    congr 1
    ring
  simp_rw [hpoint]
  rw [integral_mul_right, laguerre_heat_laplace_complex_coefficient α hα n]
  push_cast
  ring

private theorem laguerre_heat_time_laplace_weight_integrable
    (α : ℝ) (hα : 0 < α) :
    Integrable (fun τ : Ioi (0 : ℝ) =>
      (τ : ℝ) * Real.exp (-α * (τ : ℝ))) := by
  have hbase : IntegrableOn (fun t : ℝ => t * Real.exp (-t)) (Ioi 0) := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, mul_comm]
      using Real.GammaIntegral_convergent (s := 2) (by norm_num)
  have hscaled : IntegrableOn
      (fun t : ℝ => (α * t) * Real.exp (-(α * t))) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun t : ℝ => t * Real.exp (-t)) 0 hα).2
        (by simpa only [mul_zero] using hbase)
    simpa using h
  have hreal : IntegrableOn
      (fun t : ℝ => t * Real.exp (-(α * t))) (Ioi 0) := by
    change Integrable (fun t : ℝ => t * Real.exp (-(α * t)))
      (volume.restrict (Ioi 0))
    convert hscaled.const_mul α⁻¹ using 1
    funext t
    field_simp [hα.ne']
    ring
  have hmeas := hreal.aestronglyMeasurable
  rw [IntegrableOn, ← map_comap_subtype_coe, integrable_map_measure] at hreal
  · change Integrable
      (fun τ : Ioi (0 : ℝ) => (τ : ℝ) * Real.exp (-α * (τ : ℝ)))
      (Measure.comap Subtype.val volume)
    simpa only [Function.comp_apply, neg_mul] using hreal
  · simpa only [map_comap_subtype_coe measurableSet_Ioi] using hmeas
  · exact measurable_subtype_coe.aemeasurable
  · exact measurableSet_Ioi

theorem laguerre_heat_time_laplace_integrable (α : ℝ) (hα : 0 < α)
    (f : LaguerreWeightedHilbert) :
    Integrable (fun τ : Ioi (0 : ℝ) =>
      (((τ : ℝ) * Real.exp (-α * (τ : ℝ))) : ℂ) •
        laguerreHeatOperator (τ : ℝ) τ.property.le f) := by
  have hw : Continuous (fun τ : Ioi (0 : ℝ) =>
      (((τ : ℝ) * Real.exp (-α * (τ : ℝ))) : ℂ)) := by fun_prop
  have hsm := hw.stronglyMeasurable.smul (laguerre_heat_action_stronglyMeasurable f)
  have hbound := (laguerre_heat_time_laplace_weight_integrable α hα).mul_const ‖f‖
  apply hbound.mono' hsm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun τ => by
    rw [norm_smul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos τ.property, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left
      (laguerre_heat_contracts (τ : ℝ) τ.property.le f)
      (mul_pos τ.property (Real.exp_pos _)).le)

private theorem laguerre_heat_time_laplace_complex_coefficient
    (α : ℝ) (hα : 0 < α) (n : ℕ) :
    (∫ τ : Ioi (0 : ℝ),
      (((τ : ℝ) * Real.exp (-(((n : ℝ) + α) * (τ : ℝ)))) : ℂ)) =
      (((n : ℝ) + α)⁻¹ ^ 2 : ℂ) := by
  calc
    _ = (↑(∫ τ : Ioi (0 : ℝ),
        (τ : ℝ) * Real.exp (-(((n : ℝ) + α) * (τ : ℝ)))) : ℂ) := by
          calc
            _ = ∫ τ : Ioi (0 : ℝ),
                (↑((τ : ℝ) * Real.exp
                  (-(((n : ℝ) + α) * (τ : ℝ)))) : ℂ) := by
                    apply integral_congr_ae
                    exact Filter.Eventually.of_forall (fun τ => by norm_cast)
            _ = _ := integral_ofReal
    _ = (↑(∫ τ : ℝ in Ioi 0,
        τ * Real.exp (-(((n : ℝ) + α) * τ))) : ℂ) := by
          rw [integral_subtype (s := Ioi (0 : ℝ)) measurableSet_Ioi
            (fun τ : ℝ => τ * Real.exp (-(((n : ℝ) + α) * τ)))]
    _ = _ := by
      rw [laguerre_heat_time_laplace_eigenvalue α hα n]
      norm_cast

private theorem laguerre_squared_resolvent_coordinate (α : ℝ) (hα : 0 < α)
    (f : LaguerreWeightedHilbert) (n : ℕ) :
    laguerreHilbertBasis.repr (laguerreSquaredResolvent α hα f) n =
      (((n : ℂ) + (α : ℂ))⁻¹ ^ 2) * laguerreHilbertBasis.repr f n := by
  simp only [laguerreSquaredResolvent, ContinuousLinearMap.comp_apply,
    laguerre_resolvent_coordinate]
  ring

/-- The time-weighted Bochner heat integral is the square of the actual
resolvent on every weighted `L²` input. -/
theorem laguerre_heat_time_laplace_operator (α : ℝ) (hα : 0 < α)
    (f : LaguerreWeightedHilbert) :
    (∫ τ : Ioi (0 : ℝ),
      (((τ : ℝ) * Real.exp (-α * (τ : ℝ))) : ℂ) •
        laguerreHeatOperator (τ : ℝ) τ.property.le f) =
      laguerreSquaredResolvent α hα f := by
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext n
  rw [laguerre_squared_resolvent_coordinate,
    laguerreHilbertBasis.repr_apply_apply]
  have hin := ((innerSL ℂ (laguerreHilbertBasis n)).integral_comp_comm
    (laguerre_heat_time_laplace_integrable α hα f))
  change (∫ τ : Ioi (0 : ℝ),
      @inner ℂ LaguerreWeightedHilbert _ (laguerreHilbertBasis n)
        ((((τ : ℝ) * Real.exp (-α * (τ : ℝ))) : ℂ) •
          laguerreHeatOperator (τ : ℝ) τ.property.le f)) =
    @inner ℂ LaguerreWeightedHilbert _ (laguerreHilbertBasis n)
      (∫ τ : Ioi (0 : ℝ),
        (((τ : ℝ) * Real.exp (-α * (τ : ℝ))) : ℂ) •
          laguerreHeatOperator (τ : ℝ) τ.property.le f) at hin
  rw [← hin]
  have hpoint (τ : Ioi (0 : ℝ)) :
      @inner ℂ LaguerreWeightedHilbert _ (laguerreHilbertBasis n)
        ((((τ : ℝ) * Real.exp (-α * (τ : ℝ))) : ℂ) •
          laguerreHeatOperator (τ : ℝ) τ.property.le f) =
        (((τ : ℝ) * Real.exp (-(((n : ℝ) + α) * (τ : ℝ)))) : ℂ) *
          laguerreHilbertBasis.repr f n := by
    rw [inner_smul_right, ← laguerreHilbertBasis.repr_apply_apply,
      laguerre_heat_coordinate, ← mul_assoc]
    congr 1
    norm_cast
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hpoint]
  rw [integral_mul_right, laguerre_heat_time_laplace_complex_coefficient α hα n]
  push_cast
  ring

end
end Sigma
