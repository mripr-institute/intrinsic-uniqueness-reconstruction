import SigmaOpGammaAlternativeRecipe
import SigmaOpNonnegativeMixing
import SigmaProbGammaBetaDensity

namespace Sigma
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The genuine Gamma(a,1) law gives full mass to positive heat times. -/
theorem alternative_gamma_positive_ae (a : ℝ) :
    ∀ᵐ t ∂alternativeGammaMixingMeasure a, 0 < t := by
  rw [alternativeGammaMixingMeasure, gamma_beta_gamma_measure]
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem measurableSet_Ioi)

theorem alternative_gamma_positive_subtype_integral (a : ℝ) (f : ℝ → ℝ) :
    (∫ t : Ioi (0 : ℝ), f t.val
      ∂(Measure.comap Subtype.val (alternativeGammaMixingMeasure a))) =
      ∫ t : ℝ, f t ∂alternativeGammaMixingMeasure a := by
  rw [integral_subtype_comap measurableSet_Ioi]
  change (∫ t : ℝ, f t ∂(alternativeGammaMixingMeasure a).restrict (Ioi 0)) = _
  exact congrArg (fun ρ : Measure ℝ => ∫ t : ℝ, f t ∂ρ)
    (Measure.restrict_eq_self_of_ae_mem (alternative_gamma_positive_ae a))

/-- The Gamma(a,1) heat average of each compactified spectral value is
exactly the alternative resolvent power, including the zero endpoint. -/
theorem alternative_gamma_heat_scalar_integral (a r : ℝ) (ha : 0 < a)
    (hr : r ∈ Icc (0 : ℝ) 1) :
    (∫ t : Ioi (0 : ℝ), resolventHeatScalar t.val r
      ∂(Measure.comap Subtype.val (alternativeGammaMixingMeasure a))) =
      r ^ a := by
  calc
    (∫ t : Ioi (0 : ℝ), resolventHeatScalar t.val r
      ∂(Measure.comap Subtype.val (alternativeGammaMixingMeasure a))) =
        ∫ t : ℝ, resolventHeatScalar t r ∂alternativeGammaMixingMeasure a :=
      alternative_gamma_positive_subtype_integral a (fun t => resolventHeatScalar t r)
    _ = r ^ a := by
      rcases hr.1.eq_or_lt with hzero | hpos
      · rw [← hzero]
        simp [resolvent_heat_scalar_zero, ha.ne']
      · have hb : 0 ≤ r⁻¹ - 1 := sub_nonneg.mpr ((one_le_inv₀ hpos).mpr hr.2)
        have he : (fun t : ℝ => resolventHeatScalar t r) =ᵐ[alternativeGammaMixingMeasure a]
            (fun t => Real.exp (-((r⁻¹ - 1) * t))) := by
          filter_upwards [alternative_gamma_positive_ae a] with t ht
          rw [resolvent_heat_scalar_eq ht hpos]
          congr 1
          ring
        rw [integral_congr_ae he, alternative_gamma_laplace a (r⁻¹ - 1) ha hb]
        rw [show 1 + (r⁻¹ - 1) = r⁻¹ by ring,
          Real.rpow_neg (inv_nonneg.mpr hpos.le), Real.inv_rpow hpos.le, inv_inv]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The alternative Gamma recipe is an actual norm-convergent operator
integral for every positive exponent and every nonnegative native operator. -/
theorem resolvent_heat_alternative_gamma_integral (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    (a : ℝ) (ha : 0 < a) :
    (∫ t : Ioi (0 : ℝ), resolventHeatOperator R t.val
      ∂(Measure.comap Subtype.val (alternativeGammaMixingMeasure a))) =
      cfc (fun r : ℝ => r ^ a) R := by
  letI : IsProbabilityMeasure (alternativeGammaMixingMeasure a) :=
    alternative_gamma_probability a ha
  letI : CompactSpace (spectrum ℝ R) :=
    ContinuousFunctionalCalculus.compactSpace_spectrum (p := IsSelfAdjoint) R
  letI : SecondCountableTopologyEither (Ioi (0 : ℝ))
      C(spectrum ℝ R, ℝ) := ⟨Or.inl inferInstance⟩
  have hc : Continuous (fun p : Ioi (0 : ℝ) × spectrum ℝ R =>
      resolventHeatScalar p.1.val p.2.val) := by
    have ht : Continuous (fun p : Ioi (0 : ℝ) × spectrum ℝ R => p.1.val) :=
      continuous_subtype_val.comp continuous_fst
    have hr : Continuous (fun p : Ioi (0 : ℝ) × spectrum ℝ R => p.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact ht.rexp.mul ((expNegInvGlue.contDiff (n := 0)).continuous.comp
      (hr.div ht (fun p => ne_of_gt p.1.property)))
  have hb (t : Ioi (0 : ℝ)) (r : ℝ) (hr : r ∈ spectrum ℝ R) :
      ‖resolventHeatScalar t.val r‖ ≤ ‖(1 : ℝ)‖ := by
    rw [Real.norm_of_nonneg (resolvent_heat_scalar_nonneg _ _), norm_one]
    exact resolvent_heat_scalar_le_one t.property (hσ hr)
  have hfin : HasFiniteIntegral (fun _ : Ioi (0 : ℝ) => (1 : ℝ))
      (Measure.comap Subtype.val (alternativeGammaMixingMeasure a)) :=
    (integrable_const (1 : ℝ)).hasFiniteIntegral
  have hi := cfc_integral' (μ := Measure.comap Subtype.val
      (alternativeGammaMixingMeasure a))
    (fun t : Ioi (0 : ℝ) => resolventHeatScalar t.val)
    (fun _ => (1 : ℝ)) R hc hb hfin hR
  have hscalar : cfc (fun r : ℝ =>
      ∫ t : Ioi (0 : ℝ), resolventHeatScalar t.val r
        ∂(Measure.comap Subtype.val (alternativeGammaMixingMeasure a))) R =
      cfc (fun r : ℝ => r ^ a) R := by
    apply cfc_congr
    intro r hr
    exact alternative_gamma_heat_scalar_integral a r ha (hσ hr)
  calc
    (∫ t : Ioi (0 : ℝ), resolventHeatOperator R t.val
      ∂(Measure.comap Subtype.val (alternativeGammaMixingMeasure a))) =
        ∫ t : Ioi (0 : ℝ), cfc (resolventHeatScalar t.val) R
          ∂(Measure.comap Subtype.val (alternativeGammaMixingMeasure a)) := by
      apply integral_congr_ae
      filter_upwards with t
      change (if 0 < t.val then cfc (resolventHeatScalar t.val) R else 1) = _
      exact if_pos t.property
    _ = cfc (fun r : ℝ =>
        ∫ t : Ioi (0 : ℝ), resolventHeatScalar t.val r
          ∂(Measure.comap Subtype.val (alternativeGammaMixingMeasure a))) R := hi.symm
    _ = cfc (fun r : ℝ => r ^ a) R := hscalar

/-- The literal alternative mixing equation for an arbitrary nonnegative
self-adjoint operator, expressed through its actual shift resolvent. -/
theorem op_nonnegative_alternative_gamma_mixing (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B)
    (a : ℝ) (ha : 0 < a) :
    (∫ t : Ioi (0 : ℝ), opNonnegativeHeat B hsa hB t.val
      ∂(Measure.comap Subtype.val (alternativeGammaMixingMeasure a))) =
      cfc (fun r : ℝ => r ^ a) (opNonnegativeResolvent B hsa hB) :=
  resolvent_heat_alternative_gamma_integral
    (opNonnegativeResolvent B hsa hB)
    (op_nonnegative_resolvent_selfAdjoint B hsa hB)
    (op_nonnegative_resolvent_spectrum B hsa hB) a ha

end
end Sigma
