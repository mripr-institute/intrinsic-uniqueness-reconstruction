import SigmaOpEndpointFlux

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The second actual zero-energy solution, normalized to vanish at one. -/
def laguerreSecondZeroSolution (t : ℝ) : ℂ :=
  ∫ s in (1:ℝ)..t, (steinFlux s : ℂ)⁻¹

theorem inverse_flux_continuousOn : ContinuousOn (fun t => (steinFlux t : ℂ)⁻¹) (Ioi 0) :=
  (Complex.continuous_ofReal.comp steinFlux_contDiff.continuous).continuousOn.inv₀
    (fun _ ht => stein_flux_ne_zero ht)

theorem laguerre_second_zero_locally_ac :
    PositiveRayLocallyAbsolutelyContinuous laguerreSecondZeroSolution := by
  intro l r hl ε hε
  exact positive_primitive_absolute_continuity _
    (inverse_flux_continuousOn.locallyIntegrableOn measurableSet_Ioi) (by norm_num) hl ε hε

theorem laguerre_second_zero_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt laguerreSecondZeroSolution (steinFlux t : ℂ)⁻¹ t := by
  apply laguerre_second_zero_locally_ac.hasDerivAt_of_ae_continuous inverse_flux_continuousOn _ ht
  exact positive_primitive_hasDerivAt_ae _
    (inverse_flux_continuousOn.locallyIntegrableOn measurableSet_Ioi) (by norm_num)

theorem laguerre_second_zero_flux {t : ℝ} (ht : 0 < t) :
    (steinFlux t : ℂ)*deriv laguerreSecondZeroSolution t = 1 := by
  rw [(laguerre_second_zero_hasDerivAt ht).deriv,mul_inv_cancel₀ (stein_flux_ne_zero ht)]

theorem laguerre_second_zero_flux_locally_ac :
    PositiveRayLocallyAbsolutelyContinuous
      (fun t => (steinFlux t : ℂ)*deriv laguerreSecondZeroSolution t) :=
  (smooth_positive_locally_ac (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (1:ℂ)))).congr
    (fun _ ht => laguerre_second_zero_flux ht)

theorem laguerre_second_zero_divergence {t : ℝ} (ht : 0 < t) :
    laguerreDivergenceExpression laguerreSecondZeroSolution t = 0 := by
  have he : (fun t => (steinFlux t : ℂ)*deriv laguerreSecondZeroSolution t) =ᶠ[𝓝 t]
      (fun _ => (1:ℂ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact laguerre_second_zero_flux hs
  simp only [laguerreDivergenceExpression,he.deriv_eq,(hasDerivAt_const t (1:ℂ)).deriv,mul_zero]

/-- A classical zero-energy solution is determined by two constants; this is
a genuine fundamental system rather than just two displayed example functions. -/
theorem laguerre_zero_solution_fundamental_system (F : ℝ → ℂ)
    (hF : PositiveRayLocallyAbsolutelyContinuous F)
    (hQ : PositiveRayLocallyAbsolutelyContinuous (fun t => (steinFlux t : ℂ)*deriv F t))
    (hz : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), laguerreDivergenceExpression F t = 0) :
    ∃ a b : ℂ, EqOn F (fun t => a+b*laguerreSecondZeroSolution t) (Ioi 0) := by
  let Q : ℝ → ℂ := fun t => (steinFlux t : ℂ)*deriv F t
  have hQd : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), HasDerivAt Q 0 t := by
    filter_upwards [hQ.ae_differentiableAt,hz,ae_restrict_mem measurableSet_Ioi] with t ht hzt hp
    have hp0 : (SigmaPresentations.density t : ℂ) ≠ 0 := by
      have he : 0 < SigmaPresentations.density t := mul_pos hp (Real.exp_pos _)
      exact_mod_cast he.ne'
    have hd : deriv Q t=0 := by
      change -(SigmaPresentations.density t : ℂ)⁻¹*deriv Q t=0 at hzt
      exact (mul_eq_zero.mp hzt).resolve_left (neg_ne_zero.mpr (inv_ne_zero hp0))
    exact hd ▸ ht.hasDerivAt
  have hconst {t : ℝ} (ht : 0 < t) : Q t=Q 1 := by
    have he := hQ.integral_eq_sub (g := fun _ => 0)
      (continuous_const.continuousOn.locallyIntegrableOn measurableSet_Ioi) hQd
      (by norm_num : (0:ℝ)<1) ht
    rw [intervalIntegral.integral_zero] at he
    exact sub_eq_zero.mp he.symm
  let D : ℝ → ℂ := fun t => F t-Q 1*laguerreSecondZeroSolution t
  have hD : PositiveRayLocallyAbsolutelyContinuous D := hF.sub
    ((smooth_positive_locally_ac (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => Q 1))).mul
      laguerre_second_zero_locally_ac)
  have hDd : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), HasDerivAt D 0 t := by
    filter_upwards [hF.ae_differentiableAt,ae_restrict_mem measurableSet_Ioi] with t ht hp
    have he : deriv F t-Q 1*(steinFlux t : ℂ)⁻¹=0 := by
      rw [← hconst hp]
      dsimp [Q]
      field_simp [stein_flux_ne_zero hp]
    simpa only [he] using ht.hasDerivAt.sub ((laguerre_second_zero_hasDerivAt hp).const_mul (Q 1))
  refine ⟨F 1,Q 1,?_⟩
  intro t ht
  have he := hD.integral_eq_sub (g := fun _ => 0)
    (continuous_const.continuousOn.locallyIntegrableOn measurableSet_Ioi) hDd
    (by norm_num : (0:ℝ)<1) ht
  simp only [intervalIntegral.integral_zero,D,laguerreSecondZeroSolution,intervalIntegral.integral_same,
    mul_zero,sub_zero] at he
  change F t=F 1+Q 1*laguerreSecondZeroSolution t
  dsimp [laguerreSecondZeroSolution]
  linear_combination -he

end
end Sigma
