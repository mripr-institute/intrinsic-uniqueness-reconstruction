import SigmaOpWeakFlux

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- Continuity of an a.e. derivative upgrades a literal AC function to an
everywhere differentiable function on the positive ray. -/
theorem PositiveRayLocallyAbsolutelyContinuous.hasDerivAt_of_ae_continuous
    {F g : ℝ → ℂ} (hF : PositiveRayLocallyAbsolutelyContinuous F)
    (hg : ContinuousOn g (Ioi 0))
    (hd : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), HasDerivAt F (g t) t)
    {t : ℝ} (ht : 0 < t) : HasDerivAt F (g t) t := by
  have hgl : LocallyIntegrableOn g (Ioi 0) volume := hg.locallyIntegrableOn measurableSet_Ioi
  have hp := intervalIntegral.integral_hasDerivAt_right
    (positive_locally_integrable_interval g hgl (by norm_num : (0:ℝ)<1) ht)
    (show StronglyMeasurableAtFilter g (𝓝 t) volume from
      ⟨Ioi 0,isOpen_Ioi.mem_nhds ht,hg.aestronglyMeasurable measurableSet_Ioi⟩)
    (hg.continuousAt (isOpen_Ioi.mem_nhds ht))
  apply (hp.const_add (F 1)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  have he := hF.integral_eq_sub hgl hd (by norm_num : (0:ℝ)<1) hs
  linear_combination -he

theorem stein_flux_ne_zero {t : ℝ} (ht : 0 < t) : (steinFlux t : ℂ) ≠ 0 := by
  have hq : 0 < steinFlux t := by dsimp [steinFlux]; positivity
  exact_mod_cast hq.ne'

/-- The flux representative is the literal classical flux at every positive
point: the weak equation upgrades F to C1 in the interior. -/
theorem laguerre_operator_classical_flux
    (x : (laguerreSpectralOperator id).domain) (F : ℝ → ℂ)
    (hFx : F =ᵐ[gammaProbability] (x.val : ℝ → ℂ))
    (hF : PositiveRayLocallyAbsolutelyContinuous F)
    (henergy : IntegrableOn (fun t => steinFlux t*‖deriv F t‖^2) (Ioi 0) volume) :
    PositiveRayLocallyAbsolutelyContinuous (fun t => (steinFlux t : ℂ)*deriv F t) ∧
      ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
        HasDerivAt (fun t => (steinFlux t : ℂ)*deriv F t)
          (-(SigmaPresentations.density t : ℂ)*laguerreSpectralOperator id x t) t := by
  obtain ⟨Q,hQc,hQ,hQd⟩ := laguerre_operator_regular_flux x F hFx hF henergy
  let g : ℝ → ℂ := fun t => Q t/(steinFlux t : ℂ)
  have hgc : ContinuousOn g (Ioi 0) := hQc.continuousOn.div
    (Complex.continuous_ofReal.comp steinFlux_contDiff.continuous).continuousOn
    (fun _ ht => stein_flux_ne_zero ht)
  have hgd : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), HasDerivAt F (g t) t := by
    filter_upwards [hF.ae_differentiableAt,hQ,ae_restrict_mem measurableSet_Ioi] with t hFt hQt ht
    have he : g t = deriv F t := by
      dsimp only [g]
      rw [hQt,mul_div_cancel_left₀ _ (stein_flux_ne_zero ht)]
    rw [he]
    exact hFt.hasDerivAt
  have hpoint : EqOn (fun t => (steinFlux t : ℂ)*deriv F t) Q (Ioi 0) := by
    intro t ht
    dsimp only
    rw [(hF.hasDerivAt_of_ae_continuous hgc hgd ht).deriv]
    dsimp only [g]
    rw [mul_div_cancel₀ _ (stein_flux_ne_zero ht)]
  refine ⟨hQc.congr hpoint,?_⟩
  filter_upwards [hQd,ae_restrict_mem measurableSet_Ioi] with t hQt ht
  apply hQt.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  exact hpoint hs

def laguerreDivergenceExpression (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  -(SigmaPresentations.density t : ℂ)⁻¹ * deriv (fun t => (steinFlux t : ℂ)*deriv F t) t

/-- The full operator domain supplies the exact maximal-domain regularity and
literal divergence expression, with the operator image as its L2 representative. -/
theorem laguerre_operator_maximal_representative
    (x : (laguerreSpectralOperator id).domain) :
    ∃ F : ℝ → ℂ, F =ᵐ[gammaProbability] (x.val : ℝ → ℂ) ∧
      PositiveRayLocallyAbsolutelyContinuous F ∧
      PositiveRayLocallyAbsolutelyContinuous (fun t => (steinFlux t : ℂ)*deriv F t) ∧
      laguerreDivergenceExpression F =ᵐ[gammaProbability]
        (laguerreSpectralOperator id x : ℝ → ℂ) := by
  obtain ⟨F,hFx,hF,henergy,_⟩ := laguerre_square_root_regular_representative
    ⟨x.val,laguerre_integer_domain_le_square_root x.property⟩
  obtain ⟨hQ,hQd⟩ := laguerre_operator_classical_flux x F hFx hF henergy
  refine ⟨F,hFx,hF,hQ,gamma_ae_iff_positive_volume_ae.mpr ?_⟩
  filter_upwards [hQd,ae_restrict_mem measurableSet_Ioi] with t hQt ht
  have hp : (SigmaPresentations.density t : ℂ) ≠ 0 := by
    have hp' : 0 < SigmaPresentations.density t := mul_pos ht (Real.exp_pos _)
    exact_mod_cast hp'.ne'
  simp only [laguerreDivergenceExpression,hQt.deriv,neg_mul_neg]
  field_simp

end
end Sigma
