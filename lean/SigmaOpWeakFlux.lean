import SigmaOpWeakPrimitive
import SigmaOpSobolevDomain

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem gamma_l2_locally_integrableOn (x : LaguerreWeightedHilbert) :
    LocallyIntegrableOn (x : ℝ → ℂ) (Ioi 0) volume := by
  intro t ht
  change 0 < t at ht
  refine ⟨Icc (t/2) (t+1),?_,gamma_l2_locally_integrable x (by linarith)⟩
  apply mem_nhdsWithin_of_mem_nhds
  exact Icc_mem_nhds (by linarith) (by linarith)

theorem complex_locally_integrable_conj {g : ℝ → ℂ}
    (hg : LocallyIntegrableOn g (Ioi 0) volume) :
    LocallyIntegrableOn (fun t => starRingEnd ℂ (g t)) (Ioi 0) volume := by
  intro t ht
  obtain ⟨s,hs,hi⟩ := hg t ht
  exact ⟨s,hs,Complex.conjCLE.toContinuousLinearMap.integrable_comp hi⟩

theorem l2_compact_pairing_density (x : LaguerreWeightedHilbert)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi 0) :
    @inner ℂ LaguerreWeightedHilbert _ x (smoothCompactL2Vector f hf hs) =
      ∫ t : ℝ, (SigmaPresentations.density t : ℂ)*starRingEnd ℂ (x t)*f t := by
  rw [L2.inner_def]
  have he : (fun t => @inner ℂ ℂ _ (x t) (smoothCompactL2Vector f hf hs t)) =ᵐ[gammaProbability]
      (fun t => starRingEnd ℂ (x t)*f t) := by
    filter_upwards [smooth_compact_l2_coe f hf hs] with t ht
    simp only [RCLike.inner_apply,ht]
  rw [integral_congr_ae he,gamma_probability_complex_integral]
  simp_rw [← mul_assoc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  rw [image_eq_zero_of_nmem_tsupport (fun h => ht (hp h)),mul_zero]

theorem finite_energy_gradient_inner_compact (F : ℝ → ℂ)
    (henergy : IntegrableOn (fun t => steinFlux t*‖deriv F t‖^2) (Ioi 0) volume)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi 0) :
    @inner ℂ LaguerreWeightedHilbert _ (finiteEnergyGradient F henergy)
      (smoothCompactGradient f hf hs) =
      ∫ t : ℝ, (steinFlux t : ℂ)*starRingEnd ℂ (deriv F t)*deriv f t := by
  rw [L2.inner_def]
  have he : (fun t => @inner ℂ ℂ _ (finiteEnergyGradient F henergy t)
      (smoothCompactGradient f hf hs t)) =ᵐ[gammaProbability]
      (fun t => starRingEnd ℂ (weightedTestDerivative F t)*weightedTestDerivative f t) := by
    filter_upwards [finite_energy_gradient_coe F henergy,smooth_compact_gradient_coe f hf hs]
      with t hFt hft
    simp only [RCLike.inner_apply,hFt,hft]
  rw [integral_congr_ae he,gamma_probability_complex_integral]
  have heq : (∫ t : ℝ in Ioi 0, (SigmaPresentations.density t : ℂ)*
      (starRingEnd ℂ (weightedTestDerivative F t)*weightedTestDerivative f t)) =
      ∫ t : ℝ in Ioi 0, (steinFlux t : ℂ)*starRingEnd ℂ (deriv F t)*deriv f t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hsq : (Real.sqrt t : ℂ)^2 = (t : ℂ) := by
      rw [← Complex.ofReal_pow,Real.sq_sqrt ht.le]
    simp only [weightedTestDerivative,map_mul,Complex.conj_ofReal]
    calc
      _ = (SigmaPresentations.density t : ℂ)*(Real.sqrt t : ℂ)^2 *
          starRingEnd ℂ (deriv F t)*deriv f t := by ring
      _ = _ := by
        rw [hsq]
        simp only [steinFlux,SigmaPresentations.density,Complex.ofReal_mul,Complex.ofReal_pow]
        ring
  rw [heq]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have hd : deriv f t = 0 := not_not.mp (fun h => ht (hp (support_deriv_subset h)))
  rw [hd,mul_zero]

/-- The actual operator equation supplies the distributional equation for the
conjugated flux, with no regularity assumption on the operator image. -/
theorem laguerre_operator_weak_flux
    (x : (laguerreSpectralOperator id).domain) (F : ℝ → ℂ)
    (hFx : F =ᵐ[gammaProbability] (x.val : ℝ → ℂ))
    (hF : PositiveRayLocallyAbsolutelyContinuous F)
    (henergy : IntegrableOn (fun t => steinFlux t*‖deriv F t‖^2) (Ioi 0) volume)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi 0) :
    (∫ t : ℝ, ((steinFlux t : ℂ)*starRingEnd ℂ (deriv F t))*deriv f t) +
      (∫ t : ℝ, (-(SigmaPresentations.density t : ℂ)*
        starRingEnd ℂ (laguerreSpectralOperator id x t))*f t) = 0 := by
  have he := laguerre_spectral_formal_adjoint id x
    ⟨smoothCompactL2Vector f hf hs,smooth_compact_mem_laguerre_domain f hf hs⟩
  rw [laguerre_spectral_extends_differential_test,
    finite_energy_ac_compact_gradient_pairing x.val F hFx hF henergy f hf hs hp,
    l2_compact_pairing_density _ f hf hs hp,
    finite_energy_gradient_inner_compact F henergy f hf hs hp] at he
  simp_rw [neg_mul,integral_neg]
  linear_combination -he


/-- Every vector in the full operator domain has a genuine locally AC flux
representative satisfying the divergence equation almost everywhere. -/
theorem laguerre_operator_regular_flux
    (x : (laguerreSpectralOperator id).domain) (F : ℝ → ℂ)
    (hFx : F =ᵐ[gammaProbability] (x.val : ℝ → ℂ))
    (hF : PositiveRayLocallyAbsolutelyContinuous F)
    (henergy : IntegrableOn (fun t => steinFlux t*‖deriv F t‖^2) (Ioi 0) volume) :
    ∃ Q : ℝ → ℂ, PositiveRayLocallyAbsolutelyContinuous Q ∧
      Q =ᵐ[volume.restrict (Ioi 0)] (fun t => (steinFlux t : ℂ)*deriv F t) ∧
      ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
        HasDerivAt Q (-(SigmaPresentations.density t : ℂ)*laguerreSpectralOperator id x t) t := by
  have hq : Continuous (fun t => (steinFlux t : ℂ)) :=
    Complex.continuous_ofReal.comp steinFlux_contDiff.continuous
  have hp : Continuous (fun t => (SigmaPresentations.density t : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_id.mul continuous_id.neg.rexp)
  have hu : LocallyIntegrableOn (fun t => (steinFlux t : ℂ)*starRingEnd ℂ (deriv F t))
      (Ioi 0) volume :=
    (complex_locally_integrable_conj (finite_energy_derivative_locally_integrable F henergy)).continuousOn_mul
      hq.continuousOn isOpen_Ioi.isLocallyClosed
  have hg : LocallyIntegrableOn (fun t => -(SigmaPresentations.density t : ℂ)*
      starRingEnd ℂ (laguerreSpectralOperator id x t)) (Ioi 0) volume :=
    (complex_locally_integrable_conj (gamma_l2_locally_integrableOn (laguerreSpectralOperator id x))).continuousOn_mul
      hp.neg.continuousOn isOpen_Ioi.isLocallyClosed
  obtain ⟨U,hU,hUc,hUd⟩ := complex_weak_derivative_regular_representative _ _ hu hg
    (laguerre_operator_weak_flux x F hFx hF henergy)
  refine ⟨fun t => starRingEnd ℂ (U t),hUc.conj,?_,?_⟩
  · filter_upwards [hU] with t ht
    simp only [ht,map_mul,Complex.conj_ofReal,starRingEnd_self_apply]
  · filter_upwards [hUd] with t ht
    have he := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t ht
    change HasDerivAt (fun t => starRingEnd ℂ (U t))
      (starRingEnd ℂ (-(SigmaPresentations.density t : ℂ)*starRingEnd ℂ (laguerreSpectralOperator id x t))) t at he
    simpa only [map_mul,map_neg,
      Complex.conj_ofReal,starRingEnd_self_apply] using he

end
end Sigma
