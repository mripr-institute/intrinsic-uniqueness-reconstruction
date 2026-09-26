import SigmaOpACIntegrationByParts

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem finite_energy_ac_compact_gradient_pairing
    (x : LaguerreWeightedHilbert) (F : ℝ → ℂ)
    (hFx : F =ᵐ[gammaProbability] (x : ℝ → ℂ))
    (hF : PositiveRayLocallyAbsolutelyContinuous F)
    (henergy : IntegrableOn (fun t => steinFlux t * ‖deriv F t‖^2) (Ioi 0) volume)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi 0) :
    @inner ℂ LaguerreWeightedHilbert _ x (smoothCompactL2Image f hf hs) =
      @inner ℂ LaguerreWeightedHilbert _ (finiteEnergyGradient F henergy)
        (smoothCompactGradient f hf hs) := by
  have hfd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hfs : tsupport (deriv f) ⊆ tsupport f := closure_minimal support_deriv_subset isClosed_closure
  let w : ℝ → ℂ := fun t => (steinFlux t : ℂ)*deriv f t
  have hw : ContDiff ℝ ∞ w := (Complex.ofRealCLM.contDiff.comp steinFlux_contDiff).mul hfd
  have hws : HasCompactSupport w := hs.deriv.mul_left
  have hwp : tsupport w ⊆ Ioi 0 := tsupport_mul_subset_right.trans (hfs.trans hp)
  have hdw (t : ℝ) : deriv w t =
      -(SigmaPresentations.density t : ℂ)*opComplexLaguerreExpression f t := by
    have hd : HasDerivAt w
        (((2-t)*SigmaPresentations.density t : ℝ)*deriv f t +
          (steinFlux t : ℂ)*deriv (deriv f) t) t := by
      simpa only [Function.comp_apply] using
        (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (steinFlux_hasDerivAt t)).mul
          ((hfd.differentiable (by simp) t).hasDerivAt)
    rw [hd.deriv]
    simp only [opComplexLaguerreExpression,steinFlux,SigmaPresentations.density,
      Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_pow,Complex.ofReal_ofNat]
    ring
  have hgl : LocallyIntegrableOn (fun t => starRingEnd ℂ (deriv F t)) (Ioi 0) volume := by
    intro t ht
    obtain ⟨s,hs,hi⟩ := finite_energy_derivative_locally_integrable F henergy t ht
    exact ⟨s,hs,Complex.conjCLE.toContinuousLinearMap.integrable_comp hi⟩
  have hgd : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      HasDerivAt (fun t => starRingEnd ℂ (F t)) (starRingEnd ℂ (deriv F t)) t := by
    filter_upwards [hF.ae_differentiableAt] with t ht
    exact Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t ht.hasDerivAt
  have hibp := hF.conj.compact_integration_by_parts hgl hgd w hw hws hwp
  have hsupp (t : ℝ) (ht : t ∉ Ioi (0:ℝ)) : w t = 0 ∧ deriv w t = 0 := by
    have hn : t ∉ tsupport w := fun h => ht (hwp h)
    exact ⟨image_eq_zero_of_nmem_tsupport hn,not_not.mp (fun hh => hn (support_deriv_subset hh))⟩
  have he : (∫ t : ℝ in Ioi 0, starRingEnd ℂ (deriv F t)*w t) +
      (∫ t : ℝ in Ioi 0, starRingEnd ℂ (F t)*deriv w t) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht => by rw [(hsupp t ht).1,mul_zero]),
      setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht => by rw [(hsupp t ht).2,mul_zero])]
    exact hibp
  have hleft : @inner ℂ LaguerreWeightedHilbert _ x (smoothCompactL2Image f hf hs) =
      -(∫ t : ℝ in Ioi 0, starRingEnd ℂ (F t)*deriv w t) := by
    rw [L2.inner_def]
    have heq : (fun t => @inner ℂ ℂ _ (x t) (smoothCompactL2Image f hf hs t)) =ᵐ[gammaProbability]
        (fun t => starRingEnd ℂ (F t)*opComplexLaguerreExpression f t) := by
      filter_upwards [hFx,smooth_compact_image_coe f hf hs] with t hft hit
      simp only [RCLike.inner_apply,← hft,hit]
    rw [integral_congr_ae heq,gamma_probability_complex_integral,← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [hdw]
    ring
  have hright : @inner ℂ LaguerreWeightedHilbert _ (finiteEnergyGradient F henergy)
      (smoothCompactGradient f hf hs) =
      ∫ t : ℝ in Ioi 0, starRingEnd ℂ (deriv F t)*w t := by
    rw [L2.inner_def]
    have heq : (fun t => @inner ℂ ℂ _ (finiteEnergyGradient F henergy t)
        (smoothCompactGradient f hf hs t)) =ᵐ[gammaProbability]
        (fun t => starRingEnd ℂ (weightedTestDerivative F t)*weightedTestDerivative f t) := by
      filter_upwards [finite_energy_gradient_coe F henergy,smooth_compact_gradient_coe f hf hs]
        with t hFt hft
      simp only [RCLike.inner_apply,hFt,hft]
    rw [integral_congr_ae heq,gamma_probability_complex_integral]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hsq : (Real.sqrt t : ℂ)^2 = (t : ℂ) := by
      rw [← Complex.ofReal_pow,Real.sq_sqrt ht.le]
    simp only [weightedTestDerivative,map_mul,Complex.conj_ofReal,w]
    calc
      _ = (SigmaPresentations.density t : ℂ)*(Real.sqrt t : ℂ)^2 *
          starRingEnd ℂ (deriv F t)*deriv f t := by ring
      _ = _ := by
        rw [hsq]
        simp only [steinFlux,SigmaPresentations.density,Complex.ofReal_mul,Complex.ofReal_pow]
        ring
  rw [hleft,hright]
  linear_combination -he

/-- Every finite-energy locally absolutely continuous representative belongs
to the actual square-root domain. There are no endpoint trace assumptions. -/
theorem laguerre_square_root_mem_of_ac_finite_energy
    (x : LaguerreWeightedHilbert) (F : ℝ → ℂ)
    (hFx : F =ᵐ[gammaProbability] (x : ℝ → ℂ))
    (hF : PositiveRayLocallyAbsolutelyContinuous F)
    (henergy : IntegrableOn (fun t => steinFlux t * ‖deriv F t‖^2) (Ioi 0) volume) :
    x ∈ (laguerreSpectralOperator Real.sqrt).domain := by
  apply laguerre_square_root_mem_of_compact_gradient_pairing x (finiteEnergyGradient F henergy)
  exact finite_energy_ac_compact_gradient_pairing x F hFx hF henergy

/-- The exact weighted Sobolev description of the square-root domain, with
literal local absolute continuity and no condition at either endpoint. -/
theorem laguerre_square_root_domain_iff_ac_finite_energy (x : LaguerreWeightedHilbert) :
    x ∈ (laguerreSpectralOperator Real.sqrt).domain ↔
      ∃ F : ℝ → ℂ, F =ᵐ[gammaProbability] (x : ℝ → ℂ) ∧
        PositiveRayLocallyAbsolutelyContinuous F ∧
        IntegrableOn (fun t => steinFlux t * ‖deriv F t‖^2) (Ioi 0) volume := by
  constructor
  · intro hx
    obtain ⟨F,hFx,hF,he,_⟩ := laguerre_square_root_regular_representative ⟨x,hx⟩
    exact ⟨F,hFx,hF,he⟩
  · rintro ⟨F,hFx,hF,he⟩
    exact laguerre_square_root_mem_of_ac_finite_energy x F hFx hF he

end
end Sigma
