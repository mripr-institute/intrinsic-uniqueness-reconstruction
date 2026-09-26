import SigmaOpClassicalFlux

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem op_complex_laguerre_expression_tsupport (f : ℝ → ℂ) :
    tsupport (opComplexLaguerreExpression f) ⊆ tsupport f := by
  have hd : tsupport (deriv f) ⊆ tsupport f := closure_minimal support_deriv_subset isClosed_closure
  apply closure_minimal ?_ isClosed_closure
  intro t ht
  by_contra hn
  have hdf : deriv f t = 0 := not_not.mp (fun h => hn (support_deriv_subset h))
  have hddf : deriv (deriv f) t = 0 :=
    not_not.mp (fun h => hn (hd (support_deriv_subset h)))
  exact ht (by simp [opComplexLaguerreExpression,hdf,hddf])

theorem complex_flux_test_derivative (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    deriv (fun t => (steinFlux t : ℂ)*deriv f t) t =
      -(SigmaPresentations.density t : ℂ)*opComplexLaguerreExpression f t := by
  have hfd := (contDiff_infty_iff_deriv.mp hf).2
  have hd : HasDerivAt (fun t => (steinFlux t : ℂ)*deriv f t)
      (((2-t)*SigmaPresentations.density t : ℝ)*deriv f t +
        (steinFlux t : ℂ)*deriv (deriv f) t) t := by
    simpa only [Function.comp_apply] using
      (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (steinFlux_hasDerivAt t)).mul
        ((hfd.differentiable (by simp) t).hasDerivAt)
  rw [hd.deriv]
  simp only [opComplexLaguerreExpression,steinFlux,SigmaPresentations.density,
    Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_pow,Complex.ofReal_ofNat]
  ring

theorem continuous_derivative_of_ac_flux {F : ℝ → ℂ}
    (hQ : PositiveRayLocallyAbsolutelyContinuous (fun t => (steinFlux t : ℂ)*deriv F t)) :
    ContinuousOn (deriv F) (Ioi 0) := by
  have hc := hQ.continuousOn.div
    (Complex.continuous_ofReal.comp steinFlux_contDiff.continuous).continuousOn
    (fun _ ht => stein_flux_ne_zero ht)
  apply hc.congr
  intro t ht
  exact (mul_div_cancel_left₀ (deriv F t) (stein_flux_ne_zero ht)).symm

/-- Literal maximal-domain hypotheses imply the adjoint test pairing. No
energy or boundary condition is imposed on the input. -/
theorem laguerre_maximal_compact_pairing
    (x y : LaguerreWeightedHilbert) (F : ℝ → ℂ)
    (hFx : F =ᵐ[gammaProbability] (x : ℝ → ℂ))
    (hF : PositiveRayLocallyAbsolutelyContinuous F)
    (hQ : PositiveRayLocallyAbsolutelyContinuous (fun t => (steinFlux t : ℂ)*deriv F t))
    (hy : laguerreDivergenceExpression F =ᵐ[gammaProbability] (y : ℝ → ℂ))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi 0) :
    @inner ℂ LaguerreWeightedHilbert _ y (smoothCompactL2Vector f hf hs) =
      @inner ℂ LaguerreWeightedHilbert _ x (smoothCompactL2Image f hf hs) := by
  let Q : ℝ → ℂ := fun t => (steinFlux t : ℂ)*deriv F t
  have hFl : LocallyIntegrableOn (deriv F) (Ioi 0) volume :=
    (continuous_derivative_of_ac_flux hQ).locallyIntegrableOn measurableSet_Ioi
  have hFc : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      HasDerivAt (fun t => starRingEnd ℂ (F t)) (starRingEnd ℂ (deriv F t)) t := by
    filter_upwards [hF.ae_differentiableAt] with t ht
    exact Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t ht.hasDerivAt
  have hpd : Continuous (fun t => -(SigmaPresentations.density t : ℂ)) :=
    (Complex.continuous_ofReal.comp (continuous_id.mul continuous_id.neg.rexp)).neg
  have hyl : LocallyIntegrableOn (fun t => -(SigmaPresentations.density t : ℂ)*starRingEnd ℂ (y t))
      (Ioi 0) volume :=
    (complex_locally_integrable_conj (gamma_l2_locally_integrableOn y)).continuousOn_mul
      hpd.continuousOn isOpen_Ioi.isLocallyClosed
  have hQd : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      HasDerivAt (fun t => starRingEnd ℂ (Q t))
        (-(SigmaPresentations.density t : ℂ)*starRingEnd ℂ (y t)) t := by
    filter_upwards [hQ.ae_differentiableAt,gamma_ae_iff_positive_volume_ae.mp hy,
      ae_restrict_mem measurableSet_Ioi] with t ht hyt hpos
    have hp0 : (SigmaPresentations.density t : ℂ) ≠ 0 := by
      have h : 0 < SigmaPresentations.density t := mul_pos hpos (Real.exp_pos _)
      exact_mod_cast h.ne'
    have he : deriv Q t = -(SigmaPresentations.density t : ℂ)*y t := by
      change -(SigmaPresentations.density t : ℂ)⁻¹*deriv Q t=y t at hyt
      field_simp at hyt
      linear_combination -hyt
    have hh := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t ht.hasDerivAt
    change HasDerivAt (fun t => starRingEnd ℂ (Q t)) (starRingEnd ℂ (deriv Q t)) t at hh
    simpa only [he,map_mul,map_neg,Complex.conj_ofReal] using hh
  let w : ℝ → ℂ := fun t => (steinFlux t : ℂ)*deriv f t
  have hw : ContDiff ℝ ∞ w :=
    (Complex.ofRealCLM.contDiff.comp steinFlux_contDiff).mul (contDiff_infty_iff_deriv.mp hf).2
  have hwp : tsupport w ⊆ Ioi 0 := tsupport_mul_subset_right.trans
    ((closure_minimal support_deriv_subset isClosed_closure).trans hp)
  have heF := hF.conj.compact_integration_by_parts (complex_locally_integrable_conj hFl)
    hFc w hw hs.deriv.mul_left hwp
  have heQ := hQ.conj.compact_integration_by_parts hyl hQd f hf hs hp
  have hleft := l2_compact_pairing_density y f hf hs hp
  have hright : @inner ℂ LaguerreWeightedHilbert _ x (smoothCompactL2Image f hf hs) =
      ∫ t : ℝ, (SigmaPresentations.density t : ℂ)*starRingEnd ℂ (F t)*opComplexLaguerreExpression f t := by
    rw [L2.inner_def]
    have he : (fun t => @inner ℂ ℂ _ (x t) (smoothCompactL2Image f hf hs t)) =ᵐ[gammaProbability]
        (fun t => starRingEnd ℂ (F t)*opComplexLaguerreExpression f t) := by
      filter_upwards [hFx,smooth_compact_image_coe f hf hs] with t hft hit
      simp only [RCLike.inner_apply,← hft,hit]
    rw [integral_congr_ae he,gamma_probability_complex_integral]
    simp_rw [← mul_assoc]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    rw [image_eq_zero_of_nmem_tsupport
      (fun h => ht (hp (op_complex_laguerre_expression_tsupport f h))),mul_zero]
  have he1 : (fun t => starRingEnd ℂ (F t)*deriv w t) =
      (fun t => -((SigmaPresentations.density t : ℂ)*starRingEnd ℂ (F t)*opComplexLaguerreExpression f t)) := by
    funext t
    rw [complex_flux_test_derivative f hf t]
    ring
  have he2 : (fun t => starRingEnd ℂ (Q t)*deriv f t) =
      (fun t => starRingEnd ℂ (deriv F t)*w t) := by
    funext t
    simp only [Q,w,map_mul,Complex.conj_ofReal]
    ring
  rw [he1,integral_neg] at heF
  rw [he2] at heQ
  simp_rw [neg_mul,integral_neg] at heQ
  rw [hleft,hright]
  linear_combination heF-heQ


/-- Maximal locally AC representatives belong to the actual canonical domain;
the divergence expression is the actual operator image. -/
theorem laguerre_mem_of_maximal_representative
    (x y : LaguerreWeightedHilbert) (F : ℝ → ℂ)
    (hFx : F =ᵐ[gammaProbability] (x : ℝ → ℂ))
    (hF : PositiveRayLocallyAbsolutelyContinuous F)
    (hQ : PositiveRayLocallyAbsolutelyContinuous (fun t => (steinFlux t : ℂ)*deriv F t))
    (hy : laguerreDivergenceExpression F =ᵐ[gammaProbability] (y : ℝ → ℂ)) :
    ∃ hx : x ∈ laguerreCanonicalOperator.domain,
      laguerreCanonicalOperator ⟨x,hx⟩ = y := by
  have htest : ∀ u : laguerreMinimalOperator.domain,
      @inner ℂ LaguerreWeightedHilbert _ y u.val =
        @inner ℂ LaguerreWeightedHilbert _ x (laguerreMinimalOperator u) := by
    intro u
    have hum : u.val ∈ laguerreCompactTestDomain := by
      rw [← laguerre_minimal_domain]
      exact u.property
    obtain ⟨f,hf,hs,hp,hu⟩ := hum
    have he := smooth_compact_vector_eq_of_ae u.val f hf hs hu
    have hue : u = ⟨smoothCompactL2Vector f hf hs,laguerre_compact_test_mem f hf hs hp⟩ :=
      Subtype.ext he.symm
    rw [hue,laguerre_minimal_test_action f hf hs hp]
    exact laguerre_maximal_compact_pairing x y F hFx hF hQ hy f hf hs hp
  have hx := laguerreMinimalOperator.mem_adjoint_domain_of_exists x ⟨y,htest⟩
  have ha := laguerreMinimalOperator.adjoint_apply_eq laguerre_minimal_dense ⟨x,hx⟩ htest
  have hxc : x ∈ laguerreCanonicalOperator.domain := by
    rw [← laguerre_minimal_adjoint_eq_canonical]
    exact hx
  refine ⟨hxc,?_⟩
  exact (laguerre_minimal_adjoint_eq_canonical.le.2 rfl).symm.trans ha

/-- Exact maximal locally absolutely continuous domain of the actual graph
closure. The only assumptions are the two local AC conditions and L2 membership
of the literal divergence expression; no boundary or energy condition occurs. -/
theorem laguerre_canonical_domain_iff_maximal (x : LaguerreWeightedHilbert) :
    x ∈ laguerreCanonicalOperator.domain ↔
      ∃ F : ℝ → ℂ, F =ᵐ[gammaProbability] (x : ℝ → ℂ) ∧
        PositiveRayLocallyAbsolutelyContinuous F ∧
        PositiveRayLocallyAbsolutelyContinuous (fun t => (steinFlux t : ℂ)*deriv F t) ∧
        Memℒp (laguerreDivergenceExpression F) 2 gammaProbability := by
  constructor
  · intro hx
    have hx' : x ∈ (laguerreSpectralOperator id).domain := by
      rwa [← laguerre_canonical_eq_spectral]
    obtain ⟨F,hFx,hF,hQ,hy⟩ := laguerre_operator_maximal_representative ⟨x,hx'⟩
    exact ⟨F,hFx,hF,hQ,(Lp.memℒp (laguerreSpectralOperator id ⟨x,hx'⟩)).ae_eq hy.symm⟩
  · rintro ⟨F,hFx,hF,hQ,hi⟩
    exact (laguerre_mem_of_maximal_representative x (hi.toLp _) F hFx hF hQ
      (Memℒp.coeFn_toLp hi).symm).choose

end
end Sigma
