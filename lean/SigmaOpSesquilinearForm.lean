import SigmaOpWeightedSobolev

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ContDiff ENNReal NNReal

/-- The finite-disjoint-interval definition implies ordinary continuity
at each interior point; no differentiability hypothesis is needed. -/
theorem PositiveRayLocallyAbsolutelyContinuous.continuousAt
    {F : ℝ → ℂ} (hF : PositiveRayLocallyAbsolutelyContinuous F)
    {x : ℝ} (hx : 0 < x) : ContinuousAt F x := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := hF (x/2) (x+1) (by positivity)
    (ENNReal.ofReal ε) (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
  obtain ⟨d,_,hdpos,hdd⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδ
  have hdp : 0 < d := ENNReal.ofReal_pos.mp hdpos
  refine ⟨min d (min (x/2) 1), lt_min hdp (lt_min (by positivity) zero_lt_one), ?_⟩
  intro y hy
  have hdist : |y-x| < min d (min (x/2) 1) := by simpa only [Real.dist_eq] using hy
  have hsmall := abs_lt.mp (hdist.trans_le (min_le_right _ _))
  have hlow : x/2 ≤ min x y := by
    apply le_min <;> linarith [min_le_left (x/2) (1:ℝ)]
  have hupp : max x y ≤ x+1 := by
    apply max_le <;> linarith [min_le_right (x/2) (1:ℝ)]
  have hlen : max x y-min x y = |y-x| := by
    rcases le_total x y with h | h
    · rw [max_eq_right h, min_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    · rw [max_eq_left h, min_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
  have hb := hd 1 (fun _ => min x y) (fun _ => max x y)
    (fun _ => ⟨hlow, min_le_max, hupp⟩)
    (by intro i _ j _ hij; exact (hij (Subsingleton.elim i j)).elim)
    (by simpa only [Fin.sum_univ_one, hlen] using
      (ENNReal.ofReal_lt_ofReal_iff hdp).mpr (hdist.trans_le (min_le_left _ _)) |>.trans hdd)
  have hn : (‖F (max x y)-F (min x y)‖₊ : ℝ≥0∞) < ENNReal.ofReal ε := by
    simpa only [Fin.sum_univ_one] using hb
  have he : ‖F (max x y)-F (min x y)‖ = dist (F y) (F x) := by
    rcases le_total x y with h | h
    · rw [max_eq_right h, min_eq_left h, dist_eq_norm]
    · rw [max_eq_left h, min_eq_right h, dist_eq_norm, norm_sub_rev]
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hε] at hn
  exact he ▸ hn

theorem PositiveRayLocallyAbsolutelyContinuous.continuousOn
    {F : ℝ → ℂ} (hF : PositiveRayLocallyAbsolutelyContinuous F) :
    ContinuousOn F (Ioi 0) := fun _ hx => (hF.continuousAt hx).continuousWithinAt

theorem PositiveRayLocallyAbsolutelyContinuous.eqOn_of_ae
    {F G : ℝ → ℂ} (hF : PositiveRayLocallyAbsolutelyContinuous F)
    (hG : PositiveRayLocallyAbsolutelyContinuous G) (he : F =ᵐ[gammaProbability] G) :
    EqOn F G (Ioi 0) :=
  Measure.eqOn_open_of_ae_eq (gamma_ae_iff_positive_volume_ae.mp he)
    isOpen_Ioi hF.continuousOn hG.continuousOn

theorem smooth_compact_vector_smul (c : ℂ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    smoothCompactL2Vector (fun t => c * f t) (contDiff_const.mul hf) hs.mul_left =
      c • smoothCompactL2Vector f hf hs := by
  apply Lp.ext
  filter_upwards [smooth_compact_l2_coe (fun t => c * f t) (contDiff_const.mul hf) hs.mul_left,
    Lp.coeFn_smul c (smoothCompactL2Vector f hf hs), smooth_compact_l2_coe f hf hs]
    with t ht hsm hf'
  simp only [ht, hsm, Pi.smul_apply, hf', smul_eq_mul]

theorem smooth_compact_gradient_smul (c : ℂ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    smoothCompactGradient (fun t => c * f t) (contDiff_const.mul hf) hs.mul_left =
      c • smoothCompactGradient f hf hs := by
  apply Lp.ext
  filter_upwards [smooth_compact_gradient_coe (fun t => c * f t) (contDiff_const.mul hf) hs.mul_left,
    Lp.coeFn_smul c (smoothCompactGradient f hf hs), smooth_compact_gradient_coe f hf hs]
    with t ht hsm hf'
  simp only [ht, hsm, Pi.smul_apply, hf', smul_eq_mul, weightedTestDerivative,
    deriv_const_mul c (hf.differentiable (by simp) t)]
  ring

private def smoothRoot (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    LaguerreWeightedHilbert :=
  laguerreSpectralOperator Real.sqrt ⟨smoothCompactL2Vector f hf hs,
    laguerre_integer_domain_le_square_root (smooth_compact_mem_laguerre_domain f hf hs)⟩

private theorem smooth_root_smul (c : ℂ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    smoothRoot (fun t => c * f t) (contDiff_const.mul hf) hs.mul_left =
      c • smoothRoot f hf hs := by
  unfold smoothRoot
  have he : (⟨smoothCompactL2Vector (fun t => c * f t) (contDiff_const.mul hf) hs.mul_left,
      laguerre_integer_domain_le_square_root (smooth_compact_mem_laguerre_domain _ _ _)⟩ :
      (laguerreSpectralOperator Real.sqrt).domain) =
      c • ⟨smoothCompactL2Vector f hf hs,
        laguerre_integer_domain_le_square_root (smooth_compact_mem_laguerre_domain _ _ _)⟩ := by
    apply Subtype.ext
    exact smooth_compact_vector_smul c f hf hs
  rw [he, LinearPMap.map_smul]

private theorem smooth_gradient_re_inner (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    (@inner ℂ LaguerreWeightedHilbert _ (smoothCompactGradient f hf hfs)
      (smoothCompactGradient g hg hgs)).re =
    (@inner ℂ LaguerreWeightedHilbert _ (smoothRoot f hf hfs) (smoothRoot g hg hgs)).re := by
  change RCLike.re (@inner ℂ LaguerreWeightedHilbert _ _ _) =
    RCLike.re (@inner ℂ LaguerreWeightedHilbert _ _ _)
  rw [re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    smooth_compact_gradient_sub_norm, smooth_compact_gradient_norm_eq_root,
    smooth_compact_gradient_norm_eq_root]
  rfl

theorem smooth_compact_gradient_inner (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    @inner ℂ LaguerreWeightedHilbert _ (smoothCompactGradient f hf hfs)
      (smoothCompactGradient g hg hgs) =
    @inner ℂ LaguerreWeightedHilbert _
      (laguerreSpectralOperator Real.sqrt ⟨smoothCompactL2Vector f hf hfs,
        laguerre_integer_domain_le_square_root (smooth_compact_mem_laguerre_domain _ _ _)⟩)
      (laguerreSpectralOperator Real.sqrt ⟨smoothCompactL2Vector g hg hgs,
        laguerre_integer_domain_le_square_root (smooth_compact_mem_laguerre_domain _ _ _)⟩) := by
  apply Complex.ext
  · exact smooth_gradient_re_inner f g hf hg hfs hgs
  · have h := smooth_gradient_re_inner f (fun t => Complex.I * g t)
      hf (contDiff_const.mul hg) hfs hgs.mul_left
    rw [smooth_compact_gradient_smul, smooth_root_smul,
      inner_smul_right, inner_smul_right] at h
    simpa only [Complex.I_mul_re, neg_inj] using h

/-- Convergence of compact smooth functions and their weighted gradients
also gives convergence under the actual closed square-root operator. -/
theorem smooth_compact_root_tendsto_of_gradient
    (f : ℕ → ℝ → ℂ) (hf : ∀ k, ContDiff ℝ ∞ (f k))
    (hs : ∀ k, HasCompactSupport (f k))
    (x : (laguerreSpectralOperator Real.sqrt).domain) (g : LaguerreWeightedHilbert)
    (hv : Tendsto (fun k => smoothCompactL2Vector (f k) (hf k) (hs k)) atTop (𝓝 x.val))
    (hg : Tendsto (fun k => smoothCompactGradient (f k) (hf k) (hs k)) atTop (𝓝 g)) :
    Tendsto (fun k => laguerreSpectralOperator Real.sqrt
      ⟨smoothCompactL2Vector (f k) (hf k) (hs k),
        laguerre_integer_domain_le_square_root (smooth_compact_mem_laguerre_domain _ _ _)⟩)
      atTop (𝓝 (laguerreSpectralOperator Real.sqrt x)) := by
  have hc : CauchySeq (fun k => smoothRoot (f k) (hf k) (hs k)) := by
    have hcs := Metric.cauchySeq_iff.mp hg.cauchySeq
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := hcs ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have hh := hN m hm n hn
    rw [dist_eq_norm, smooth_compact_gradient_sub_norm] at hh
    exact hh
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
  have hmem : (x.val, y) ∈ (laguerreSpectralOperator Real.sqrt).graph := by
    apply (laguerre_spectral_closed Real.sqrt).mem_of_tendsto (hv.prod_mk_nhds hy)
    exact Eventually.of_forall fun k => LinearPMap.mem_graph _
      ⟨smoothCompactL2Vector (f k) (hf k) (hs k),
        laguerre_integer_domain_le_square_root (smooth_compact_mem_laguerre_domain _ _ _)⟩
  obtain ⟨z,hz,hzy⟩ := (LinearPMap.mem_graph_iff _).mp hmem
  have he : z = x := Subtype.ext hz
  rw [he] at hzy
  dsimp only at hzy
  rw [← hzy] at hy
  exact hy

theorem gamma_integrable_positive_complex_density (f : ℝ → ℂ)
    (hf : Integrable f gammaProbability) :
    IntegrableOn (fun t => (SigmaPresentations.density t : ℂ) * f t) (Ioi 0) volume := by
  change Integrable f (volume.withDensity
    (fun t => ((Real.toNNReal (gammaPDFReal 2 1 t):ℝ≥0):ℝ≥0∞))) at hf
  have hi := (integrable_withDensity_iff_integrable_smul
    ((measurable_gammaPDFReal 2 1).real_toNNReal)).mp hf
  have he : (fun t => Real.toNNReal (gammaPDFReal 2 1 t) • f t) =
      (Ici (0:ℝ)).indicator (fun t => (SigmaPresentations.density t : ℂ) * f t) := by
    funext t
    rw [NNReal.smul_def, Complex.real_smul,
      Real.coe_toNNReal _ (gammaPDFReal_nonneg (by norm_num) (by norm_num) t), gamma_pdf_intrinsic]
    by_cases ht : 0 ≤ t <;> simp [ht]
  rw [he, integrable_indicator_iff measurableSet_Ici] at hi
  exact hi.mono_set Ioi_subset_Ici_self

private theorem weighted_derivative_pair_pointwise (g h : LaguerreWeightedHilbert)
    (t : ℝ) (ht : 0 < t) :
    (steinFlux t : ℂ) * weightedDerivativeRepresentative g t *
      starRingEnd ℂ (weightedDerivativeRepresentative h t) =
      (SigmaPresentations.density t : ℂ) * (g t * starRingEnd ℂ (h t)) := by
  have hsq : (Real.sqrt t : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
  have hq : (steinFlux t : ℂ) =
      (SigmaPresentations.density t : ℂ) * (Real.sqrt t : ℂ)^2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ht.le]
    simp only [steinFlux, SigmaPresentations.density]
    push_cast
    ring
  rw [hq]
  simp only [weightedDerivativeRepresentative, map_div₀, Complex.conj_ofReal]
  field_simp
  ring

/-- The literal mixed weighted derivative integral, in the paper's convention
(linear in its first argument), is the reversed Lean inner product. -/
theorem regular_representative_weighted_inner (g h : LaguerreWeightedHilbert)
    (F G : ℝ → ℂ)
    (hF : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      HasDerivAt F (weightedDerivativeRepresentative g t) t)
    (hG : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      HasDerivAt G (weightedDerivativeRepresentative h t) t) :
    IntegrableOn (fun t => (steinFlux t : ℂ) * deriv F t * starRingEnd ℂ (deriv G t))
      (Ioi 0) volume ∧
    (∫ t : ℝ in Ioi 0, (steinFlux t : ℂ) * deriv F t * starRingEnd ℂ (deriv G t)) =
      @inner ℂ LaguerreWeightedHilbert _ h g := by
  have hi : Integrable (fun t => g t * starRingEnd ℂ (h t)) gammaProbability := by
    simpa only [RCLike.inner_apply, mul_comm] using (L2.integrable_inner (𝕜 := ℂ) h g)
  have he : (fun t => (steinFlux t : ℂ) * deriv F t * starRingEnd ℂ (deriv G t))
      =ᵐ[volume.restrict (Ioi 0)]
      (fun t => (SigmaPresentations.density t : ℂ) * (g t * starRingEnd ℂ (h t))) := by
    filter_upwards [hF, hG, ae_restrict_mem measurableSet_Ioi] with t hf hg ht
    rw [hf.deriv, hg.deriv]
    exact weighted_derivative_pair_pointwise g h t ht
  refine ⟨(gamma_integrable_positive_complex_density _ hi).congr he.symm, ?_⟩
  rw [integral_congr_ae he, L2.inner_def, gamma_probability_complex_integral]
  simp only [RCLike.inner_apply, mul_comm]

/-- All vectors in the full spectral square-root domain have actual locally
absolutely continuous representatives satisfying the mixed differential form
identity. The reverse Sobolev-domain inclusion is a separate assertion. -/
theorem laguerre_square_root_sesquilinear_representatives
    (x y : (laguerreSpectralOperator Real.sqrt).domain) :
    ∃ F G : ℝ → ℂ,
      F =ᵐ[gammaProbability] (x.val : ℝ → ℂ) ∧
      G =ᵐ[gammaProbability] (y.val : ℝ → ℂ) ∧
      PositiveRayLocallyAbsolutelyContinuous F ∧
      PositiveRayLocallyAbsolutelyContinuous G ∧
      IntegrableOn (fun t => (steinFlux t : ℂ) * deriv F t * starRingEnd ℂ (deriv G t))
        (Ioi 0) volume ∧
      (∫ t : ℝ in Ioi 0, (steinFlux t : ℂ) * deriv F t * starRingEnd ℂ (deriv G t)) =
        @inner ℂ LaguerreWeightedHilbert _
          (laguerreSpectralOperator Real.sqrt y) (laguerreSpectralOperator Real.sqrt x) := by
  obtain ⟨f,hf,hs,_,g,hv,hg,hfae,_⟩ := laguerre_weighted_gradient_completion_ae x
  obtain ⟨u,hu,hus,_,h,huv,hh,huae,_⟩ := laguerre_weighted_gradient_completion_ae y
  have hpos := operator_integer_samples_ae_pos gammaProbability
    operator_gamma_probability_integer_samples
  obtain ⟨F,hF,hFd,hFac⟩ := positive_sobolev_limit_regular_representative
    gammaProbability hpos f hf (x.val : ℝ → ℂ) (weightedDerivativeRepresentative g)
    (gamma_l2_div_sqrt_locally_integrable g) hfae
    (fun _ _ ha hb => smooth_compact_gradient_local_derivative_tendsto f hf hs g hg ha hb)
  obtain ⟨G,hG,hGd,hGac⟩ := positive_sobolev_limit_regular_representative
    gammaProbability hpos u hu (y.val : ℝ → ℂ) (weightedDerivativeRepresentative h)
    (gamma_l2_div_sqrt_locally_integrable h) huae
    (fun _ _ ha hb => smooth_compact_gradient_local_derivative_tendsto u hu hus h hh ha hb)
  obtain ⟨hi,he⟩ := regular_representative_weighted_inner g h F G hFd hGd
  refine ⟨F,G,hF,hG,hFac,hGac,hi,he.trans ?_⟩
  have hlim := (smooth_compact_root_tendsto_of_gradient u hu hus y h huv hh).inner (𝕜 := ℂ)
    (smooth_compact_root_tendsto_of_gradient f hf hs x g hv hg)
  apply tendsto_nhds_unique (hh.inner (𝕜 := ℂ) hg)
  convert hlim using 1
  funext k
  exact smooth_compact_gradient_inner (u k) (f k) (hu k) (hf k) (hus k) (hs k)

/-- The mixed form identity holds for any locally absolutely continuous
representatives, on the whole native square-root domain. Lean's inner product
is conjugate-linear in its first argument, hence the displayed argument order. -/
theorem laguerre_square_root_sesquilinear_form
    (x y : (laguerreSpectralOperator Real.sqrt).domain) (F G : ℝ → ℂ)
    (hFx : F =ᵐ[gammaProbability] (x.val : ℝ → ℂ))
    (hGy : G =ᵐ[gammaProbability] (y.val : ℝ → ℂ))
    (hFac : PositiveRayLocallyAbsolutelyContinuous F)
    (hGac : PositiveRayLocallyAbsolutelyContinuous G) :
    IntegrableOn (fun t => (steinFlux t : ℂ) * deriv F t * starRingEnd ℂ (deriv G t))
      (Ioi 0) volume ∧
    (∫ t : ℝ in Ioi 0, (steinFlux t : ℂ) * deriv F t * starRingEnd ℂ (deriv G t)) =
      @inner ℂ LaguerreWeightedHilbert _
        (laguerreSpectralOperator Real.sqrt y) (laguerreSpectralOperator Real.sqrt x) := by
  obtain ⟨F₀,G₀,hF₀,hG₀,hF₀ac,hG₀ac,hi,he⟩ :=
    laguerre_square_root_sesquilinear_representatives x y
  have hF := hFac.eqOn_of_ae hF₀ac (hFx.trans hF₀.symm)
  have hG := hGac.eqOn_of_ae hG₀ac (hGy.trans hG₀.symm)
  have hder {U V : ℝ → ℂ} (h : EqOn U V (Ioi 0)) {t : ℝ} (ht : 0 < t) :
      deriv U t = deriv V t := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact h hs
  have hpair : (fun t => (steinFlux t : ℂ) * deriv F t * starRingEnd ℂ (deriv G t))
      =ᵐ[volume.restrict (Ioi 0)]
      (fun t => (steinFlux t : ℂ) * deriv F₀ t * starRingEnd ℂ (deriv G₀ t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hder hF ht, hder hG ht]
  exact ⟨hi.congr hpair.symm, (integral_congr_ae hpair).trans he⟩

end
end Sigma
