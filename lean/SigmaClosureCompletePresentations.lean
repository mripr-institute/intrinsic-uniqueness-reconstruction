import SigmaClosurePresentations
import SigmaCompletionFamily
import SigmaSelfConcordanceGeometry
import SigmaProbEntropyCalibration
import SigmaProbNativeHazard
import SigmaProbDistributionGreen
import SigmaRealTreesInverse
import SigmaFareyClosure
import SigmaFenchelConverseConvex
import SigmaProbKLBoundaries
import SigmaProbODE
import SigmaProbDeficitSmooth

namespace Sigma.Closure
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ContDiff

private theorem positive_extension_eq (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    positiveExtension (fun x : PositiveCoordinate => f x) =ᶠ[𝓝 t] f := by
  filter_upwards [Ioi_mem_nhds ht] with x hx
  change 0 < x at hx
  simp [positiveExtension, hx]

private theorem positive_extension_deriv (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    deriv (positiveExtension (fun x : PositiveCoordinate => f x)) t = deriv f t :=
  (positive_extension_eq f ht).deriv_eq

private theorem positive_extension_curvature (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    scCurvature (positiveExtension (fun x : PositiveCoordinate => f x)) t =
      scCurvature f t := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds ht] with x hx
  exact positive_extension_deriv f hx

private theorem positive_extension_third (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    scThirdDerivative (positiveExtension (fun x : PositiveCoordinate => f x)) t =
      scThirdDerivative f t := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds ht] with x hx
  exact positive_extension_curvature f hx

def typedCompletionData (slopeAnchor : Bool) : PresentationData :=
  ⟨GroupFunction, fun h =>
      (∀ z > -1, DifferentiableAt ℝ (groupExtension h) z) ∧
      (∀ z > -1, -1 < deriv (groupExtension h) z),
    Prop, fun h => TypedCompletion (groupExtension h) ∧
      (if slopeAnchor then deriv (groupExtension h) 0 = 0 else groupExtension h 0 = 0),
    True⟩

def typedCompletionNode (slopeAnchor : Bool) : IdentifiedNode := by
  let w : GroupFunction := fun x => completionFamily 1 x
  have he (z : ℝ) (hz : -1 < z) : groupExtension w z = completionFamily 1 z := by
    simp [w, groupExtension, hz]
  have hd (z : ℝ) (hz : -1 < z) :
      HasDerivAt (groupExtension w) (1 / (1 + z) - 1) z := by
    apply (completionFamily_hasDerivAt 1 hz).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hz] with x hx
    exact he x hx
  have hr (z : ℝ) (hz : -1 < z) : -1 < deriv (groupExtension w) z := by
    rw [(hd z hz).deriv]
    have hp : 0 < 1 / (1 + z) := one_div_pos.mpr (by linarith)
    linarith
  refine ⟨typedCompletionData slopeAnchor,
    assemblePresentation (typedCompletionData slopeAnchor) w ⟨⟨?_, hr⟩, ?_⟩ ?_⟩
  · exact fun z hz => (hd z hz).differentiableAt
  · apply propext
    refine ⟨fun _ => trivial, fun _ => ⟨?_, ?_⟩⟩
    · exact (typed_completion_iff_family _ (fun z hz => (hd z hz).differentiableAt) hr).mpr
        ⟨1, by norm_num, he⟩
    · cases slopeAnchor <;> simp [he 0 (by norm_num), (hd 0 (by norm_num)).deriv,
        completionFamily]
  · intro h hh ho
    obtain ⟨hc, ha⟩ := (Iff.of_eq ho).mpr True.intro
    funext z
    have hu : groupExtension h z = Real.log (1 + z.val) - z.val := by
      cases slopeAnchor
      · exact completion_value_anchor_identifies _ hh.1 hh.2 hc ha z z.property
      · exact completion_slope_anchor_identifies _ hh.1 hh.2 hc ha z z.property
    simpa [groupExtension, z.property, w, completionFamily] using hu

def selfConcordanceData (unsigned : Bool) : PresentationData :=
  ⟨ScalarFunction, fun F => ContDiffOn ℝ 3 (positiveExtension F) (Ioi 0) ∧
      ∀ t > 0, 0 < scCurvature (positiveExtension F) t,
    Prop, fun F => positiveExtension F 1 = 0 ∧ deriv (positiveExtension F) 1 = 0 ∧
      scCurvature (positiveExtension F) 1 = 1 ∧
      ∀ t > 0, if unsigned then
        |scThirdDerivative (positiveExtension F) t| =
          2 * (scCurvature (positiveExtension F) t) ^ (3 / 2 : ℝ)
      else scThirdDerivative (positiveExtension F) t =
        -2 * (scCurvature (positiveExtension F) t) ^ (3 / 2 : ℝ), True⟩

def selfConcordanceNode (unsigned : Bool) : IdentifiedNode := by
  refine ⟨selfConcordanceData unsigned,
    assemblePresentation (selfConcordanceData unsigned) (fun t => I t) ⟨⟨?_, ?_⟩, ?_⟩ ?_⟩
  · exact sc_intrinsic_C3.congr (fun t ht => by simp [positiveExtension, mem_Ioi.mp ht])
  · intro t ht
    rw [positive_extension_curvature I ht]
    exact sc_intrinsic_calibration.2.2.2 t ht
  · apply propext
    refine ⟨fun _ => trivial, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
    · simpa [positiveExtension] using sc_intrinsic_calibration.1
    · rw [positive_extension_deriv I (by norm_num)]
      exact sc_intrinsic_calibration.2.1
    · rw [positive_extension_curvature I (by norm_num)]
      exact sc_intrinsic_calibration.2.2.1
    · intro t ht
      rw [positive_extension_third I ht, positive_extension_curvature I ht]
      cases unsigned
      · exact sc_intrinsic_signed_equality ht
      · simp only [↓reduceIte]
        rw [sc_intrinsic_signed_equality ht, abs_mul]
        have hp : 0 ≤ (scCurvature I t) ^ (3 / 2 : ℝ) := Real.rpow_nonneg
          (sc_intrinsic_calibration.2.2.2 t ht).le _
        rw [abs_of_nonneg hp]
        norm_num
  · intro F hF ho
    obtain ⟨hv, hs, hc, he⟩ := (Iff.of_eq ho).mpr True.intro
    funext t
    have hu : positiveExtension F t = I t := by
      cases unsigned
      · exact self_concordance_signed_identifies _ hF.1 hF.2 hv hs hc he t t.property
      · exact self_concordance_unsigned_identifies _ hF.1 hF.2 hv hs hc he t t.property
    simpa [positiveExtension, t.property] using hu

/-- All causal linear test functionals are admitted, so no extra regularity
or a priori norm bound restricts the paper's distributional candidate class. -/
def causalGreenData : PresentationData :=
  ⟨P5CausalDistribution, fun _ => True, P5TestFunction →ₗ[ℝ] ℝ,
    fun T => p5DistributionGreenOperator T.apply, p5DiracFunctional⟩

def causalGreenNode : IdentifiedNode := by
  have hw : p5DistributionGreenOperator p5CausalGreen.apply =
      p5DiracFunctional := by
    ext f
    rw [p5DistributionGreenOperator_apply]
    exact p5_causal_green_pairing_eq_dirac f
  refine ⟨causalGreenData, assemblePresentation causalGreenData p5CausalGreen
    ⟨trivial, hw⟩ ?_⟩
  intro S _ hS
  apply P5CausalDistribution.ext
  apply p5_causal_distribution_green_unique
  intro f
  simpa only [causalGreenData, p5DistributionGreenOperator_apply] using
    congrArg (fun T : P5TestFunction →ₗ[ℝ] ℝ => T f) hS

def exactLegendreData : PresentationData :=
  ⟨ℝ → EReal, fun F => LowerSemicontinuousOn F (Ioi 0) ∨ ExtendedConvex F,
    ℝ → EReal, fullFenchelConjugate, intrinsicConjugateTarget⟩

def exactLegendreNode : IdentifiedNode :=
  ⟨exactLegendreData, assemblePresentation exactLegendreData extendedIntrinsic
    ⟨Or.inl extended_intrinsic_lower_semicontinuousOn, extended_intrinsic_full_conjugate⟩
    (fun F hF ho => exact_legendre_target_identifies F ho hF)⟩

def hessianMetricData : PresentationData :=
  ⟨ScalarFunction, fun F =>
      (∀ t > 0, DifferentiableAt ℝ (positiveExtension F) t) ∧
      (∀ t > 0, DifferentiableAt ℝ (deriv (positiveExtension F)) t),
    Prop, fun F => positiveExtension F 1 = 0 ∧ deriv (positiveExtension F) 1 = 0 ∧
      ∀ t > 0, scCurvature (positiveExtension F) t = 1 / t ^ (2 : ℕ), True⟩

def hessianMetricNode : IdentifiedNode := by
  refine ⟨hessianMetricData, assemblePresentation hessianMetricData (fun t => I t)
    ⟨⟨?_, ?_⟩, ?_⟩ ?_⟩
  · intro t ht
    exact ((SigmaBase.potential_hasDerivAt ht).congr_of_eventuallyEq
      (positive_extension_eq I ht)).differentiableAt
  · intro t ht
    apply (sc_intrinsic_second_hasDerivAt ht).differentiableAt.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact positive_extension_deriv I hx
  · apply propext
    refine ⟨fun _ => trivial, fun _ => ⟨?_, ?_, ?_⟩⟩
    · simpa [positiveExtension] using sc_intrinsic_calibration.1
    · rw [positive_extension_deriv I (by norm_num)]
      exact sc_intrinsic_calibration.2.1
    · intro t ht
      rw [positive_extension_curvature I ht]
      exact sc_intrinsic_curvature ht
  · intro F hF ho
    obtain ⟨hv, hs, hc⟩ := (Iff.of_eq ho).mpr True.intro
    funext t
    have hu := sc_anchored_curvature_reconstructs _ hF.1 hF.2 hc hv hs t t.property
    simpa [positiveExtension, t.property] using hu

/-- Actual oriented relative entropy, with the reference Poisson(1) in the
first argument and the marked rate in the second. -/
def orientedPoissonKLData : PresentationData :=
  ⟨ScalarFunction, fun _ => True, ScalarFunction, id,
    fun t => finiteRelativeEntropy (poissonMeasure 1)
      (poissonMeasure ⟨t, t.property.le⟩)⟩

def orientedPoissonKLNode : IdentifiedNode := by
  refine ⟨orientedPoissonKLData,
    assemblePresentation orientedPoissonKLData (fun t => I t) ⟨trivial, ?_⟩ ?_⟩
  · funext t
    exact (poisson_relative_entropy_slice ⟨t, t.property.le⟩ t.property).symm
  · intro F _ ho
    funext t
    exact (congrFun ho t).trans
      (poisson_relative_entropy_slice ⟨t, t.property.le⟩ t.property)

def orientedExponentialKLData : PresentationData :=
  ⟨ScalarFunction, fun _ => True, ScalarFunction, id,
    fun t => finiteRelativeEntropy (rateExpProbability 1) (rateExpProbability t.val)⟩

def orientedExponentialKLNode : IdentifiedNode := by
  refine ⟨orientedExponentialKLData,
    assemblePresentation orientedExponentialKLData (fun t => I t) ⟨trivial, ?_⟩ ?_⟩
  · funext t
    exact (exponential_relative_entropy_slice t t.property).symm
  · intro f _ ho
    funext t
    exact (congrFun ho t).trans (exponential_relative_entropy_slice t t.property)

def orientedGaussianKLData : PresentationData :=
  ⟨ScalarFunction, fun _ => True, ScalarFunction, id,
    fun t => 2 * finiteRelativeEntropy (gaussianReal 0 ⟨t, t.property.le⟩) (gaussianReal 0 1)⟩

def orientedGaussianKLNode : IdentifiedNode := by
  refine ⟨orientedGaussianKLData,
    assemblePresentation orientedGaussianKLData (fun t => I t) ⟨trivial, ?_⟩ ?_⟩
  · funext t
    exact (gaussian_relative_entropy_slice ⟨t, t.property.le⟩ t.property).symm
  · intro f _ ho
    funext t
    exact (congrFun ho t).trans
      (gaussian_relative_entropy_slice ⟨t, t.property.le⟩ t.property)

/-- Restricting the candidate to the retained domain avoids identifying
values outside that domain. Analytic representatives and their formal germ
are observed existentially; the conclusion is never an admissibility field. -/
def connectedAnalyticData (U : Set ℝ) (F : PowerSeries ℝ) : PresentationData :=
  ⟨U → ℝ, fun f => ∃ g : ℝ → ℝ, AnalyticOnNhd ℝ g U ∧ ∀ x : U, g x = f x,
    Prop, fun f => ∃ g : ℝ → ℝ, AnalyticOnNhd ℝ g U ∧
      HasRealFormalGerm g F ∧ ∀ x : U, g x = f x, True⟩

def connectedAnalyticNode (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U)
    (g : ℝ → ℝ) (F : PowerSeries ℝ)
    (hg : AnalyticOnNhd ℝ g U) (hF : HasRealFormalGerm g F) : IdentifiedNode := by
  refine ⟨connectedAnalyticData U F,
    assemblePresentation (connectedAnalyticData U F) (fun x => g x)
      ⟨⟨g, hg, fun _ => rfl⟩, ?_⟩ ?_⟩
  · exact propext ⟨fun _ => trivial, fun _ => ⟨g, hg, hF, fun _ => rfl⟩⟩
  · intro f _ ho
    obtain ⟨k, hk, hkg, he⟩ := (Iff.of_eq ho).mpr True.intro
    funext x
    exact (he x).symm.trans
      (real_formal_germ_global_recovery hkg hF hk hg hU h0 x.property)

def connectedToddNode (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U) : IdentifiedNode :=
  connectedAnalyticNode U hU h0 realTodd (formalTodd ℝ)
    (fun x _ => real_todd_analytic x) real_todd_formal_germ

def connectedAhatNode (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U) : IdentifiedNode :=
  connectedAnalyticNode U hU h0 realAhat (formalAhat ℝ)
    (fun x _ => real_ahat_analytic x) real_ahat_formal_germ

def connectedLNode (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U) : IdentifiedNode :=
  connectedAnalyticNode U hU h0 realLgenus (formalL ℝ)
    (fun x _ => real_lgenus_analytic x) real_lgenus_formal_germ

def connectedChiNode (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U)
    (y : ℝ) (_hy : y ≠ -1) : IdentifiedNode :=
  connectedAnalyticNode U hU h0 (realChi y) (formalChi ℝ y)
    (fun x _ => real_chi_analytic y x) (real_chi_formal_germ y)

def connectedInverseToddNode (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U) :
    IdentifiedNode :=
  connectedAnalyticNode U hU h0 (fun x => (realTodd x)⁻¹) (formalTodd ℝ)⁻¹
    (fun x _ => (real_characteristic_inverses_analytic x).1)
    real_characteristic_inverse_formal_germs.1

def connectedInverseAhatNode (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U) :
    IdentifiedNode :=
  connectedAnalyticNode U hU h0 (fun x => (realAhat x)⁻¹) (formalAhat ℝ)⁻¹
    (fun x _ => (real_characteristic_inverses_analytic x).2.1)
    real_characteristic_inverse_formal_germs.2.1

def connectedInverseLNode (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U) :
    IdentifiedNode :=
  connectedAnalyticNode U hU h0 (fun x => (realLgenus x)⁻¹) (formalL ℝ)⁻¹
    (fun x _ => (real_characteristic_inverses_analytic x).2.2.1)
    real_characteristic_inverse_formal_germs.2.2.1

def connectedInverseChiNode (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U)
    (y : ℝ) (_hy : y ≠ -1) (hn : ∀ x ∈ U, realChi y x ≠ 0) : IdentifiedNode :=
  connectedAnalyticNode U hU h0 (fun x => (realChi y x)⁻¹) (formalChi ℝ y)⁻¹
    (fun x hx => (real_characteristic_inverses_analytic x).2.2.2 y (hn x hx))
    (real_characteristic_inverse_formal_germs.2.2.2 y)

def rayDensityMeasure (f : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal (f x))

theorem intrinsic_ray_density_measure :
    rayDensityMeasure SigmaPresentations.density = gammaProbability := by
  rw [← canonical_linked_density_measure]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (intrinsic_linked_density t ht).symm

/-- Density representatives are identified up to null sets by using their
actual laws as candidates. The mass, mean and logarithmic mean are retained. -/
def entropyMaximizerData : PresentationData :=
  ⟨Measure ℝ, fun μ => ∃ f : ℝ → ℝ,
      CalibratedGammaDensity f (1 - Real.eulerMascheroniConstant) ∧
      rayDensityMeasure f = μ,
    Prop, fun μ => ∃ f : ℝ → ℝ,
      CalibratedGammaDensity f (1 - Real.eulerMascheroniConstant) ∧
      rayDensityMeasure f = μ ∧
      calibratedExtendedEntropy (1 + Real.eulerMascheroniConstant) f =
        ((1 + Real.eulerMascheroniConstant : ℝ) : EReal), True⟩

def entropyMaximizerNode : IdentifiedNode := by
  refine ⟨entropyMaximizerData, assemblePresentation entropyMaximizerData gammaProbability
    ⟨⟨SigmaPresentations.density, gamma_density_calibrated, intrinsic_ray_density_measure⟩,
      ?_⟩ ?_⟩
  · exact propext ⟨fun _ => trivial, fun _ => ⟨SigmaPresentations.density,
      gamma_density_calibrated, intrinsic_ray_density_measure, gamma_extended_entropy_value⟩⟩
  · intro μ _ ho
    obtain ⟨f, hf, hμ, hm⟩ := (Iff.of_eq ho).mpr True.intro
    rw [← hμ, ← intrinsic_ray_density_measure]
    apply withDensity_congr_ae
    filter_upwards [(calibrated_gamma_maximum_entropy f hf).2.mp hm] with x hx
    rw [hx]

private theorem gamma_native_survival (x : ℝ) (hx : 0 ≤ x) :
    lifetimeSurvival gammaProbability x = gammaSurvival x := by
  rw [lifetimeSurvival, gamma_probability_tail x hx,
    ENNReal.toReal_ofReal (gamma_survival_positive hx).le]

private theorem gamma_native_hazard :
    lifetimeHazard gammaProbability =ᵐ[volume.restrict (Ioi 0)] gammaHazard := by
  have hd := Measure.rnDeriv_withDensity volume
    ((measurable_gammaPDFReal 2 1).ennreal_ofReal)
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Ioi] with x hx hpos
  change (gammaProbability.rnDeriv volume x).toReal / lifetimeSurvival gammaProbability x = _
  change ((volume.withDensity (gammaPDF 2 1)).rnDeriv volume x) = gammaPDF 2 1 x at hx
  rw [show gammaProbability.rnDeriv volume x = gammaPDF 2 1 x from hx,
    gamma_native_survival x hpos.le]
  simp only [gammaPDF, gamma_pdf_intrinsic, if_pos hpos.le,
    ENNReal.coe_toReal, Real.coe_toNNReal _ (SigmaPresentations.density_pos hpos).le,
    ENNReal.toReal_ofReal (SigmaPresentations.density_pos hpos).le]
  exact gamma_hazard_ratio x hpos.le

def nativeSurvivalData : PresentationData :=
  ⟨Measure ℝ, fun μ => IsProbabilityMeasure μ ∧ μ ≪ volume ∧
      ∀ x > 0, 0 < lifetimeSurvival μ x,
    Prop, fun μ => lifetimeSurvival μ 0 = 1 ∧
      lifetimeHazard μ =ᵐ[volume.restrict (Ioi 0)] gammaHazard, True⟩

def nativeSurvivalNode : IdentifiedNode := by
  refine ⟨nativeSurvivalData, assemblePresentation nativeSurvivalData gammaProbability
    ⟨⟨inferInstance, withDensity_absolutelyContinuous _ _, ?_⟩, ?_⟩ ?_⟩
  · intro x hx
    rw [gamma_native_survival x hx.le]
    exact gamma_survival_positive hx.le
  · exact propext ⟨fun _ => trivial, fun _ =>
      ⟨(gamma_native_survival 0 le_rfl).trans gamma_survival_anchor, gamma_native_hazard⟩⟩
  · intro μ hμ ho
    letI := hμ.1
    obtain ⟨h0, hh⟩ := (Iff.of_eq ho).mpr True.intro
    exact gamma_probability_native_hazard_inverse μ hμ.2.1 hμ.2.2 h0 hh

/-- The logistic coordinate is linked to the hazard of the same supplied
probability, and may use any a.e. representative of its density. -/
def nativeLogisticData : PresentationData :=
  ⟨Measure ℝ × (ℝ → ℝ), fun x => IsProbabilityMeasure x.1 ∧ x.1 ≪ volume ∧
      ∀ t > 0, 0 < lifetimeSurvival x.1 t,
    Prop, fun x => lifetimeSurvival x.1 0 = 1 ∧ x.2 0 = 1 / 2 ∧
      (∀ u, HasDerivAt x.2 (x.2 u * (1 - x.2 u)) u) ∧
      (∀ᵐ t ∂volume.restrict (Ioi 0), lifetimeHazard x.1 t = x.2 (Real.log t)), True⟩

def nativeLogisticNode : IdentifiedNode := by
  refine ⟨nativeLogisticData,
    assemblePresentation nativeLogisticData (gammaProbability, logisticHazard)
      ⟨⟨inferInstance, withDensity_absolutelyContinuous _ _, ?_⟩, ?_⟩ ?_⟩
  · intro t ht
    rw [gamma_native_survival t ht.le]
    exact gamma_survival_positive ht.le
  · apply propext
    refine ⟨fun _ => trivial, fun _ => ⟨?_, logistic_hazard_anchor,
      logistic_hazard_derivative, ?_⟩⟩
    · exact (gamma_native_survival 0 le_rfl).trans gamma_survival_anchor
    · filter_upwards [gamma_native_hazard, ae_restrict_mem measurableSet_Ioi] with t ht hp
      simpa only [logistic_hazard_coordinate, Real.exp_log hp] using ht
  · intro x hx ho
    letI := hx.1
    obtain ⟨h0, hv0, hv, he⟩ := (Iff.of_eq ho).mpr True.intro
    exact Prod.ext
      (gamma_probability_native_marked_logistic_inverse x.1 hx.2.1 hx.2.2 h0
        x.2 hv hv0 he) (logistic_hazard_unique x.2 hv hv0)

def secondOrderDensityData : PresentationData :=
  ⟨ScalarFunction, fun f => ∃ g : ℝ → ℝ,
      ContDiffOn ℝ 2 g (Ioi 0) ∧ ContinuousAt g 0 ∧ ∀ t : PositiveCoordinate, g t = f t,
    Prop, fun f => ∃ g : ℝ → ℝ,
      ContDiffOn ℝ 2 g (Ioi 0) ∧ ContinuousAt g 0 ∧
      (∀ t : PositiveCoordinate, g t = f t) ∧ g 0 = 0 ∧
      (∫ t : ℝ in Ioi 0, g t) = 1 ∧
      (∀ t > 0, HasDerivAt (deriv g) (-2 * deriv g t - g t) t), True⟩

def secondOrderDensityNode : IdentifiedNode := by
  have hc : ContDiff ℝ 2 SigmaPresentations.density :=
    contDiff_id.mul contDiff_id.neg.exp
  have hd : ∀ t > 0, HasDerivAt (deriv SigmaPresentations.density)
      (-2 * deriv SigmaPresentations.density t - SigmaPresentations.density t) t := by
    intro t _
    have he : deriv SigmaPresentations.density = fun x => (1 - x) * Real.exp (-x) :=
      funext (fun x => (intrinsic_density_derivative x).deriv)
    rw [he]
    convert (((hasDerivAt_id t).const_sub 1).mul ((hasDerivAt_id t).neg.exp)) using 1
    dsimp [SigmaPresentations.density]
    ring
  refine ⟨secondOrderDensityData,
    assemblePresentation secondOrderDensityData (fun t => SigmaPresentations.density t)
      ⟨⟨SigmaPresentations.density, hc.contDiffOn, hc.continuous.continuousAt,
        fun _ => rfl⟩, ?_⟩ ?_⟩
  · exact propext ⟨fun _ => trivial, fun _ =>
      ⟨SigmaPresentations.density, hc.contDiffOn, hc.continuous.continuousAt,
        (fun _ => rfl), by simp [SigmaPresentations.density],
        intrinsic_density_integral_one, hd⟩⟩
  · intro f _ ho
    obtain ⟨g, hg, hc0, he, h0, hm, hd⟩ := (Iff.of_eq ho).mpr True.intro
    have hg' : ∀ t > 0, HasDerivAt g (deriv g t) t := fun t ht =>
      ((hg.differentiableOn (by norm_num) t ht).differentiableAt (Ioi_mem_nhds ht)).hasDerivAt
    funext t
    exact (he t).symm.trans
      (normalized_second_order_density_unique g (deriv g) hg' hd hc0 h0 hm t t.property)

def gammaLaplaceData : PresentationData :=
  ⟨Measure ℝ, fun μ => IsProbabilityMeasure μ ∧ ∀ᵐ t ∂μ, 0 ≤ t,
    NonnegativeCoordinate → ℝ,
    fun μ s => ∫ t : ℝ, Real.exp (-(s.val * t)) ∂μ,
    fun s => (1 + s.val)⁻¹ ^ 2⟩

def gammaLaplaceNode : IdentifiedNode := by
  refine ⟨gammaLaplaceData, assemblePresentation gammaLaplaceData gammaProbability
    ⟨⟨inferInstance, ?_⟩, ?_⟩ ?_⟩
  · exact (operator_integer_samples_ae_pos gammaProbability
      operator_gamma_probability_integer_samples).mono (fun _ h => h.le)
  · funext s
    exact gamma_probability_laplace (by have hs := s.property; linarith)
  · intro μ hμ ho
    letI : IsProbabilityMeasure μ := hμ.1
    apply operator_full_line_mixing_characterization μ
    intro n
    have h := congrFun ho ⟨(n : ℝ), Nat.cast_nonneg n⟩
    simpa only [neg_mul, one_div] using h

def bernsteinIntegerTailData (N : ℕ) : PresentationData :=
  ⟨NonnegativeFunction, fun f => HasBernsteinRepresentation (nonnegativeExtension f),
    {n : ℕ // N ≤ n} → ℝ, fun f n => f ⟨n.val, Nat.cast_nonneg n.val⟩,
    fun n => 2 * Real.log (1 + (n.val : ℝ))⟩

def bernsteinIntegerTailNode (N : ℕ) : IdentifiedNode := by
  refine ⟨bernsteinIntegerTailData N,
    assemblePresentation (bernsteinIntegerTailData N) (fun t => gammaLaplaceExponent t)
      ⟨?_, rfl⟩ ?_⟩
  · refine ⟨gammaBernsteinRepresentation, ?_⟩
    intro l hl
    simp only [nonnegativeExtension, dif_pos hl]
    exact (gamma_bernstein_representation_exponent l hl).symm
  · intro f hf ho
    funext t
    have hu := gamma_bernstein_function_integer_tail_unique (nonnegativeExtension f) hf N
      (fun n hn => by simpa [nonnegativeExtension, Nat.cast_nonneg] using congrFun ho ⟨n, hn⟩)
      t t.property
    simpa [nonnegativeExtension, t.property] using hu

def bernsteinRepresentationData (N : ℕ) : PresentationData :=
  ⟨BernsteinRepresentation, fun _ => True, {n : ℕ // N ≤ n} → ℝ,
    fun B n => B.exponent n.val, fun n => 2 * Real.log (1 + (n.val : ℝ))⟩

def bernsteinRepresentationNode (N : ℕ) : IdentifiedNode := by
  refine ⟨bernsteinRepresentationData N,
    assemblePresentation (bernsteinRepresentationData N) gammaBernsteinRepresentation
      ⟨trivial, ?_⟩ ?_⟩
  · funext n
    exact gamma_bernstein_representation_exponent n.val (Nat.cast_nonneg n.val)
  · intro B _ ho
    have h := (gamma_bernstein_integer_tail_unique B N (fun n hn => congrFun ho ⟨n, hn⟩)).2
    cases B
    simp only [gammaBernsteinRepresentation] at h ⊢
    rcases h with ⟨rfl, rfl, rfl⟩
    rfl

def formalSeriesData (F : PowerSeries ℝ) : PresentationData :=
  ⟨PowerSeries ℝ, fun _ => True, PowerSeries ℝ, id, F⟩

def formalSeriesNode (F : PowerSeries ℝ) : IdentifiedNode :=
  ⟨formalSeriesData F, assemblePresentation (formalSeriesData F) F
    ⟨trivial, rfl⟩ (fun _ _ h => h)⟩

/-- The native inverse is observed through composition on a neighborhood of
zero. Analytic continuation retains the supplied connected domain. -/
def analyticInverseData (U : Set ℝ) (f : ℝ → ℝ) : PresentationData :=
  ⟨U → ℝ, fun k => ∃ g : ℝ → ℝ, AnalyticOnNhd ℝ g U ∧ ∀ x : U, g x = k x,
    Prop, fun k => ∃ g : ℝ → ℝ, AnalyticOnNhd ℝ g U ∧
      (∀ x : U, g x = k x) ∧ (fun s => g (f s)) =ᶠ[𝓝 (0 : ℝ)] id, True⟩

def analyticInverseNode (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U)
    (f g : ℝ → ℝ) (hg : AnalyticOnNhd ℝ g U) (hg0 : g 0 = 0)
    (hgf : (fun s => g (f s)) =ᶠ[𝓝 (0 : ℝ)] id)
    (hfg : (fun t => f (g t)) =ᶠ[𝓝 (0 : ℝ)] id) : IdentifiedNode := by
  refine ⟨analyticInverseData U f,
    assemblePresentation (analyticInverseData U f) (fun x => g x)
      ⟨⟨g, hg, fun _ => rfl⟩, ?_⟩ ?_⟩
  · exact propext ⟨fun _ => trivial, fun _ => ⟨g, hg, (fun _ => rfl), hgf⟩⟩
  · intro k _ ho
    obtain ⟨j, hj, hjk, hjf⟩ := (Iff.of_eq ho).mpr True.intro
    have ht : Tendsto g (𝓝 0) (𝓝 0) := by
      simpa only [hg0] using (hg 0 h0).continuousAt.tendsto
    have hjg : j =ᶠ[𝓝 (0 : ℝ)] g := by
      filter_upwards [hjf.comp_tendsto ht, hfg] with t h₁ h₂
      change j (f (g t)) = g t at h₁
      change f (g t) = t at h₂
      rwa [h₂] at h₁
    have he := hj.eqOn_of_preconnected_of_eventuallyEq hg hU h0 hjg
    funext x
    exact (hjk x).symm.trans (he x.property)

def borelInverseNode (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U) : IdentifiedNode :=
  analyticInverseNode U hU h0 borelGenerating borelInverse
    (fun x _ => analyticAt_id.mul
      ((analyticOnNhd_rexp _ (mem_univ _)).comp (analyticAt_const.sub analyticAt_id)))
    (by simp [borelInverse]) borel_inverse_analytic_germs.1 borel_inverse_analytic_germs.2

def rootedInverseNode (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U) : IdentifiedNode :=
  analyticInverseNode U hU h0 rootedAnalyticSeries.sum rootedInverse
    (fun x _ => analyticAt_id.mul
      ((analyticOnNhd_rexp _ (mem_univ _)).comp analyticAt_id.neg))
    (by simp [rootedInverse]) rooted_inverse_analytic_germs.1 rooted_inverse_analytic_germs.2

/-- P6's global converse requires analyticity only on the open positive
ray. The observed inverse germ is one-sided and imposes no extension at 0. -/
def treeInverseDensityGerm (borel : Bool) (t : ℝ) : ℝ :=
  if borel then borelInverse t / Real.exp 1 else rootedInverse t

theorem tree_inverse_density_germ (borel : Bool) (t : ℝ) :
    treeInverseDensityGerm borel t = rootedInverse t := by
  cases borel <;> simp [treeInverseDensityGerm, marked_borel_inverse_scale,
    mul_div_cancel_right₀ _ (Real.exp_ne_zero 1)]

def positiveTreeInverseData (borel : Bool) : PresentationData :=
  ⟨ScalarFunction, fun f => AnalyticOnNhd ℝ (positiveExtension f) (Ioi 0),
    Prop, fun f => ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, 0 < t → t < δ → positiveExtension f t = treeInverseDensityGerm borel t,
    True⟩

def positiveTreeInverseNode (borel : Bool) : IdentifiedNode := by
  let w : ScalarFunction := fun t => SigmaPresentations.density t
  have hw (t : ℝ) (ht : 0 < t) : positiveExtension w t = rootedInverse t := by
    simp [w, positiveExtension, ht, rootedInverse, SigmaPresentations.density]
  refine ⟨positiveTreeInverseData borel,
    assemblePresentation (positiveTreeInverseData borel) w ⟨?_, ?_⟩ ?_⟩
  · intro t ht
    have ha : AnalyticAt ℝ rootedInverse t :=
      analyticAt_id.mul ((analyticOnNhd_rexp _ (mem_univ _)).comp analyticAt_id.neg)
    apply ha.congr
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (hw s hs).symm
  · exact propext ⟨fun _ => trivial, fun _ => ⟨1, by norm_num,
      fun t ht _ => (hw t ht).trans (tree_inverse_density_germ borel t).symm⟩⟩
  · intro f hf ho
    obtain ⟨δ, hδ, hg⟩ := (Iff.of_eq ho).mpr True.intro
    have hu := inverse_germ_identifies_analytic_density (positiveExtension f) hf δ hδ
      (fun t ht hlt => (hg t ht hlt).trans (tree_inverse_density_germ borel t))
    funext t
    simpa [positiveExtension, t.property, w, SigmaPresentations.density] using hu t t.property

def rationalLabelsData : PresentationData :=
  ⟨List Bool → ℚ, fun _ => True, Prop,
    fun v => v [] = 1 ∧ (∀ w, v (false :: w) = cwLeft (v w)) ∧
      (∀ w, v (true :: w) = cwRight (v w)), True⟩

def rationalLabelsNode : IdentifiedNode := by
  refine ⟨rationalLabelsData, assemblePresentation rationalLabelsData cwValue
    ⟨trivial, ?_⟩ ?_⟩
  · exact propext ⟨fun _ => trivial, fun _ => ⟨rfl, fun _ => rfl, fun _ => rfl⟩⟩
  · intro v _ ho
    obtain ⟨hr, hl, hh⟩ := (Iff.of_eq ho).mpr True.intro
    funext w
    induction w with
    | nil => exact hr
    | cons b w ih => cases b <;> simp only [cwValue, hl, hh, ih]

def markedRationalExtensionData (right : Bool) : PresentationData :=
  ⟨GroupFunction, fun f => ∃ a b c d : ℝ,
      (∀ x : GroupCoordinate, c * x.val + d ≠ 0) ∧
      ∀ x : GroupCoordinate, f x = (a * x.val + b) / (c * x.val + d),
    {q : ℚ // 0 < q} → ℝ,
    fun f q => f ⟨q.val, by
      have h : (0 : ℝ) < q.val := by exact_mod_cast q.property
      linarith⟩,
    fun q => if right then (cwRight q.val : ℝ) else (cwLeft q.val : ℝ)⟩

def markedRationalExtensionNode (right : Bool) : IdentifiedNode := by
  let w : GroupFunction := fun x => if right then 1 + x.val else fareyLeft x.val
  refine ⟨markedRationalExtensionData right,
    assemblePresentation (markedRationalExtensionData right) w ⟨?_, ?_⟩ ?_⟩
  · cases right
    · refine ⟨1, 0, 1, 1, ?_, ?_⟩
      · intro x; have hx := x.property; dsimp; linarith
      · intro x; simp [w, fareyLeft, add_comm]
    · refine ⟨1, 1, 0, 1, ?_, ?_⟩
      · intro x; norm_num
      · intro x; simp [w, add_comm]
  · funext q
    cases right <;> simp [markedRationalExtensionData, w, cwLeft, cwRight, fareyLeft]
  · intro f hf ho
    obtain ⟨a, b, c, d, _, hf⟩ := hf
    have he (q : ℚ) (hq : 0 < q) :
        (a * q + b) / (c * q + d) =
          if right then (cwRight q : ℝ) else (cwLeft q : ℝ) := by
      have h := congrFun ho ⟨q, hq⟩
      change f _ = _ at h
      rwa [hf] at h
    funext x
    rw [hf x]
    cases right
    · exact mobius_left_positive_rational_extension a b c d he x
    · exact mobius_right_positive_rational_extension a b c d he x

def analyticRationalExtensionData : PresentationData :=
  ⟨GroupFunction, fun f => AnalyticOnNhd ℝ (groupExtension f) (Ioi (-1)),
    {q : ℚ // 0 < q} → ℝ,
    fun f q => f ⟨q.val, by
      have h : (0 : ℝ) < q.val := by exact_mod_cast q.property
      linarith⟩,
    fun q => (cwLeft q.val : ℝ)⟩

def analyticRationalExtensionNode : IdentifiedNode := by
  let w : GroupFunction := fun x => fareyLeft x.val
  have hw (x : ℝ) (hx : -1 < x) : groupExtension w x = fareyLeft x := by
    simp [groupExtension, w, hx]
  refine ⟨analyticRationalExtensionData,
    assemblePresentation analyticRationalExtensionData w ⟨?_, ?_⟩ ?_⟩
  · intro x hx
    have hf : AnalyticAt ℝ fareyLeft x :=
      analyticAt_id.div (analyticAt_const.add analyticAt_id) (by linarith [mem_Ioi.mp hx])
    apply hf.congr
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact (hw t ht).symm
  · funext q
    simp [analyticRationalExtensionData, w, fareyLeft, cwLeft]
  · intro f hf ho
    have he := analytic_farey_left_extension (groupExtension f) hf (fun q hq => by
      have hp : (-1 : ℝ) < q := by
        have h : (0 : ℝ) < q := by exact_mod_cast hq
        linarith
      simpa [analyticRationalExtensionData, groupExtension, hp, cwLeft, fareyLeft]
        using congrFun ho ⟨q, hq⟩)
    funext x
    simpa [groupExtension, x.property, w] using he x.property

theorem identified_node_unique (N : IdentifiedNode) (x : N.data.Candidate)
    (hx : N.data.admissible x ∧ N.data.observe x = N.data.value) :
    x = (N.reconstruction calibratedIntrinsic).val := by
  have h := N.reconstruction.apply_symm_apply ⟨x, hx⟩
  rw [calibrated_intrinsic_unique (N.reconstruction.symm ⟨x, hx⟩)] at h
  exact congrArg Subtype.val h.symm

def projectiveObservation (schwarzian : Bool) (f : ScalarFunction) : Prop :=
  if schwarzian then projectiveSchwarzianData.admissible f ∧
    projectiveSchwarzianData.observe f = projectiveSchwarzianData.value
  else projectiveCrossRatioData.admissible f ∧
    projectiveCrossRatioData.observe f = projectiveCrossRatioData.value

def projectivePrimitiveData (schwarzian : Bool) : PresentationData :=
  ⟨ScalarFunction × ScalarFunction,
    fun x => ∀ t > 0, HasDerivAt (positiveExtension x.1) (positiveExtension x.2 t) t,
    Prop, fun x => positiveExtension x.1 1 = 0 ∧ projectiveObservation schwarzian x.2,
    True⟩

def projectivePrimitiveNode (schwarzian : Bool) : IdentifiedNode := by
  refine ⟨projectivePrimitiveData schwarzian,
    assemblePresentation (projectivePrimitiveData schwarzian)
      ((fun t => H t), (fun t => projectiveModel t)) ⟨?_, ?_⟩ ?_⟩
  · intro t ht
    have hd := intrinsic_equality_derivative
      (positiveExtension (fun x : PositiveCoordinate => H x))
      (fun x hx => by simp [positiveExtension, hx]) t ht
    simpa [positiveExtension, ht, projectiveModel] using hd
  · apply propext
    refine ⟨fun _ => trivial, fun _ => ⟨?_, ?_⟩⟩
    · norm_num [positiveExtension, H, SigmaPresentations.H]
    · cases schwarzian
      · exact (projectiveCrossRatioNode.reconstruction calibratedIntrinsic).property
      · exact (projectiveSchwarzianNode.reconstruction calibratedIntrinsic).property
  · intro x hx ho
    obtain ⟨ha, hp⟩ := (Iff.of_eq ho).mpr True.intro
    have hf : x.2 = fun t : PositiveCoordinate => projectiveModel t := by
      cases schwarzian
      · exact identified_node_unique projectiveCrossRatioNode x.2 hp
      · exact identified_node_unique projectiveSchwarzianNode x.2 hp
    apply Prod.ext _ hf
    funext t
    have hu := projective_anchored_primitive_identifies
      (positiveExtension x.1) (positiveExtension x.2) hx ha
      (fun s hs => by simp [hf, positiveExtension, hs, projectiveModel]) t t.property
    simpa [positiveExtension, t.property] using hu

section FormalField
variable (K : Type) [Field K] [CharZero K]

def fieldToddTowerData : PresentationData :=
  ⟨PowerSeries K, fun Q => PowerSeries.constantCoeff K Q = 1,
    {n : ℕ // 0 < n} → K,
    fun Q n => PowerSeries.coeff K n.val (Q ^ (n.val + 1)), fun _ => 1⟩

def fieldToddTowerNode : IdentifiedNode := by
  refine ⟨fieldToddTowerData K,
    assemblePresentation (fieldToddTowerData K) (formalTodd K)
      ⟨formal_todd_constant K, ?_⟩ ?_⟩
  · funext n; exact formal_todd_tower K n
  · intro Q hQ ho
    exact (normalized_todd_tower_iff_exponential_quotient K Q).mp
      ⟨hQ, fun n hn => congrFun ho ⟨n, hn⟩⟩

def fieldFormalSeriesData (F : PowerSeries K) : PresentationData :=
  ⟨PowerSeries K, fun _ => True, PowerSeries K, id, F⟩

def fieldFormalSeriesNode (F : PowerSeries K) : IdentifiedNode :=
  ⟨fieldFormalSeriesData K F, assemblePresentation (fieldFormalSeriesData K F) F
    ⟨trivial, rfl⟩ (fun _ _ h => h)⟩

def fieldAhatData : PresentationData :=
  ⟨PowerSeries K, fun Q => PowerSeries.constantCoeff K Q = 1,
    PowerSeries K, fun Q => formalExponential K (1 / 2) * Q, formalTodd K⟩

def fieldAhatNode : IdentifiedNode := by
  refine ⟨fieldAhatData K, assemblePresentation (fieldAhatData K) (formalAhat K)
    ⟨formal_ahat_constant K, formal_ahat_to_todd K⟩ ?_⟩
  intro Q _ ho
  change PowerSeries K at Q
  change formalExponential K (1 / 2) * Q = formalTodd K at ho
  change Q = formalAhat K
  have hn : formalExponential K (1 / 2) ≠ 0 := by
    intro h
    have hc := congrArg (PowerSeries.constantCoeff K) h
    simp [formal_exponential_constant] at hc
  exact mul_left_cancel₀ hn (ho.trans (formal_ahat_to_todd K).symm)

def fieldLData : PresentationData :=
  ⟨PowerSeries K, fun Q => PowerSeries.constantCoeff K Q = 1,
    PowerSeries K, fun Q => PowerSeries.rescale (1 / 2 : K) Q +
      PowerSeries.C K (1 / 2) * PowerSeries.X, formalTodd K⟩

def fieldLNode : IdentifiedNode := by
  refine ⟨fieldLData K, assemblePresentation (fieldLData K) (formalL K)
    ⟨formal_L_constant K, formal_L_to_todd K⟩ ?_⟩
  intro Q _ ho
  have hr : PowerSeries.rescale (1 / 2 : K) Q =
      PowerSeries.rescale (1 / 2 : K) (formalL K) :=
    add_right_cancel (ho.trans (formal_L_to_todd K).symm)
  have h := congrArg (PowerSeries.rescale (2 : K)) hr
  simpa [PowerSeries.rescale_rescale] using h

def fieldChiData (y : K) (_hy : y ≠ -1) : PresentationData :=
  ⟨PowerSeries K, fun Q => PowerSeries.constantCoeff K Q = 1,
    PowerSeries K, characteristicChiToTodd K y, formalTodd K⟩

def fieldChiNode (y : K) (hy : y ≠ -1) : IdentifiedNode := by
  refine ⟨fieldChiData K y hy, assemblePresentation (fieldChiData K y hy) (formalChi K y)
    ⟨formal_chi_constant K y, formal_chi_recovers_todd K y hy⟩ ?_⟩
  intro Q _ ho
  calc
    Q = characteristicToddToChi K y (characteristicChiToTodd K y Q) :=
      (characteristic_Todd_chi_inverse K y hy Q).symm
    _ = characteristicToddToChi K y (formalTodd K) := congrArg _ ho
    _ = formalChi K y := rfl

end FormalField

def productPresentationData (P Q : PresentationData) : PresentationData :=
  ⟨P.Candidate × Q.Candidate, fun x => P.admissible x.1 ∧ Q.admissible x.2,
    P.Observation × Q.Observation, fun x => (P.observe x.1, Q.observe x.2),
    (P.value, Q.value)⟩

def productNode (A B : IdentifiedNode) : IdentifiedNode := by
  let a := A.reconstruction calibratedIntrinsic
  let b := B.reconstruction calibratedIntrinsic
  refine ⟨productPresentationData A.data B.data,
    assemblePresentation (productPresentationData A.data B.data) (a.val, b.val)
      ⟨⟨a.property.1, b.property.1⟩, Prod.ext a.property.2 b.property.2⟩ ?_⟩
  intro x hx ho
  exact Prod.ext
    (identified_node_unique A x.1 ⟨hx.1, congrArg Prod.fst ho⟩)
    (identified_node_unique B x.2 ⟨hx.2, congrArg Prod.snd ho⟩)

/-- Numerical labels and their declared full-domain extension remain in the
same presentation. A bare unlabelled tree is not a member of this family. -/
def markedRationalNode : IdentifiedNode :=
  productNode rationalLabelsNode
    (productNode (markedRationalExtensionNode false) (markedRationalExtensionNode true))

def analyticMarkedRationalNode : IdentifiedNode :=
  productNode rationalLabelsNode analyticRationalExtensionNode

private theorem group_farey_integral (t : ℝ) (ht : 0 < t) :
    (∫ s in (0 : ℝ)..t - 1,
      groupExtension (fun x : GroupCoordinate => fareyLeft x) s) = I t := by
  change _ = SigmaBase.potential t
  rw [← farey_left_integral ht]
  apply intervalIntegral.integral_congr
  intro s hs
  have hp : -1 < s := by
    rcases le_total (0 : ℝ) (t - 1) with h | h
    · rw [uIcc_of_le h] at hs
      linarith [hs.1]
    · rw [uIcc_of_ge h] at hs
      linarith [hs.1]
  simp [groupExtension, hp]

theorem marked_rational_scalar_recovery (x : markedRationalNode.data.Solution)
    (t : ℝ) (ht : 0 < t) :
    (∫ s in (0 : ℝ)..t - 1, groupExtension x.val.2.1 s) = I t := by
  rw [identified_node_unique markedRationalNode x.val x.property]
  exact group_farey_integral t ht

theorem analytic_marked_rational_scalar_recovery
    (x : analyticMarkedRationalNode.data.Solution) (t : ℝ) (ht : 0 < t) :
    (∫ s in (0 : ℝ)..t - 1, groupExtension x.val.2 s) = I t := by
  rw [identified_node_unique analyticMarkedRationalNode x.val x.property]
  exact group_farey_integral t ht

/-- The paper's finite list of presentation families. Parameters retain the
coefficient field, marked chi parameter, and analytic continuation domain.
Each distinct observation is a separate constructor. -/
inductive CompletePresentation (K : Type) [Field K] [CharZero K]
  | available (A : AvailablePresentation)
  | typedCompletion (slopeAnchor : Bool)
  | selfConcordance (unsigned : Bool)
  | hessianMetric | exactLegendre
  | projectivePrimitive (schwarzian : Bool)
  | gammaLaplace | entropyMaximizer | orientedPoissonKL | orientedExponentialKL | orientedGaussianKL
  | nativeSurvival | nativeLogistic | secondOrderDensity | causalGreen
  | bernsteinIntegerTail (N : ℕ)
  | bernsteinRepresentation (N : ℕ)
  | toddTower | toddSeries | ahatSeries | lSeries
  | completeAhatSeries | completeLSeries
  | completeChiSeries (y : K) (hy : y ≠ -1)
  | markedChi (y : K) (hy : y ≠ -1)
  | inverseTodd | inverseAhat | inverseL
  | inverseChi (y : K) (hy : y ≠ -1)
  | analyticTodd (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U)
  | analyticAhat (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U)
  | analyticL (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U)
  | analyticChi (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U)
      (y : ℝ) (hy : y ≠ -1)
  | analyticInverseTodd (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U)
  | analyticInverseAhat (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U)
  | analyticInverseL (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U)
  | analyticInverseChi (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U)
      (y : ℝ) (hy : y ≠ -1) (hn : ∀ x ∈ U, realChi y x ≠ 0)
  | borelInverse (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U)
  | rootedInverse (U : Set ℝ) (hU : IsPreconnected U) (h0 : 0 ∈ U)
  | positiveTreeInverse (borel : Bool)
  | markedRational | analyticMarkedRational

def completePresentation (K : Type) [Field K] [CharZero K] :
    CompletePresentation K → IdentifiedNode
  | .available A => availablePresentation A
  | .typedCompletion b => typedCompletionNode b
  | .selfConcordance b => selfConcordanceNode b
  | .hessianMetric => hessianMetricNode
  | .exactLegendre => exactLegendreNode
  | .projectivePrimitive b => projectivePrimitiveNode b
  | .gammaLaplace => gammaLaplaceNode
  | .entropyMaximizer => entropyMaximizerNode
  | .orientedPoissonKL => orientedPoissonKLNode
  | .orientedExponentialKL => orientedExponentialKLNode
  | .orientedGaussianKL => orientedGaussianKLNode
  | .nativeSurvival => nativeSurvivalNode
  | .nativeLogistic => nativeLogisticNode
  | .secondOrderDensity => secondOrderDensityNode
  | .causalGreen => causalGreenNode
  | .bernsteinIntegerTail N => bernsteinIntegerTailNode N
  | .bernsteinRepresentation N => bernsteinRepresentationNode N
  | .toddTower => fieldToddTowerNode K
  | .toddSeries => fieldFormalSeriesNode K (formalTodd K)
  | .ahatSeries => fieldAhatNode K
  | .lSeries => fieldLNode K
  | .completeAhatSeries => fieldFormalSeriesNode K (formalAhat K)
  | .completeLSeries => fieldFormalSeriesNode K (formalL K)
  | .completeChiSeries y _ => fieldFormalSeriesNode K (formalChi K y)
  | .markedChi y hy => fieldChiNode K y hy
  | .inverseTodd => fieldFormalSeriesNode K (formalTodd K)⁻¹
  | .inverseAhat => fieldFormalSeriesNode K (formalAhat K)⁻¹
  | .inverseL => fieldFormalSeriesNode K (formalL K)⁻¹
  | .inverseChi y _ => fieldFormalSeriesNode K (formalChi K y)⁻¹
  | .analyticTodd U hU h0 => connectedToddNode U hU h0
  | .analyticAhat U hU h0 => connectedAhatNode U hU h0
  | .analyticL U hU h0 => connectedLNode U hU h0
  | .analyticChi U hU h0 y hy => connectedChiNode U hU h0 y hy
  | .analyticInverseTodd U hU h0 => connectedInverseToddNode U hU h0
  | .analyticInverseAhat U hU h0 => connectedInverseAhatNode U hU h0
  | .analyticInverseL U hU h0 => connectedInverseLNode U hU h0
  | .analyticInverseChi U hU h0 y hy hn => connectedInverseChiNode U hU h0 y hy hn
  | .borelInverse U hU h0 => borelInverseNode U hU h0
  | .rootedInverse U hU h0 => rootedInverseNode U hU h0
  | .positiveTreeInverse b => positiveTreeInverseNode b
  | .markedRational => markedRationalNode
  | .analyticMarkedRational => analyticMarkedRationalNode

def completeReconstruction (K : Type) [Field K] [CharZero K]
    (A B : CompletePresentation K) :
    (completePresentation K A).data.Solution ≃ (completePresentation K B).data.Solution :=
  (completePresentation K A).reconstruction.symm.trans
    (completePresentation K B).reconstruction

theorem complete_intrinsic_roundtrips (K : Type) [Field K] [CharZero K]
    (A : CompletePresentation K) :
    (∀ s, (completePresentation K A).reconstruction.symm
      ((completePresentation K A).reconstruction s) = s) ∧
    (∀ x, (completePresentation K A).reconstruction
      ((completePresentation K A).reconstruction.symm x) = x) :=
  ⟨(completePresentation K A).reconstruction.symm_apply_apply,
    (completePresentation K A).reconstruction.apply_symm_apply⟩

theorem complete_reconstruction_roundtrip (K : Type) [Field K] [CharZero K]
    (A B : CompletePresentation K) (x : (completePresentation K A).data.Solution) :
    completeReconstruction K B A (completeReconstruction K A B x) = x := by
  simp [completeReconstruction]

theorem complete_presentation_unique (K : Type) [Field K] [CharZero K]
    (A : CompletePresentation K) :
    ∃! x : (completePresentation K A).data.Candidate,
      (completePresentation K A).data.admissible x ∧
      (completePresentation K A).data.observe x = (completePresentation K A).data.value := by
  let N := completePresentation K A
  exact ⟨(N.reconstruction calibratedIntrinsic).val,
    (N.reconstruction calibratedIntrinsic).property, identified_node_unique N⟩

def IntrinsicObject.Analytic (s : IntrinsicObject) : Prop :=
  ∃ g : ℝ → ℝ, AnalyticOnNhd ℝ g (Ioi 0) ∧ ∀ t : PositiveCoordinate, s.val t = g t

theorem calibrated_intrinsic_analytic (s : IntrinsicObject) : s.Analytic := by
  rw [calibrated_intrinsic_unique s]
  refine ⟨H, ?_, fun _ => rfl⟩
  intro t ht
  have he : H = fun x => -SigmaBase.potential x :=
    funext SigmaPresentations.H_eq_neg_potential
  rw [he]
  exact (potential_analyticAt t ht).neg

/-- Existence and uniqueness use the calibrated intrinsic analytic object;
the full enumeration supplies every encoder and identifying decoder. -/
theorem global_reconstruction_closure (K : Type) [Field K] [CharZero K] :
    (∃! s : IntrinsicObject, s.Analytic) ∧
    (∀ A : CompletePresentation K,
      Nonempty (IntrinsicObject ≃ (completePresentation K A).data.Solution)) ∧
    (∀ A B : CompletePresentation K,
      Nonempty ((completePresentation K A).data.Solution ≃
        (completePresentation K B).data.Solution)) :=
  ⟨⟨calibratedIntrinsic, calibrated_intrinsic_analytic calibratedIntrinsic,
      fun s _ => calibrated_intrinsic_unique s⟩,
    (fun A => ⟨(completePresentation K A).reconstruction⟩),
    (fun A B => ⟨completeReconstruction K A B⟩)⟩

end
end Sigma.Closure
