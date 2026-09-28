import SigmaClosure
import SigmaProbInverse
import SigmaOpMomentInverse
import SigmaOpLaguerreL2
import SigmaSteinMomentLimits
import SigmaRealToddTower
import SigmaProbStieltjes
import SigmaOpCoordinateProjections
import SigmaProbPoisson
import SigmaProbGumbel
import SigmaProbGWBorel
import SigmaProbCompletionSamples
import SigmaRealTreesBorel
import SigmaBregman
import SigmaProjectiveForward
import SigmaProbHaar
import SigmaFenchelConverseLSC
import SigmaProbWeights
import SigmaProbEquilibrium
import SigmaProbPoissonInverse
import SigmaRealCharacteristicChi
import SigmaProbSurvival
import SigmaOpGammaShapeThreeEvolution
import SigmaOpLinkedMixingCoordinate
import SigmaAffineCurvature
import SigmaProbCanonicalPair
import SigmaRealCharacteristicGerm

namespace Sigma.Closure
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff

/-- A calibrated intrinsic object on the paper's marked positive coordinate.
Its differential certificate is retained, rather than equality to a recipe. -/
def IntrinsicObject := {F : ScalarFunction //
  ∃ G : ℝ → ℝ, DifferentialCoreClause G ∧ ∀ t : PositiveCoordinate, F t = G t}

def calibratedIntrinsic : IntrinsicObject :=
  ⟨fun t => H t, H, (differential_core_iff H).mpr (fun _ _ => rfl), fun _ => rfl⟩

theorem calibrated_intrinsic_unique (s : IntrinsicObject) : s = calibratedIntrinsic := by
  apply Subtype.ext
  obtain ⟨G, hG, he⟩ := s.property
  funext t
  exact (he t).trans (differential_core_identifies G hG t t.property)

/-- The candidate class and the actual observation map are separate data.
No inverse or uniqueness conclusion is assumed in this record. -/
structure PresentationData where
  Candidate : Type
  admissible : Candidate → Prop
  Observation : Type
  observe : Candidate → Observation
  value : Observation

def PresentationData.Solution (P : PresentationData) :=
  {x : P.Candidate // P.admissible x ∧ P.observe x = P.value}

/-- The generic assembly uses a proved local identifying theorem. Every
concrete instance below supplies that proof from its own native candidate class. -/
def assemblePresentation (P : PresentationData) (w : P.Candidate)
    (hw : P.admissible w ∧ P.observe w = P.value)
    (hunique : ∀ x, P.admissible x → P.observe x = P.value → x = w) :
    IntrinsicObject ≃ P.Solution where
  toFun _ := ⟨w, hw⟩
  invFun _ := calibratedIntrinsic
  left_inv s := (calibrated_intrinsic_unique s).symm
  right_inv x := Subtype.ext (hunique x.val x.property.1 x.property.2).symm

structure IdentifiedNode where
  data : PresentationData
  reconstruction : IntrinsicObject ≃ data.Solution

def intrinsicHData : PresentationData :=
  ⟨ScalarFunction, fun _ => True, ScalarFunction, id, fun t => H t⟩

def intrinsicIData : PresentationData :=
  ⟨ScalarFunction, fun _ => True, ScalarFunction, id, fun t => I t⟩

def intrinsicDensityData : PresentationData :=
  ⟨PositiveFunction, fun _ => True, ScalarFunction, Subtype.val, fun t => p t⟩

def intrinsicHNode : IdentifiedNode :=
  ⟨intrinsicHData, assemblePresentation intrinsicHData (fun t => H t)
    ⟨trivial, rfl⟩ (fun _ _ h => h)⟩

def intrinsicINode : IdentifiedNode :=
  ⟨intrinsicIData, assemblePresentation intrinsicIData (fun t => I t)
    ⟨trivial, rfl⟩ (fun _ _ h => h)⟩

def intrinsicDensityNode : IdentifiedNode :=
  ⟨intrinsicDensityData, assemblePresentation intrinsicDensityData
    ⟨fun t => p t, fun t => SigmaPresentations.density_pos t.property⟩
    ⟨trivial, rfl⟩ (fun _ _ h => Subtype.ext h)⟩

def gammaCharacteristicData : PresentationData :=
  ⟨Measure ℝ, IsProbabilityMeasure, ℝ → ℂ, probabilityCharacteristic, gammaCharacteristic⟩

def gammaCharacteristicNode : IdentifiedNode := by
  refine ⟨gammaCharacteristicData,
    assemblePresentation gammaCharacteristicData gammaProbability
      ⟨(show IsProbabilityMeasure gammaProbability from inferInstance), ?_⟩ ?_⟩
  · funext x
    exact gamma_probability_characteristic x
  · intro μ hμ he
    letI : IsProbabilityMeasure μ := hμ
    exact gamma_characteristic_identifies_real_line_measure μ (congrFun he)

def gammaLawData : PresentationData :=
  ⟨Measure ℝ, IsProbabilityMeasure, Measure ℝ, id, gammaProbability⟩

def gammaLawNode : IdentifiedNode :=
  ⟨gammaLawData, assemblePresentation gammaLawData gammaProbability
    ⟨(show IsProbabilityMeasure gammaProbability from inferInstance), rfl⟩
    (fun _ _ h => h)⟩

def gammaMellinData : PresentationData :=
  ⟨Measure ℝ, fun μ => IsProbabilityMeasure μ ∧ ∀ᵐ t ∂μ, 0 < t,
    ℝ → ℂ, fun μ x => ∫ t : ℝ, (t : ℂ) ^ (Complex.I*(x : ℂ)) ∂μ,
    fun x => Complex.Gamma (2+Complex.I*(x : ℂ))⟩

def gammaMellinNode : IdentifiedNode := by
  refine ⟨gammaMellinData, assemblePresentation gammaMellinData gammaProbability
    ⟨⟨inferInstance, operator_integer_samples_ae_pos gammaProbability
      operator_gamma_probability_integer_samples⟩, ?_⟩ ?_⟩
  · funext x
    exact gamma_mellin_on_imaginary_line x
  · intro μ hμ he
    letI := hμ.1
    exact imaginary_mellin_identifies_positive_probability μ hμ.2 (congrFun he)

def gammaStieltjesData : PresentationData :=
  ⟨Measure ℝ, fun μ => IsFiniteMeasure μ ∧ ∀ᵐ t ∂μ, 0 ≤ t,
    PositiveCoordinate → ℝ, fun μ x => probabilityStieltjes μ x,
    fun x => probabilityStieltjes gammaProbability x⟩

def gammaStieltjesNode : IdentifiedNode := by
  refine ⟨gammaStieltjesData, assemblePresentation gammaStieltjesData gammaProbability
    ⟨⟨inferInstance, ?_⟩, rfl⟩ ?_⟩
  · exact (operator_integer_samples_ae_pos gammaProbability
      operator_gamma_probability_integer_samples).mono (fun _ h => h.le)
  · intro μ hμ he
    letI := hμ.1
    exact probability_stieltjes_unique μ gammaProbability hμ.2
      ((operator_integer_samples_ae_pos gammaProbability
        operator_gamma_probability_integer_samples).mono (fun _ h => h.le))
      (fun x hx => congrFun he ⟨x, hx⟩)

/-- This observation retains the actual maximal coordinate multiplier and
the constant vector, not merely the generator's unmarked spectrum. -/
def gammaMarkedCoordinateData : PresentationData :=
  ⟨{μ : Measure ℝ // IsProbabilityMeasure μ}, fun _ => True, Prop,
    fun P => @Exists (Lp ℂ 2 P.val ≃ₗᵢ[ℂ] Lp ℂ 2 gammaProbability) (fun U =>
      @CoordinateMultiplicationIntertwines P.val P.property gammaProbability inferInstance U ∧
      U (@coordinateConstantOne P.val P.property) = coordinateConstantOne gammaProbability),
    True⟩

def gammaMarkedCoordinateNode : IdentifiedNode := by
  refine ⟨gammaMarkedCoordinateData, assemblePresentation gammaMarkedCoordinateData
    ⟨gammaProbability, inferInstance⟩ ⟨trivial, ?_⟩ ?_⟩
  · apply propext
    constructor
    · intro _; trivial
    · intro _
      exact ⟨LinearIsometryEquiv.refl ℂ _, (fun _ hf => ⟨hf, rfl⟩), rfl⟩
  · intro P _ he
    have hp : gammaMarkedCoordinateData.observe P := (Iff.of_eq he).mpr True.intro
    obtain ⟨U, hU, hone⟩ := hp
    apply Subtype.ext
    letI := P.property
    exact marked_multiplication_unitary_preserves_probability P.val gammaProbability U hU hone

def gammaMomentsData : PresentationData :=
  ⟨Measure ℝ, fun _ => True, ℕ → ℝ,
    fun μ n => ∫ t : ℝ, t^n ∂μ, fun n => ((n+1).factorial : ℝ)⟩

def gammaMomentsNode : IdentifiedNode := by
  refine ⟨gammaMomentsData,
    assemblePresentation gammaMomentsData gammaProbability ⟨trivial, ?_⟩ ?_⟩
  · funext n
    exact gamma_probability_moments n
  · intro μ _ he
    exact operator_full_line_factorial_moment_unique μ (congrFun he)

def gammaIntegerLaplaceData : PresentationData :=
  ⟨Measure ℝ, IsFiniteMeasure, ℕ → ℝ,
    fun μ n => ∫ t : ℝ, Real.exp (-(n : ℝ)*t) ∂μ,
    fun n => (1/(1+(n : ℝ))) ^ 2⟩

def gammaIntegerLaplaceNode : IdentifiedNode := by
  refine ⟨gammaIntegerLaplaceData,
    assemblePresentation gammaIntegerLaplaceData gammaProbability
      ⟨(show IsFiniteMeasure gammaProbability from inferInstance), ?_⟩ ?_⟩
  · funext n
    exact operator_gamma_probability_integer_samples n
  · intro μ hμ he
    letI : IsFiniteMeasure μ := hμ
    exact operator_full_line_mixing_characterization μ (congrFun he)

abbrev SteinTest := {f : ℝ → ℝ // ContDiff ℝ ∞ f ∧ HasCompactSupport f}

def gammaSteinData : PresentationData :=
  ⟨Measure ℝ, IsProbabilityMeasure, SteinTest → ℝ,
    fun μ f => ∫ t : ℝ, t*deriv f.val t + (2-t)*f.val t ∂μ, fun _ => 0⟩

def gammaSteinNode : IdentifiedNode := by
  refine ⟨gammaSteinData,
    assemblePresentation gammaSteinData gammaProbability
      ⟨(show IsProbabilityMeasure gammaProbability from inferInstance), ?_⟩ ?_⟩
  · funext f
    exact gamma_probability_weak_stein f.val f.property.1 f.property.2
  · intro μ hμ he
    letI : IsProbabilityMeasure μ := hμ
    apply (weak_stein_characterization μ).mp
    intro f hf hc
    exact congrFun he ⟨f, hf, hc⟩

def gammaLaguerreData : PresentationData :=
  ⟨Measure ℝ, fun μ => IsProbabilityMeasure μ ∧
      ∀ P : Polynomial ℝ, Integrable (fun t : ℝ => P.eval t) μ,
    {n : ℕ // n ≠ 0} → ℝ,
    fun μ n => ∫ t : ℝ, opLaguerre n.val t ∂μ, fun _ => 0⟩

def gammaLaguerreNode : IdentifiedNode := by
  refine ⟨gammaLaguerreData,
    assemblePresentation gammaLaguerreData gammaProbability ⟨⟨inferInstance, ?_⟩, ?_⟩ ?_⟩
  · intro P
    exact gamma_polynomial_integrable P
  · funext n
    exact operator_gamma_laguerre_orthogonality n.val n.property
  · intro μ hμ he
    letI := hμ.1
    exact (operator_marked_laguerre_characterization μ hμ.2).mp
      (fun n hn => congrFun he ⟨n, hn⟩)

def toddTowerData : PresentationData :=
  ⟨PowerSeries ℚ, fun Q => PowerSeries.constantCoeff ℚ Q = 1,
    {n : ℕ // 0 < n} → ℚ,
    fun Q n => PowerSeries.coeff ℚ n.val (Q^(n.val+1)), fun _ => 1⟩

def toddTowerNode : IdentifiedNode := by
  refine ⟨toddTowerData,
    assemblePresentation toddTowerData (formalTodd ℚ) ⟨formal_todd_constant ℚ, ?_⟩ ?_⟩
  · funext n
    exact formal_todd_tower ℚ n.val
  · intro Q hQ he
    exact (normalized_todd_tower_iff_exponential_quotient ℚ Q).mp
      ⟨hQ, fun n hn => congrFun he ⟨n, hn⟩⟩

def ahatSeriesData : PresentationData :=
  ⟨PowerSeries ℚ, fun Q => PowerSeries.constantCoeff ℚ Q = 1,
    PowerSeries ℚ,
    fun Q => formalExponential ℚ (1/2) * Q,
    formalTodd ℚ⟩

def ahatSeriesNode : IdentifiedNode := by
  refine ⟨ahatSeriesData,
    assemblePresentation ahatSeriesData (formalAhat ℚ)
      ⟨formal_ahat_constant ℚ, formal_ahat_to_todd ℚ⟩ ?_⟩
  intro Q _ he
  change PowerSeries ℚ at Q
  change formalExponential ℚ (1/2) * Q = formalTodd ℚ at he
  change Q = formalAhat ℚ
  have hn : formalExponential ℚ (1/2) ≠ 0 := by
    intro hz
    have hc := congrArg (PowerSeries.constantCoeff ℚ) hz
    simp [formal_exponential_constant] at hc
  exact mul_left_cancel₀ hn (he.trans (formal_ahat_to_todd ℚ).symm)

def lSeriesData : PresentationData :=
  ⟨PowerSeries ℚ, fun Q => PowerSeries.constantCoeff ℚ Q = 1,
    PowerSeries ℚ,
    fun Q => PowerSeries.rescale (1/2 : ℚ) Q +
      PowerSeries.C ℚ (1/2) * PowerSeries.X,
    formalTodd ℚ⟩

def lSeriesNode : IdentifiedNode := by
  refine ⟨lSeriesData,
    assemblePresentation lSeriesData (formalL ℚ)
      ⟨formal_L_constant ℚ, formal_L_to_todd ℚ⟩ ?_⟩
  intro Q _ he
  have hr : PowerSeries.rescale (1/2 : ℚ) Q =
      PowerSeries.rescale (1/2 : ℚ) (formalL ℚ) :=
    add_right_cancel (he.trans (formal_L_to_todd ℚ).symm)
  have h := congrArg (PowerSeries.rescale (2 : ℚ)) hr
  simpa [PowerSeries.rescale_rescale] using h

/-- The parameter is part of the node, and the inverse uses precisely the
nondegeneracy mark y ≠ -1. -/
def markedChiData (y : ℚ) (_hy : y ≠ -1) : PresentationData :=
  ⟨PowerSeries ℚ, fun Q => PowerSeries.constantCoeff ℚ Q = 1,
    PowerSeries ℚ,
    characteristicChiToTodd ℚ y,
    formalTodd ℚ⟩

def markedChiNode (y : ℚ) (hy : y ≠ -1) : IdentifiedNode := by
  refine ⟨markedChiData y hy,
    assemblePresentation (markedChiData y hy) (formalChi ℚ y)
      ⟨formal_chi_constant ℚ y, formal_chi_recovers_todd ℚ y hy⟩ ?_⟩
  intro Q _ he
  calc
    Q = characteristicToddToChi ℚ y (characteristicChiToTodd ℚ y Q) :=
      (characteristic_Todd_chi_inverse ℚ y hy Q).symm
    _ = characteristicToddToChi ℚ y (formalTodd ℚ) := congrArg _ he
    _ = formalChi ℚ y := rfl

/-- A supplied real-analytic representative is identified by its complete
formal germ only on the retained connected continuation class. -/
def analyticSeriesData (F : PowerSeries ℝ) : PresentationData :=
  ⟨ℝ → ℝ, fun f => AnalyticOnNhd ℝ f Set.univ,
    Prop, fun f => HasRealFormalGerm f F, True⟩

def analyticSeriesNode (f : ℝ → ℝ) (F : PowerSeries ℝ)
    (hf : ∀ u, AnalyticAt ℝ f u) (hg : HasRealFormalGerm f F) : IdentifiedNode := by
  let hfa : AnalyticOnNhd ℝ f Set.univ := fun u _ => hf u
  refine ⟨analyticSeriesData F,
    assemblePresentation (analyticSeriesData F) f
      ⟨hfa, propext ⟨fun _ => True.intro, fun _ => hg⟩⟩ ?_⟩
  intro g hga he
  have hgg : HasRealFormalGerm g F := (Iff.of_eq he).mpr True.intro
  have hEq := real_formal_germ_global_recovery hgg hg hga hfa
    isPreconnected_univ (Set.mem_univ 0)
  funext u
  exact hEq (Set.mem_univ u)

def analyticToddNode : IdentifiedNode :=
  analyticSeriesNode realTodd (formalTodd ℝ)
    real_todd_analytic real_todd_formal_germ

def analyticAhatNode : IdentifiedNode :=
  analyticSeriesNode realAhat (formalAhat ℝ)
    real_ahat_analytic real_ahat_formal_germ

def analyticLNode : IdentifiedNode :=
  analyticSeriesNode realLgenus (formalL ℝ)
    real_lgenus_analytic real_lgenus_formal_germ

def analyticChiNode (y : ℚ) (_hy : y ≠ -1) : IdentifiedNode :=
  analyticSeriesNode (realChi (y : ℝ)) (formalChi ℝ (y : ℝ))
    (real_chi_analytic (y : ℝ)) (real_chi_formal_germ (y : ℝ))

/-- Extending a function on the marked positive coordinate is only a device for
stating the local differential observations; its values off that coordinate
play no role in the candidate or the inverse. -/
def positiveExtension (F : ScalarFunction) (t : ℝ) : ℝ :=
  if h : 0 < t then F ⟨t, h⟩ else 0

private theorem canonicalH_extension (t : ℝ) (ht : 0 < t) :
    positiveExtension (fun x : PositiveCoordinate => H x.val) t = H t := by
  simp [positiveExtension, ht]

private theorem canonicalH_extension_differentiable (t : ℝ) (ht : 0 < t) :
    DifferentiableAt ℝ (positiveExtension (fun x : PositiveCoordinate => H x.val)) t :=
  (intrinsic_equality_derivative _ canonicalH_extension t ht).differentiableAt

def calibratedCurvatureData : PresentationData :=
  ⟨ScalarFunction,
    fun F => ∀ t > 0, DifferentiableAt ℝ (positiveExtension F) t,
    Prop,
    fun F => positiveExtension F 1 = 0 ∧ deriv (positiveExtension F) 1 = 0 ∧
      ∀ t > 0, HasDerivAt (deriv (positiveExtension F)) (-(1/t^2)) t,
    True⟩

def calibratedCurvatureNode : IdentifiedNode := by
  refine ⟨calibratedCurvatureData,
    assemblePresentation calibratedCurvatureData (fun t => H t)
      ⟨canonicalH_extension_differentiable, ?_⟩ ?_⟩
  · apply propext
    constructor
    · intro _; trivial
    · intro _
      refine ⟨?_, ?_, ?_⟩
      · norm_num [positiveExtension, H, SigmaPresentations.H]
      · have hd := (intrinsic_equality_derivative _ canonicalH_extension 1 (by norm_num)).deriv
        simpa using hd
      · exact intrinsic_equality_curvature _ canonicalH_extension
  · intro F hd he
    obtain ⟨hv, hs, hc⟩ := (Iff.of_eq he).mpr True.intro
    funext t
    have hu := curvature_reconstruction (positiveExtension F) hd hc hv hs t.val t.property
    simpa [positiveExtension, t.property] using hu

def calibratedRiccatiData : PresentationData :=
  ⟨ScalarFunction,
    fun F => ∀ t > 0, DifferentiableAt ℝ (positiveExtension F) t,
    Prop,
    fun F => positiveExtension F 1 = 0 ∧ deriv (positiveExtension F) 1 = 0 ∧
      ∀ t > 0,
        HasDerivAt (deriv (positiveExtension F))
          (-(deriv (positiveExtension F) t + 1)^2) t,
    True⟩

def calibratedRiccatiNode : IdentifiedNode := by
  refine ⟨calibratedRiccatiData,
    assemblePresentation calibratedRiccatiData (fun t => H t)
      ⟨canonicalH_extension_differentiable, ?_⟩ ?_⟩
  · apply propext
    constructor
    · intro _; trivial
    · intro _
      have hv : positiveExtension (fun t : PositiveCoordinate => H t) 1 = 0 := by
        norm_num [positiveExtension, H, SigmaPresentations.H]
      have hs : deriv (positiveExtension (fun t : PositiveCoordinate => H t)) 1 = 0 := by
        have hd := (intrinsic_equality_derivative _ canonicalH_extension 1 (by norm_num)).deriv
        simpa using hd
      exact ⟨hv, hs, (calibrated_riccati_iff _
        canonicalH_extension_differentiable hv hs).mpr canonicalH_extension⟩
  · intro F hd he
    obtain ⟨hv, hs, hr⟩ := (Iff.of_eq he).mpr True.intro
    funext t
    have hu := riccati_reconstruction (positiveExtension F) hd hr hv hs t.val t.property
    simpa [positiveExtension, t.property] using hu

def recenteringData : PresentationData :=
  ⟨ScalarFunction,
    fun F => ∀ t > 0, DifferentiableAt ℝ (positiveExtension F) t,
    Prop,
    fun F => HasDerivAt (deriv (positiveExtension F)) (-1) 1 ∧
      ∀ a > 0, ∀ v > 0,
        positiveExtension F (a*v) - positiveExtension F a -
          a*deriv (positiveExtension F) a*(v-1) = positiveExtension F v,
    True⟩

def recenteringNode : IdentifiedNode := by
  refine ⟨recenteringData,
    assemblePresentation recenteringData (fun t => H t)
      ⟨canonicalH_extension_differentiable, ?_⟩ ?_⟩
  · apply propext
    constructor
    · intro _; trivial
    · intro _
      have h2 : HasDerivAt
          (deriv (positiveExtension (fun t : PositiveCoordinate => H t))) (-1) 1 := by
        convert intrinsic_equality_curvature _ canonicalH_extension 1 (by norm_num) using 1
        norm_num
      exact ⟨h2, (recentering_iff _ canonicalH_extension_differentiable h2).mpr
        canonicalH_extension⟩
  · intro F hd he
    obtain ⟨h2, hr⟩ := (Iff.of_eq he).mpr True.intro
    funext t
    have hu := recentering_reconstruction (positiveExtension F) hd hr h2 t.val t.property
    simpa [positiveExtension, t.property] using hu

def differentialCoreData : PresentationData :=
  ⟨ScalarFunction, fun _ => True, Prop,
    fun F => DifferentialCoreClause (positiveExtension F), True⟩

def differentialCoreNode : IdentifiedNode := by
  refine ⟨differentialCoreData,
    assemblePresentation differentialCoreData (fun t => H t) ⟨trivial, ?_⟩ ?_⟩
  · apply propext
    constructor
    · intro _; trivial
    · intro _
      apply (differential_core_iff _).mpr
      intro t ht
      simp [positiveExtension, ht]
  · intro F _ he
    have hF : DifferentialCoreClause (positiveExtension F) :=
      (Iff.of_eq he).mpr True.intro
    funext t
    have h := differential_core_identifies (positiveExtension F) hF t t.property
    simpa [positiveExtension, t.property] using h

def exactFlowData : PresentationData :=
  ⟨ScalarFunction, fun _ => True, Prop,
    fun q => positiveExtension q 1 = 1 ∧
      ∀ t > 0, ∀ s : ℝ, 0 < t+s →
        positiveExtension q (t+s) =
          positiveExtension q t / (1+s*positiveExtension q t),
    True⟩

def exactFlowNode : IdentifiedNode := by
  refine ⟨exactFlowData,
    assemblePresentation exactFlowData (fun t => 1/t.val)
      ⟨trivial, ?_⟩ ?_⟩
  · apply propext
    constructor
    · intro _; trivial
    · intro _
      constructor
      · simp [positiveExtension]
      · intro t ht s hts
        simpa [positiveExtension, ht, hts] using
          exact_flow_of_reciprocal t s ht hts
  · intro q _ he
    obtain ⟨h1, hf⟩ := (Iff.of_eq he).mpr True.intro
    funext t
    have hu := exact_flow_identifies (positiveExtension q) h1 hf t.val t.property
    simpa [positiveExtension, t.property] using hu

abbrev GroupCoordinate := {x : ℝ // -1 < x}
abbrev GroupFunction := GroupCoordinate → ℝ

def groupExtension (L : GroupFunction) (x : ℝ) : ℝ :=
  if h : -1 < x then L ⟨x, h⟩ else 0

def groupLogData : PresentationData :=
  ⟨GroupFunction, fun _ => True, Prop,
    fun L => HasDerivAt (groupExtension L) 1 0 ∧
      ∀ x > -1, ∀ y > -1,
        groupExtension L (star x y) = groupExtension L x + groupExtension L y,
    True⟩

def groupLogNode : IdentifiedNode := by
  refine ⟨groupLogData,
    assemblePresentation groupLogData (fun x => Real.log (1 + x.val))
      ⟨trivial, ?_⟩ ?_⟩
  · apply propext
    constructor
    · intro _; trivial
    · intro _
      constructor
      · have hd : HasDerivAt (fun x : ℝ => Real.log (1 + x)) 1 0 := by
          convert (((hasDerivAt_id (0 : ℝ)).const_add 1).log (by norm_num)) using 1
          simp
        apply hd.congr_of_eventuallyEq
        filter_upwards [isOpen_Ioi.mem_nhds (show (-1 : ℝ) < 0 by norm_num)]
          with x hx
        change -1 < x at hx
        simp [groupExtension, hx]
      · intro x hx y hy
        simp [groupExtension, hx, hy, SigmaBase.star_closed hx hy,
          SigmaBase.log_star hx hy]
  · intro L _ he
    obtain ⟨h0, hh⟩ := (Iff.of_eq he).mpr True.intro
    funext x
    have h := normalized_group_log_unique_at_identity (groupExtension L) h0 hh
      x.val x.property
    simpa [groupExtension, x.property] using h

def groupCocycleData : PresentationData :=
  ⟨GroupFunction, fun _ => True, Prop,
    fun L => HasDerivAt (groupExtension L) 0 0 ∧
      ∀ x > -1, ∀ y > -1,
        groupExtension L (star x y) =
          groupExtension L x + groupExtension L y - x*y,
    True⟩

def groupCocycleNode : IdentifiedNode := by
  refine ⟨groupCocycleData,
    assemblePresentation groupCocycleData (fun x => SigmaBase.displacement x.val)
      ⟨trivial, ?_⟩ ?_⟩
  · apply propext
    constructor
    · intro _; trivial
    · intro _
      constructor
      · have hd : HasDerivAt SigmaBase.displacement 0 0 := by
          have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + x)) 1 0 := by
            convert (((hasDerivAt_id (0 : ℝ)).const_add 1).log (by norm_num)) using 1
            simp
          simpa [SigmaBase.displacement] using hlog.sub (hasDerivAt_id (0 : ℝ))
        apply hd.congr_of_eventuallyEq
        filter_upwards [isOpen_Ioi.mem_nhds (show (-1 : ℝ) < 0 by norm_num)]
          with x hx
        change -1 < x at hx
        simp [groupExtension, hx]
      · intro x hx y hy
        simp [groupExtension, hx, hy, SigmaBase.star_closed hx hy,
          SigmaBase.displacement_cocycle hx hy]
  · intro L _ he
    obtain ⟨h0, hh⟩ := (Iff.of_eq he).mpr True.intro
    funext x
    have h := normalized_cocycle_unique_at_identity (groupExtension L) h0 hh
      x.val x.property
    simpa [groupExtension, x.property, SigmaBase.displacement] using h

def symmetricBregmanData : PresentationData :=
  ⟨ScalarFunction,
    fun F => ∀ t > 0, DifferentiableAt ℝ (positiveExtension F) t,
    Prop,
    fun F => positiveExtension F 1 = 0 ∧
      deriv (positiveExtension F) 1 = 0 ∧
      ∀ t > 0,
        Bregman (positiveExtension F) t 1 +
          Bregman (positiveExtension F) 1 t = t + 1/t - 2,
    True⟩

def symmetricBregmanNode : IdentifiedNode := by
  refine ⟨symmetricBregmanData,
    assemblePresentation symmetricBregmanData (fun t => I t)
      ⟨?_, ?_⟩ ?_⟩
  · intro t ht
    have he : positiveExtension (fun t : PositiveCoordinate => I t) =ᶠ[nhds t] I := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
      change 0 < x at hx
      simp [positiveExtension, hx]
    exact ((SigmaBase.potential_hasDerivAt ht).congr_of_eventuallyEq he).differentiableAt
  · apply propext
    constructor
    · intro _; trivial
    · intro _
      have hd (t : ℝ) (ht : 0 < t) :
          deriv (positiveExtension (fun t : PositiveCoordinate => I t)) t = 1 - 1/t := by
        have he : positiveExtension (fun t : PositiveCoordinate => I t) =ᶠ[nhds t] I := by
          filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
          change 0 < x at hx
          simp [positiveExtension, hx]
        exact ((SigmaBase.potential_hasDerivAt ht).congr_of_eventuallyEq he).deriv
      refine ⟨?_, ?_, ?_⟩
      · simp [positiveExtension, I, SigmaBase.potential]
      · simpa using hd 1 (by norm_num)
      · intro t ht
        unfold Bregman
        rw [hd t ht, hd 1 (by norm_num)]
        simp only [positiveExtension, dif_pos ht, dif_pos (show (0 : ℝ) < 1 by norm_num)]
        field_simp [ne_of_gt ht]
        ring
  · intro F hF he
    obtain ⟨hv, hd1, hs⟩ := (Iff.of_eq he).mpr True.intro
    funext t
    have hu := anchored_symmetric_bregman_unique (positiveExtension F)
      hF hv hd1 hs t t.property
    simpa [positiveExtension, t.property] using hu

private theorem canonicalI_extension_deriv (t : ℝ) (ht : 0 < t) :
    deriv (positiveExtension (fun x : PositiveCoordinate => I x.val)) t = 1 - 1/t := by
  have he : positiveExtension (fun x : PositiveCoordinate => I x.val) =ᶠ[nhds t] I := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    change 0 < x at hx
    simp [positiveExtension, hx]
  exact ((SigmaBase.potential_hasDerivAt ht).congr_of_eventuallyEq he).deriv

def scaleBregmanData : PresentationData :=
  ⟨ScalarFunction,
    fun F => ∀ t > 0, DifferentiableAt ℝ (positiveExtension F) t,
    Prop,
    fun F => ScaleInvariantBregman (positiveExtension F) ∧
      positiveExtension F 1 = 0 ∧ deriv (positiveExtension F) 1 = 0 ∧
      deriv (positiveExtension F) 2 - deriv (positiveExtension F) 1 = 1/2,
    True⟩

def scaleBregmanNode : IdentifiedNode := by
  refine ⟨scaleBregmanData,
    assemblePresentation scaleBregmanData (fun t => I t)
      ⟨?_, ?_⟩ ?_⟩
  · intro t ht
    exact (SigmaBase.potential_hasDerivAt ht |>.congr_of_eventuallyEq (by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
      change 0 < x at hx
      simp [positiveExtension, hx])).differentiableAt
  · apply propext
    constructor
    · intro _; trivial
    · intro _
      have hI : ScaleInvariantBregman I := by
        have he : affinePotential 1 0 0 = I := by
          funext t
          simp [affinePotential]
        simpa [he] using affinePotential_scale 1 0 0
      have hs : ScaleInvariantBregman
          (positiveExtension (fun x : PositiveCoordinate => I x.val)) := by
        intro c hc t ht s hs
        have h := hI c hc t ht s hs
        unfold Bregman at h ⊢
        simp only [positiveExtension, dif_pos (mul_pos hc ht),
          dif_pos (mul_pos hc hs), dif_pos ht, dif_pos hs,
          canonicalI_extension_deriv _ (mul_pos hc hs),
          canonicalI_extension_deriv _ hs]
        rw [(SigmaBase.potential_hasDerivAt (mul_pos hc hs)).deriv,
          (SigmaBase.potential_hasDerivAt hs).deriv] at h
        exact h
      refine ⟨hs, ?_, ?_, ?_⟩
      · norm_num [positiveExtension, I, SigmaBase.potential]
      · simpa using canonicalI_extension_deriv 1 (by norm_num)
      · rw [canonicalI_extension_deriv 2 (by norm_num),
          canonicalI_extension_deriv 1 (by norm_num)]
        norm_num
  · intro F hd he
    obtain ⟨hs, hv, hd1, hd2⟩ := (Iff.of_eq he).mpr True.intro
    funext t
    have hu := calibrated_scale_bregman_unique (positiveExtension F)
      hd hs hv hd1 hd2 t.val t.property
    simpa [positiveExtension, t.property] using hu

def projectiveCrossRatioData : PresentationData :=
  ⟨ScalarFunction,
    fun f => InjOn (positiveExtension f) (Ioi 0), Prop,
    fun f => PreservesPositiveCrossRatios (positiveExtension f) ∧
      positiveExtension f 1 = 0 ∧
      positiveExtension f 2 = -1/2 ∧
      positiveExtension f 3 = -2/3,
    True⟩

def projectiveCrossRatioNode : IdentifiedNode := by
  refine ⟨projectiveCrossRatioData,
    assemblePresentation projectiveCrossRatioData (fun t => projectiveModel t)
      ⟨?_, ?_⟩ ?_⟩
  · intro x hx y hy he
    change 0 < x at hx
    change 0 < y at hy
    simp only [positiveExtension, dif_pos hx, dif_pos hy] at he
    exact projectiveModel_injective he
  · apply propext
    constructor
    · intro _; trivial
    · intro _
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x₁ h₁ x₂ h₂ x₃ h₃ x₄ h₄ h12 h13 h14 h23 h24 h34
        simpa [positiveExtension, h₁, h₂, h₃, h₄] using
          projectiveModel_preserves_cross_ratios x₁ h₁ x₂ h₂ x₃ h₃ x₄ h₄
            h12 h13 h14 h23 h24 h34
      · norm_num [positiveExtension, projectiveModel]
      · norm_num [positiveExtension, projectiveModel]
      · norm_num [positiveExtension, projectiveModel]
  · intro f hi he
    obtain ⟨hc, h1, h2, h3⟩ := (Iff.of_eq he).mpr True.intro
    funext t
    have hu := calibrated_cross_ratio_identifies (positiveExtension f)
      hi hc h1 h2 h3 t t.property
    simpa [positiveExtension, t.property, projectiveModel] using hu

private theorem projectiveExtension_eq (t : ℝ) (ht : 0 < t) :
    positiveExtension (fun x : PositiveCoordinate => projectiveModel x.val) t =
      projectiveModel t := by
  simp [positiveExtension, ht]

private theorem projectiveExtension_deriv (t : ℝ) (ht : 0 < t) :
    deriv (positiveExtension (fun x : PositiveCoordinate => projectiveModel x.val)) t =
      deriv projectiveModel t := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
  exact projectiveExtension_eq x hx

private theorem projectiveExtension_deriv2 (t : ℝ) (ht : 0 < t) :
    deriv (deriv (positiveExtension
      (fun x : PositiveCoordinate => projectiveModel x.val))) t =
      deriv (deriv projectiveModel) t := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
  exact projectiveExtension_deriv x hx

private theorem projectiveExtension_deriv3 (t : ℝ) (ht : 0 < t) :
    deriv (deriv (deriv (positiveExtension
      (fun x : PositiveCoordinate => projectiveModel x.val)))) t =
      deriv (deriv (deriv projectiveModel)) t := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
  exact projectiveExtension_deriv2 x hx

def projectiveSchwarzianData : PresentationData :=
  ⟨ScalarFunction,
    fun f => ContDiffOn ℝ 3 (positiveExtension f) (Ioi 0),
    Prop,
    fun f => (∀ t > 0, deriv (positiveExtension f) t ≠ 0) ∧
      (∀ t > 0, projectiveSchwarzian (positiveExtension f) t = 0) ∧
      positiveExtension f 1 = 0 ∧ deriv (positiveExtension f) 1 = -1 ∧
      deriv (deriv (positiveExtension f)) 1 = 2,
    True⟩

def projectiveSchwarzianNode : IdentifiedNode := by
  refine ⟨projectiveSchwarzianData,
    assemblePresentation projectiveSchwarzianData
      (fun t => projectiveModel t.val) ⟨?_, ?_⟩ ?_⟩
  · apply projectiveModel_C3.congr
    intro t ht
    exact projectiveExtension_eq t ht
  · apply propext
    constructor
    · intro _; trivial
    · intro _
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro t ht
        rw [projectiveExtension_deriv t ht]
        exact (projectiveModel_schwarzian_marks).2.2.2 t ht
      · intro t ht
        unfold projectiveSchwarzian
        rw [projectiveExtension_deriv t ht,
          projectiveExtension_deriv2 t ht,
          projectiveExtension_deriv3 t ht]
        exact projectiveModel_schwarzian_zero ht
      · simpa [projectiveExtension_eq 1 (by norm_num)] using
          (projectiveModel_schwarzian_marks).1
      · simpa [projectiveExtension_deriv 1 (by norm_num)] using
          (projectiveModel_schwarzian_marks).2.1
      · simpa [projectiveExtension_deriv2 1 (by norm_num)] using
          (projectiveModel_schwarzian_marks).2.2.1
  · intro f hC he
    obtain ⟨hn, hz, hv, h1, h2⟩ := (Iff.of_eq he).mpr True.intro
    funext t
    have hu := calibrated_schwarzian_identifies (positiveExtension f)
      hC hn hz hv h1 h2 t.val t.property
    simpa [positiveExtension, t.property, projectiveModel] using hu

/-- The exact Fenchel conjugate is observed on its full real dual coordinate.
The native lower-semicontinuous candidate class is retained. -/
def exactFenchelData : PresentationData :=
  ⟨ℝ → EReal, fun F => LowerSemicontinuousOn F (Ioi 0),
    ℝ → EReal, fullFenchelConjugate, intrinsicConjugateTarget⟩

def exactFenchelNode : IdentifiedNode :=
  ⟨exactFenchelData,
    assemblePresentation exactFenchelData extendedIntrinsic
      ⟨extended_intrinsic_lower_semicontinuousOn,
        extended_intrinsic_full_conjugate⟩
      (fun F hF he => fenchel_lower_semicontinuous_identifies F he hF)⟩

def poissonRecurrenceData : PresentationData :=
  ⟨PMF ℕ, fun _ => True, Prop,
    fun q => ∀ n, ((n + 1 : ℕ) : ℝ) * (q (n + 1)).toReal = (q n).toReal,
    True⟩

def poissonRecurrenceNode : IdentifiedNode := by
  refine ⟨poissonRecurrenceData,
    assemblePresentation poissonRecurrenceData (ProbabilityTheory.poissonPMF 1)
      ⟨trivial, ?_⟩ ?_⟩
  · apply propext
    exact ⟨fun _ => trivial, fun _ => poisson_one_recurrence⟩
  · intro q _ he
    exact poisson_probability_recurrence q ((Iff.of_eq he).mpr True.intro)

def poissonLocalCGFData : PresentationData :=
  ⟨Measure ℝ, IsProbabilityMeasure, Prop,
    fun μ => ∃ a : ℝ, 0 < a ∧
      (∀ s : ℝ, |s| < a → Integrable (fun t : ℝ => Real.exp (s*t)) μ) ∧
      (∀ s : ℝ, |s| < a →
        Real.log (∫ t : ℝ, Real.exp (s*t) ∂μ) = Real.exp s - 1),
    True⟩

def poissonLocalCGFNode : IdentifiedNode := by
  refine ⟨poissonLocalCGFData,
    assemblePresentation poissonLocalCGFData poissonRealProbability
      ⟨(show IsProbabilityMeasure poissonRealProbability from inferInstance), ?_⟩ ?_⟩
  · apply propext
    exact ⟨fun _ => trivial, fun _ =>
      ⟨1, by norm_num, fun s _ => poisson_real_exponential_integrable s,
        fun s _ => poisson_real_cgf s⟩⟩
  · intro μ hμ he
    letI : IsProbabilityMeasure μ := hμ
    obtain ⟨a, ha, hi, hc⟩ := (Iff.of_eq he).mpr True.intro
    exact poisson_local_cgf_identifies_real_line_law μ a ha hi hc

/-- The centered CGF identifies the law of the marked variable N-1. -/
def centeredPoissonLocalCGFData : PresentationData :=
  ⟨Measure ℝ, IsProbabilityMeasure, Prop,
    fun μ => ∃ a : ℝ, 0 < a ∧
      (∀ s : ℝ, |s| < a → Integrable (fun t : ℝ => Real.exp (s*t)) μ) ∧
      (∀ s : ℝ, |s| < a →
        Real.log (∫ t : ℝ, Real.exp (s*t) ∂μ) =
          SigmaPresentations.centeredCGF s),
    True⟩

def centeredPoissonLocalCGFNode : IdentifiedNode := by
  refine ⟨centeredPoissonLocalCGFData,
    assemblePresentation centeredPoissonLocalCGFData centeredPoissonRealProbability
      ⟨(show IsProbabilityMeasure centeredPoissonRealProbability from inferInstance), ?_⟩ ?_⟩
  · apply propext
    exact ⟨fun _ => trivial, fun _ =>
      ⟨1, by norm_num, fun s _ => centered_poisson_real_exponential_integrable s,
        fun s _ => centered_poisson_real_cgf s⟩⟩
  · intro μ hμ he
    letI : IsProbabilityMeasure μ := hμ
    obtain ⟨a, ha, hi, hc⟩ := (Iff.of_eq he).mpr True.intro
    exact marked_centered_poisson_local_cgf_identifies_law μ a ha hi hc

def gumbelMaxData : PresentationData :=
  ⟨ℝ → ℝ, Monotone, Prop,
    fun F => (∀ x, F (x + Real.log 2) ^ 2 = F x) ∧
      (∀ x, F (x + Real.log 3) ^ 3 = F x) ∧ F 0 = Real.exp (-1),
    True⟩

def gumbelMaxNode : IdentifiedNode := by
  refine ⟨gumbelMaxData,
    assemblePresentation gumbelMaxData gumbelCDF
      ⟨gumbel_cdf_monotone, ?_⟩ ?_⟩
  · apply propext
    exact ⟨fun _ => trivial,
      fun _ => ⟨gumbel_max_two, gumbel_max_three, gumbel_cdf_anchor⟩⟩
  · intro F hF he
    obtain ⟨h2, h3, h0⟩ := (Iff.of_eq he).mpr True.intro
    exact gumbel_two_max_laws_unique F hF h2 h3 h0

def markedHaarDensityData : PresentationData :=
  ⟨ScalarFunction,
    fun q => ContinuousOn (positiveExtension q) (Ioi 0) ∧
      ∀ t : ℝ, 0 < t → 0 ≤ positiveExtension q t,
    Measure ℝ,
    fun q => positiveHaar.withDensity
      (fun t => ENNReal.ofReal (positiveExtension q t)),
    unitExpProbability⟩

def markedHaarDensityNode : IdentifiedNode := by
  refine ⟨markedHaarDensityData,
    assemblePresentation markedHaarDensityData (fun t => p t)
      ⟨?_, ?_⟩ ?_⟩
  · constructor
    · have hp : Continuous p := by
        unfold p SigmaPresentations.density
        fun_prop
      exact hp.continuousOn.congr (fun t ht => by
        change 0 < t at ht
        simp [positiveExtension, ht])
    · intro t ht
      simpa [positiveExtension, ht] using SigmaPresentations.density_pos ht |>.le
  · calc
      positiveHaar.withDensity
          (fun t => ENNReal.ofReal (positiveExtension (fun t : PositiveCoordinate => p t) t)) =
        positiveHaar.withDensity (fun t => ENNReal.ofReal (p t)) := by
          apply withDensity_congr_ae
          filter_upwards [positive_haar_positive] with t ht
          simp [positiveExtension, ht]
      _ = unitExpProbability := positive_haar_weighted_probability
  · intro q hq he
    funext t
    have hu := (positive_haar_probability_identifies (positiveExtension q)
      hq.1 (fun x hx => hq.2 x hx) he) (x := t.val) t.property
    simpa [positiveExtension, t.property] using hu

def positiveSizeBiasData : PresentationData :=
  ⟨Measure ℝ,
    fun μ => IsProbabilityMeasure μ ∧
      (∀ᵐ t ∂μ, 0 < t) ∧
      (∫⁻ t, sizeBiasWeight t ∂μ) ≠ 0 ∧
      (∫⁻ t, sizeBiasWeight t ∂μ) ≠ ⊤,
    Measure ℝ,
    fun μ => normalizedWeight μ sizeBiasWeight,
    gammaProbability⟩

def positiveSizeBiasNode : IdentifiedNode := by
  refine ⟨positiveSizeBiasData,
    assemblePresentation positiveSizeBiasData unitExpProbability
      ⟨⟨inferInstance, unit_exp_positive, ?_, ?_⟩, unit_exp_size_bias_gamma⟩ ?_⟩
  · rw [unit_exp_coordinate_mean]
    norm_num
  · rw [unit_exp_coordinate_mean]
    norm_num
  · intro μ hμ he
    letI : IsProbabilityMeasure μ := hμ.1
    exact gamma_size_bias_identifies_positive_exponential μ
      hμ.2.1 hμ.2.2.1 hμ.2.2.2 he

def positiveEquilibriumData : PresentationData :=
  ⟨Measure ℝ × ℝ,
    fun x => IsProbabilityMeasure x.1 ∧ 0 < x.2 ∧
      x.1 (Ioi 0) = 1 ∧ (∫ t : ℝ, t ∂x.1) = x.2,
    Measure ℝ,
    fun x => equilibriumMeasure x.1 x.2,
    (volume.restrict (Ioi 0)).withDensity
      (fun t => ENNReal.ofReal ((1+t)*Real.exp (-t)/2))⟩

def positiveEquilibriumNode : IdentifiedNode := by
  refine ⟨positiveEquilibriumData,
    assemblePresentation positiveEquilibriumData (gammaProbability, 2)
      ⟨⟨inferInstance, by norm_num, ?_, ?_⟩, ?_⟩ ?_⟩
  · rw [← ENNReal.toReal_eq_one_iff]
    simpa [gammaProbability, gammaShapeSurvival, gammaSurvival] using
      gamma_shape_two_survival 1 0 (by norm_num) le_rfl
  · exact gamma_probability_mean
  · exact gamma_equilibrium_density
  · intro x hx he
    letI : IsProbabilityMeasure x.1 := hx.1
    obtain ⟨hm, hμ⟩ := gamma_equilibrium_identifies x.1 x.2 hx.2.1 hx.2.2.1 he
    exact Prod.ext hμ hm

def logisticHazardData : PresentationData :=
  ⟨ℝ → ℝ, fun _ => True, Prop,
    fun v => (∀ u, HasDerivAt v (v u * (1 - v u)) u) ∧ v 0 = 1/2,
    True⟩

def logisticHazardNode : IdentifiedNode := by
  refine ⟨logisticHazardData,
    assemblePresentation logisticHazardData logisticHazard
      ⟨trivial, ?_⟩ ?_⟩
  · apply propext
    exact ⟨fun _ => trivial, fun _ =>
      ⟨logistic_hazard_derivative, logistic_hazard_anchor⟩⟩
  · intro v _ he
    obtain ⟨hv, h0⟩ := (Iff.of_eq he).mpr True.intro
    exact logistic_hazard_unique v hv h0

/-- The native coordinate probability is linked to the complex mixing measure
used by the fixed marked Laguerre operator. -/
abbrev MixingProbability := {ν : Measure OpNonnegativeRay // IsProbabilityMeasure ν}

def linkedOperatorMixingObservation (P : MixingProbability) : Prop :=
  letI : IsProbabilityMeasure P.val := P.property
  ∀ x : LaguerreWeightedHilbert,
      complexStrongIntegral (P.val.toSignedMeasure.toComplexMeasure 0)
        (fun s => opNonnegativeHeat laguerreCanonicalOperator
          laguerre_canonical_selfAdjoint laguerre_canonical_nonnegative s.val x) =
        opNonnegativeResolvent laguerreCanonicalOperator
          laguerre_canonical_selfAdjoint laguerre_canonical_nonnegative
          (opNonnegativeResolvent laguerreCanonicalOperator
            laguerre_canonical_selfAdjoint laguerre_canonical_nonnegative x)

def linkedOperatorMixingData : PresentationData :=
  ⟨MixingProbability, fun _ => True, Prop, linkedOperatorMixingObservation, True⟩

set_option maxHeartbeats 1000000 in
def linkedOperatorMixingNode : IdentifiedNode := by
  refine ⟨linkedOperatorMixingData,
    assemblePresentation linkedOperatorMixingData
      ⟨nonnegativeGammaMixingMeasure, inferInstance⟩ ⟨trivial, ?_⟩ ?_⟩
  · apply propext
    exact ⟨fun _ => trivial, fun _ x =>
      op_nonnegative_gamma_complex_mixing laguerreCanonicalOperator
        laguerre_canonical_selfAdjoint laguerre_canonical_nonnegative x⟩
  · intro P _ he
    letI : IsProbabilityMeasure P.val := P.property
    have hmix := (Iff.of_eq he).mpr True.intro
    have hu := op_linked_coordinate_probability_unique
      laguerreCanonicalOperator laguerre_canonical_selfAdjoint
      laguerre_canonical_nonnegative ?_ (P.val.toSignedMeasure.toComplexMeasure 0)
      P.val rfl hmix
    · exact Subtype.ext hu.1
    · intro n
      exact ⟨⟨laguerreHilbertBasis n, laguerre_basis_mem_canonical_domain n⟩,
        laguerreHilbertBasis.orthonormal.ne_zero n,
        laguerre_canonical_basis_action n⟩

def borelPGFData : PresentationData :=
  ⟨PMF ℕ, fun _ => True, Prop,
    fun q => ∀ s : ℝ, 0 < s → s < 1 →
      natProbabilityGenerating q s =
        s * Real.exp (natProbabilityGenerating q s - 1), True⟩

def borelPGFNode : IdentifiedNode := by
  refine ⟨borelPGFData,
    assemblePresentation borelPGFData borelPMF ⟨trivial, ?_⟩ ?_⟩
  · apply propext
    exact ⟨fun _ => trivial, fun _ =>
      (nat_pgf_poisson_branching_iff borelPMF).mp rfl⟩
  · intro q _ he
    exact nat_pgf_poisson_branching_identifies_borel q ((Iff.of_eq he).mpr True.intro)

def borelSeriesData : PresentationData :=
  ⟨PowerSeries ℝ, fun _ => True, Prop,
    fun F => F = PowerSeries.C ℝ (Real.exp (-1)) * PowerSeries.X * treeExp ℝ F ∧
      PowerSeries.C ℝ (Real.exp 1) * F * treeExp ℝ (-F) = PowerSeries.X,
    True⟩

def borelSeriesNode : IdentifiedNode := by
  refine ⟨borelSeriesData,
    assemblePresentation borelSeriesData borelSeries ⟨trivial, ?_⟩ ?_⟩
  · apply propext
    exact ⟨fun _ => trivial, fun _ =>
      ⟨borel_series_fixed_point, borel_series_inverse_identity⟩⟩
  · intro F _ he
    exact borel_series_unique F ((Iff.of_eq he).mpr True.intro).1

def rootedSeriesData : PresentationData :=
  ⟨PowerSeries ℝ, fun _ => True, Prop,
    fun F => F = PowerSeries.X * treeExp ℝ F ∧
      F * treeExp ℝ (-F) = PowerSeries.X,
    True⟩

def rootedSeriesNode : IdentifiedNode := by
  refine ⟨rootedSeriesData,
    assemblePresentation rootedSeriesData (rootedSeries ℝ)
      ⟨trivial, ?_⟩ ?_⟩
  · apply propext
    exact ⟨fun _ => trivial, fun _ =>
      ⟨rooted_series_fixed_point ℝ, rooted_series_inverse_identity ℝ⟩⟩
  · intro F _ he
    exact rooted_series_unique ℝ F ((Iff.of_eq he).mpr True.intro).1

/-- The linked deficit observation keeps both the prescribed involution and
the actual weighted pushforward law on the marked positive coordinate. -/
def linkedDeficitData : PresentationData :=
  ⟨ScalarFunction,
    fun F => RayPotential (positiveExtension F),
    Prop × Measure ℝ,
    fun F =>
      ((∀ b ≥ 1, 0 < canonicalDeficitInvolution b ∧
          canonicalDeficitInvolution b ≤ 1 ∧
          positiveExtension F (canonicalDeficitInvolution b) = positiveExtension F b),
        Measure.map (positiveRayExtension (positiveExtension F))
          ((volume.restrict (Ioi 0)).withDensity
            (deficitWeight ∘ positiveRayExtension (positiveExtension F)))),
    (True, gammaDeficitProbability)⟩

private theorem linked_deficit_canonical_extension (t : ℝ) (ht : 0 < t) :
    positiveExtension (fun x : PositiveCoordinate => SigmaBase.potential x.val) t =
      SigmaBase.potential t := by
  simp [positiveExtension, ht]

private theorem linked_deficit_canonical_ray_potential :
    RayPotential (positiveExtension
      (fun x : PositiveCoordinate => SigmaBase.potential x.val)) := by
  let J := positiveExtension (fun x : PositiveCoordinate => SigmaBase.potential x.val)
  have h := intrinsic_potential_two_branch
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.continuous.congr (fun t ht =>
      linked_deficit_canonical_extension t ht)
  · simpa [J, linked_deficit_canonical_extension] using h.anchor
  · intro a ha b hb hab
    simpa only [J, linked_deficit_canonical_extension a ha.1,
      linked_deficit_canonical_extension b hb.1] using h.left_strict ha hb hab
  · intro a ha b hb hab
    have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
    have hb0 : 0 < b := lt_of_lt_of_le (by norm_num) hb
    simpa only [J, linked_deficit_canonical_extension a ha0,
      linked_deficit_canonical_extension b hb0] using h.right_strict ha hb hab
  · apply h.left_limit.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (linked_deficit_canonical_extension t ht).symm
  · apply h.right_limit.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (linked_deficit_canonical_extension t ht).symm

private theorem linked_deficit_canonical_observation :
    (linkedDeficitData.observe
      (fun x : PositiveCoordinate => SigmaBase.potential x.val)) =
      linkedDeficitData.value := by
  apply Prod.ext
  · apply propext
    exact ⟨fun _ => True.intro, fun _ b hb => by
      rcases canonical_deficit_involution_pair b hb with ⟨h0, h1, he⟩
      exact ⟨h0, h1, by
        rw [linked_deficit_canonical_extension _ h0,
          linked_deficit_canonical_extension _ (by linarith : 0 < b)]
        exact he⟩⟩
  · have he : positiveRayExtension
        (positiveExtension (fun x : PositiveCoordinate => SigmaBase.potential x.val)) =
        positiveRayExtension SigmaBase.potential := by
      funext t
      by_cases ht : 0 < t
      · simp [positive_ray_extension_eq _ ht, linked_deficit_canonical_extension t ht]
      · simp [positiveRayExtension, ht]
    change Measure.map _ _ = gammaDeficitProbability
    rw [he]
    have hw : (volume.restrict (Ioi (0 : ℝ))).withDensity
        (deficitWeight ∘ positiveRayExtension SigmaBase.potential) = gammaProbability := by
      calc
        _ = (volume.restrict (Ioi 0)).withDensity
            (deficitWeight ∘ SigmaBase.potential) := by
              apply withDensity_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              simp [Function.comp_def, positive_ray_extension_eq _ ht]
        _ = gammaProbability := canonical_linked_density_measure
    rw [hw, gammaDeficitProbability]
    apply Measure.map_congr
    filter_upwards [operator_integer_samples_ae_pos gammaProbability
      operator_gamma_probability_integer_samples] with t ht
    exact positive_ray_extension_eq _ ht

def linkedDeficitNode : IdentifiedNode := by
  refine ⟨linkedDeficitData,
    assemblePresentation linkedDeficitData
      (fun x : PositiveCoordinate => SigmaBase.potential x.val)
      ⟨linked_deficit_canonical_ray_potential,
        linked_deficit_canonical_observation⟩ ?_⟩
  intro F hF he
  funext t
  have hp : ∀ b ≥ 1, 0 < canonicalDeficitInvolution b ∧
      canonicalDeficitInvolution b ≤ 1 ∧
      positiveExtension F (canonicalDeficitInvolution b) = positiveExtension F b := by
    exact (Iff.of_eq (congrArg Prod.fst he)).mpr True.intro
  have hlaw := congrArg Prod.snd he
  have hu := canonical_deficit_pair_identifies_on_positive_ray
    (positiveExtension F) hF hp hlaw t.val t.property
  simpa [positiveExtension, t.property] using hu.1

abbrev NonnegativeCoordinate := {t : ℝ // 0 ≤ t}
abbrev NonnegativeFunction := NonnegativeCoordinate → ℝ

def nonnegativeExtension (F : NonnegativeFunction) (t : ℝ) : ℝ :=
  if h : 0 ≤ t then F ⟨t, h⟩ else 0

/-- The candidate is a function on the stated nonnegative ray, with the
Bernstein representation condition retained. Every integer tail is observed. -/
def bernsteinTailData : PresentationData :=
  ⟨NonnegativeFunction,
    fun F => HasBernsteinRepresentation (nonnegativeExtension F),
    ℕ → ℝ, fun F n => F ⟨n, Nat.cast_nonneg n⟩,
    fun n => 2 * Real.log (1 + (n : ℝ))⟩

def bernsteinTailNode : IdentifiedNode := by
  refine ⟨bernsteinTailData,
    assemblePresentation bernsteinTailData
      (fun t => gammaLaplaceExponent t) ⟨?_, ?_⟩ ?_⟩
  · refine ⟨gammaBernsteinRepresentation, ?_⟩
    intro l hl
    simp only [nonnegativeExtension, dif_pos hl]
    exact (gamma_bernstein_representation_exponent l hl).symm
  · funext n
    rfl
  · intro F hF he
    funext t
    have hu := gamma_bernstein_function_integer_tail_unique
      (nonnegativeExtension F) hF 0
      (fun n _ => by simpa [nonnegativeExtension, Nat.cast_nonneg] using congrFun he n)
      t t.property
    simpa [nonnegativeExtension, t.property] using hu

/-- Distinct observations remain distinct typed nodes, even when they identify
the same native probability measure. This initial collection is extensible. -/
inductive AvailablePresentation
  | intrinsicH | intrinsicI | intrinsicDensity
  | gammaCharacteristic | gammaMoments | gammaIntegerLaplace | gammaStein | gammaLaguerre
  | gammaLaw | gammaMellin | gammaStieltjes | gammaMarkedCoordinate
  | toddTower
  | ahatSeries | lSeries | markedChi (y : ℚ) (hy : y ≠ -1)
  | analyticTodd | analyticAhat | analyticL | analyticChi (y : ℚ) (hy : y ≠ -1)
  | differentialCore | calibratedCurvature | calibratedRiccati | recentering
  | exactFlow | groupLog | groupCocycle | symmetricBregman | scaleBregman
  | projectiveCrossRatio | projectiveSchwarzian | exactFenchel
  | poissonRecurrence | poissonLocalCGF | centeredPoissonLocalCGF
  | gumbelMax | markedHaarDensity | positiveSizeBias
  | positiveEquilibrium | logisticHazard | linkedOperatorMixing
  | borelPGF | borelSeries | rootedSeries
  | linkedDeficit
  | bernsteinTail

def availablePresentation : AvailablePresentation → IdentifiedNode
  | .intrinsicH => intrinsicHNode
  | .intrinsicI => intrinsicINode
  | .intrinsicDensity => intrinsicDensityNode
  | .gammaCharacteristic => gammaCharacteristicNode
  | .gammaMoments => gammaMomentsNode
  | .gammaIntegerLaplace => gammaIntegerLaplaceNode
  | .gammaStein => gammaSteinNode
  | .gammaLaguerre => gammaLaguerreNode
  | .gammaLaw => gammaLawNode
  | .gammaMellin => gammaMellinNode
  | .gammaStieltjes => gammaStieltjesNode
  | .gammaMarkedCoordinate => gammaMarkedCoordinateNode
  | .toddTower => toddTowerNode
  | .ahatSeries => ahatSeriesNode
  | .lSeries => lSeriesNode
  | .markedChi y hy => markedChiNode y hy
  | .analyticTodd => analyticToddNode
  | .analyticAhat => analyticAhatNode
  | .analyticL => analyticLNode
  | .analyticChi y hy => analyticChiNode y hy
  | .differentialCore => differentialCoreNode
  | .calibratedCurvature => calibratedCurvatureNode
  | .calibratedRiccati => calibratedRiccatiNode
  | .recentering => recenteringNode
  | .exactFlow => exactFlowNode
  | .groupLog => groupLogNode
  | .groupCocycle => groupCocycleNode
  | .symmetricBregman => symmetricBregmanNode
  | .scaleBregman => scaleBregmanNode
  | .projectiveCrossRatio => projectiveCrossRatioNode
  | .projectiveSchwarzian => projectiveSchwarzianNode
  | .exactFenchel => exactFenchelNode
  | .poissonRecurrence => poissonRecurrenceNode
  | .poissonLocalCGF => poissonLocalCGFNode
  | .centeredPoissonLocalCGF => centeredPoissonLocalCGFNode
  | .gumbelMax => gumbelMaxNode
  | .markedHaarDensity => markedHaarDensityNode
  | .positiveSizeBias => positiveSizeBiasNode
  | .positiveEquilibrium => positiveEquilibriumNode
  | .logisticHazard => logisticHazardNode
  | .linkedOperatorMixing => linkedOperatorMixingNode
  | .borelPGF => borelPGFNode
  | .borelSeries => borelSeriesNode
  | .rootedSeries => rootedSeriesNode
  | .linkedDeficit => linkedDeficitNode
  | .bernsteinTail => bernsteinTailNode

def availableReconstruction (A B : AvailablePresentation) :
    (availablePresentation A).data.Solution ≃ (availablePresentation B).data.Solution :=
  (availablePresentation A).reconstruction.symm.trans (availablePresentation B).reconstruction

theorem available_reconstruction_roundtrip (A B : AvailablePresentation)
    (x : (availablePresentation A).data.Solution) :
    availableReconstruction B A (availableReconstruction A B x) = x := by
  simp [availableReconstruction]

theorem available_intrinsic_roundtrips (A : AvailablePresentation) :
    (∀ s, (availablePresentation A).reconstruction.symm
      ((availablePresentation A).reconstruction s) = s) ∧
    (∀ x, (availablePresentation A).reconstruction
      ((availablePresentation A).reconstruction.symm x) = x) :=
  ⟨(availablePresentation A).reconstruction.symm_apply_apply,
    (availablePresentation A).reconstruction.apply_symm_apply⟩

end
end Sigma.Closure
