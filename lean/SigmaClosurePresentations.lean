import SigmaClosure
import SigmaProbInverse
import SigmaOpMomentInverse
import SigmaOpLaguerreL2
import SigmaSteinMomentLimits
import SigmaRealToddTower
import SigmaProbStieltjes
import SigmaOpCoordinateProjections

namespace Sigma.Closure
noncomputable section
open MeasureTheory Set
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

/-- Distinct observations remain distinct typed nodes, even when they identify
the same native probability measure. This initial collection is extensible. -/
inductive AvailablePresentation
  | intrinsicH | intrinsicI | intrinsicDensity
  | gammaCharacteristic | gammaMoments | gammaIntegerLaplace | gammaStein | gammaLaguerre
  | gammaLaw | gammaMellin | gammaStieltjes | gammaMarkedCoordinate
  | toddTower

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
