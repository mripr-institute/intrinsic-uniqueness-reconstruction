import SigmaClosureContexts
import SigmaThomNativeSplitting
import SigmaThomNativeObservation

namespace Sigma.Closure
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

/-- A correction candidate must satisfy the supplied actual Thom comparison
for every admissible bundle. Equality to the canonical recipe is not assumed. -/
def UniversalThomCorrectionContext (T : SuppliedComplexThomTheory)
    (C : (V : NativeComplexBundle) → T.admissible V → T.HBase V.base) : Prop :=
  ∀ V hV, T.ch V.thomPair ((T.kThom V hV) 1) = C V hV • ((T.hThom V hV) 1)

theorem universal_thom_context_iff (T : SuppliedComplexThomTheory)
    (S : NativeThomSplittingContext T)
    (C : (V : NativeComplexBundle) → T.admissible V → T.HBase V.base) :
    UniversalThomCorrectionContext T C ↔ C = S.inverseTodd := by
  constructor
  · intro hC
    funext V hV
    exact ((T.context V hV).correction_unique (C V hV) (hC V hV)).trans
      (S.split V hV).correction_eq_inverseTodd
  · rintro rfl
    exact S.thom_comparison

theorem universal_thom_context_exists_unique (T : SuppliedComplexThomTheory)
    (S : NativeThomSplittingContext T) :
    ∃! C : (V : NativeComplexBundle) → T.admissible V → T.HBase V.base,
      UniversalThomCorrectionContext T C :=
  ⟨S.inverseTodd, S.thom_comparison,
    fun C hC => (universal_thom_context_iff T S C).mp hC⟩

/-- Complete actual finite universal-line observations, with all projective
stages retained, rather than a single finite-base evaluation. -/
def UniversalThomLineObservation {T : SuppliedComplexThomTheory}
    (S : NativeThomSplittingContext T) (Q : (PowerSeries ℚ)ˣ) : Prop :=
  ∀ n, thomStageMap n (↑Q⁻¹ : PowerSeries ℚ) = S.universal.coordinate n
    (T.correction (S.universal.stage n) (S.universal.admissible n))

theorem universal_thom_line_observation_iff (T : SuppliedComplexThomTheory)
    (S : NativeThomSplittingContext T) (Q : (PowerSeries ℚ)ˣ) :
    UniversalThomLineObservation S Q ↔ Q = formalToddUnitOver ℚ := by
  constructor
  · exact S.full_universal_line_inverse Q
  · rintro rfl n
    rw [← S.universal.correctionSeries_stage, S.universal.correctionSeries_eq_inverseTodd]

theorem universal_thom_line_exists_unique (T : SuppliedComplexThomTheory)
    (S : NativeThomSplittingContext T) :
    ∃! Q : (PowerSeries ℚ)ˣ, UniversalThomLineObservation S Q :=
  ⟨formalToddUnitOver ℚ, (universal_thom_line_observation_iff T S _).mpr rfl,
    fun Q hQ => (universal_thom_line_observation_iff T S Q).mp hQ⟩

/-- The full native universal-line observation also recovers the intrinsic
formal exponential, supplying the reverse scalar link in global E. -/
theorem universal_thom_intrinsic_reverse (T : SuppliedComplexThomTheory)
    (S : NativeThomSplittingContext T) :
    1-PowerSeries.X*S.universal.correctionSeries = formalExponentialOver ℚ (-1) := by
  rw [S.universal.correctionSeries_euler]
  ring

/-- All six actual fixed-context unique-existence clauses of global E.
The observation equivalences and intrinsic reverse maps are the accompanying
context theorems, including the complete universal-line equivalence above. -/
theorem fixed_context_native_closure (T : SuppliedComplexThomTheory)
    (S : NativeThomSplittingContext T) :
    (∃! μ : ℝ≥0 → Measure ℝ,
      ProbabilityConvolutionContext μ ∧ μ 1 = gammaProbability) ∧
    (∃! A : LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert,
      LaguerreClosureContext A) ∧
    (∃! F : PositiveMatrixFamily, PositiveMatrixContext F) ∧
    (∃! μ : Measure (EuclideanSpace ℝ (Fin 4)),
      IsotropicFourContext μ ∧ μ.map radialFourEnergy = gammaProbability) ∧
    (∃! q : PMF ℕ, gwTotalSizeLaw q = borelExtendedProbability) ∧
    (∃! C : (V : NativeComplexBundle) → T.admissible V → T.HBase V.base,
      UniversalThomCorrectionContext T C) :=
  ⟨convolution_context_exists_unique, laguerre_context_exists_unique,
    matrix_context_exists_unique, gaussian_radial_context_exists_unique,
    gw_context_exists_unique_offspring, universal_thom_context_exists_unique T S⟩

end
end Sigma.Closure
