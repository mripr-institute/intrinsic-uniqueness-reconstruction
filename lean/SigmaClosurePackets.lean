import SigmaClosurePresentations
import SigmaOpCanonicalSelectionBoundary
import SigmaRealRadialBoundary
import SigmaRealTreesCountermodel
import SigmaProbCompletionBoundary
import SigmaProbGammaProcessExistence
import SigmaArithmeticInventory
import SigmaMatrixGeometry

namespace Sigma.Closure
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- A selected vector law retains its actual Euclidean carrier and probability
condition. The observation forgets only the angle. -/
abbrev VectorLawPacket :=
  {μ : Measure (EuclideanSpace ℝ (Fin 4)) // IsProbabilityMeasure μ}

def vectorRadius (P : VectorLawPacket) : Measure ℝ := P.val.map radialFourEnergy

theorem vector_packet_deletion :
    ∃ P Q : VectorLawPacket, vectorRadius P = gammaProbability ∧
      vectorRadius Q = gammaProbability ∧ P.val ≠ Q.val := by
  obtain ⟨μ, ν, hμ, hν, hn, hm, hv⟩ := gamma_radial_energy_does_not_identify_vector_law
  exact ⟨⟨μ, hμ⟩, ⟨ν, hν⟩, hm, hv, hn⟩

theorem vector_packet_no_decoder {R : Type*} (s : IntrinsicObject) (r : R) :
    ¬ ∃ decode : (IntrinsicObject × R) × Measure ℝ →
        Measure (EuclideanSpace ℝ (Fin 4)),
      ∀ P : VectorLawPacket, decode ((s, r), vectorRadius P) = P.val := by
  apply retained_context_deletion vectorRadius Subtype.val (s, r)
  obtain ⟨P, Q, hP, hQ, hn⟩ := vector_packet_deletion
  exact ⟨P, Q, hP.trans hQ.symm, hn⟩

theorem tree_packet_no_decoder {R : Type*} (s : IntrinsicObject) (r : R) :
    ¬ ∃ decode : (IntrinsicObject × R) × PMF ℕ → PMF IncreasingRootedTree,
      ∀ P : PMF IncreasingRootedTree,
        decode ((s, r), P.map IncreasingRootedTree.order) = P := by
  apply retained_context_deletion
    (fun P : PMF IncreasingRootedTree => P.map IncreasingRootedTree.order) id (s, r)
  obtain ⟨P, Q, hP, hQ, hn⟩ := borel_size_does_not_identify_random_tree
  exact ⟨P, Q, hP.trans hQ.symm, hn⟩

theorem stationary_packet_no_decoder {R : Type*} (s : IntrinsicObject) (r : R) :
    ¬ ∃ decode : (IntrinsicObject × R) × Set ℂ → Measure ℝ,
      ∀ P : NativeGammaStationaryRealization,
        decode ((s, r), stationaryRealizationSpectrum P) = stationaryCoordinateLaw P := by
  apply retained_context_deletion stationaryRealizationSpectrum stationaryCoordinateLaw (s, r)
  refine ⟨gammaTwoStationaryRealization, gammaThreeStationaryRealization, ?_, ?_⟩
  · rw [gamma_two_stationary_spectrum, gamma_three_stationary_spectrum]
  · exact Ne.symm gamma_shape_three_coordinate_law_ne_shape_two

/-- The probability space is part of the deleted process packet. It is never
left behind as an untyped carrier when comparing the two constructions. -/
structure ProcessPacket where
  Sample : Type
  measurableSpace : MeasurableSpace Sample
  law : @Measure Sample measurableSpace
  probability : @IsProbabilityMeasure Sample measurableSpace law
  process : ℝ≥0 → Sample → ℝ
  measurable : ∀ t, @Measurable Sample ℝ measurableSpace _ (process t)

def ProcessPacket.timeOne (P : ProcessPacket) : Measure ℝ :=
  @Measure.map P.Sample ℝ P.measurableSpace _ (P.process 1) P.law

def ProcessPacket.independent (P : ProcessPacket) : Prop :=
  @HasIndependentNonnegativeTimeIncrements P.Sample P.measurableSpace P.law P.process

def subordinatorPacket : ProcessPacket :=
  ⟨PoissonClockSpace, inferInstance, poissonClockProbability, inferInstance,
    nativeGammaProcess, native_gamma_process_measurable⟩

def dependentProcessPacket : ProcessPacket :=
  ⟨ℝ, inferInstance, gammaProbability, inferInstance,
    gammaSingleVariableProcess, gamma_single_variable_measurable⟩

theorem process_packet_deletion :
    subordinatorPacket.timeOne = dependentProcessPacket.timeOne ∧
      subordinatorPacket.independent ∧ ¬ dependentProcessPacket.independent := by
  refine ⟨?_, native_gamma_process_category.2.2.2.1,
    gamma_single_variable_not_independent_increments⟩
  exact native_gamma_process_category.2.2.2.2.2.trans gamma_single_variable_time_one.symm

theorem process_packet_no_decoder {R : Type*} (s : IntrinsicObject) (r : R) :
    ¬ ∃ decode : (IntrinsicObject × R) × Measure ℝ → Prop,
      ∀ P : ProcessPacket, decode ((s, r), P.timeOne) = P.independent := by
  apply retained_context_deletion ProcessPacket.timeOne ProcessPacket.independent (s, r)
  refine ⟨subordinatorPacket, dependentProcessPacket, process_packet_deletion.1, ?_⟩
  intro he
  exact process_packet_deletion.2.2 (he ▸ process_packet_deletion.2.1)

/-- Both labels are actual multiplicative equivalences on the same bare
carrier; all its multiplication and divisibility remain unchanged. -/
theorem arithmetic_packet_no_decoder {R : Type*} (s : IntrinsicObject) (r : R) :
    ¬ ∃ decode : IntrinsicObject × R → (ℕ+ → ℕ+),
      ∀ E : ℕ+ ≃* ℕ+, decode (s, r) = E := by
  rintro ⟨decode, hd⟩
  have he := (hd (MulEquiv.refl ℕ+)).symm.trans (hd swapTwoThree)
  have h := congrFun he 2
  change (2 : ℕ+) = swapTwoThree 2 at h
  rw [swap_two_three_two] at h
  norm_num at h

abbrev MatrixFamily := (n : ℕ) → Matrix (Fin (n+1)) (Fin (n+1)) ℝ → ℝ

def matrixSeed (F : MatrixFamily) : ℝ → ℝ :=
  fun t => F 0 (Matrix.diagonal (fun _ => t))

theorem matrix_packet_deletion :
    ∃ F G : MatrixFamily, matrixSeed F = SigmaBase.potential ∧
      matrixSeed G = SigmaBase.potential ∧ F ≠ G := by
  refine ⟨fun _ X => matrixPotential X, fun _ X => matrixRankShiftLift X, ?_, ?_, ?_⟩
  · funext t
    simp [matrixSeed, matrixPotential, Matrix.trace, Matrix.diag,
      Matrix.det_diagonal, SigmaBase.potential]
    ring
  · funext t
    exact matrix_rank_shift_seed t
  · intro he
    have h := congrFun (congrFun he 1) (1 : Matrix (Fin 2) (Fin 2) ℝ)
    simp [matrixRankShiftLift] at h

theorem matrix_packet_no_decoder {R : Type*} (s : IntrinsicObject) (r : R) :
    ¬ ∃ decode : (IntrinsicObject × R) × (ℝ → ℝ) → MatrixFamily,
      ∀ F, decode ((s, r), matrixSeed F) = F := by
  apply retained_context_deletion matrixSeed id (s, r)
  obtain ⟨F, G, hF, hG, hn⟩ := matrix_packet_deletion
  exact ⟨F, G, hF.trans hG.symm, hn⟩

end
end Sigma.Closure
