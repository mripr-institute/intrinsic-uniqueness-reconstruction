import SigmaClosurePackets
import SigmaOpGammaShapeThreeBoundary
import SigmaRealProjectiveF5Characteristic

namespace Sigma.Closure
noncomputable section
open MeasureTheory

/-- A coordinate marking is a homeomorphic choice of labels on the positive ray. -/
abbrev CoordinateMarking := PositiveCoordinate ≃ₜ PositiveCoordinate

private def markedOne : PositiveCoordinate := ⟨1, by norm_num⟩
private def markedTwo : PositiveCoordinate := ⟨2, by norm_num⟩

def identityCoordinateMarking : CoordinateMarking := Homeomorph.refl _
def scaledCoordinateMarking : CoordinateMarking where
  toFun t := ⟨2 * t.val, mul_pos (by norm_num) t.property⟩
  invFun t := ⟨t.val / 2, div_pos t.property (by norm_num)⟩
  left_inv t := by apply Subtype.ext; dsimp; ring
  right_inv t := by apply Subtype.ext; dsimp; ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.mul continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.div_const 2

/-- The underlying intrinsic object can be retained while its external
coordinate marking is changed. -/
theorem coordinate_marking_deletion :
    identityCoordinateMarking ≠ scaledCoordinateMarking := by
  intro he
  have h := congrArg (fun e : CoordinateMarking => e markedOne) he
  have hv := congrArg Subtype.val h
  norm_num [identityCoordinateMarking, scaledCoordinateMarking, markedOne] at hv

theorem coordinate_marking_no_decoder {R : Type*}
    (s : IntrinsicObject) (r : R) :
    ¬ ∃ decode : IntrinsicObject × R → CoordinateMarking,
      ∀ e : CoordinateMarking, decode (s, r) = e := by
  rintro ⟨decode, hd⟩
  exact coordinate_marking_deletion
    ((hd identityCoordinateMarking).symm.trans (hd scaledCoordinateMarking))

/-- The common squared-resolvent mixing measure is retained alongside the
actual spectrum; the equations for both native stationary laws are proved
below from their respective operator theorems. -/
def stationarySpectrumMixingData
    (P : NativeGammaStationaryRealization) :
    Set ℂ × ComplexMeasure OpNonnegativeRay :=
  (stationaryRealizationSpectrum P, nonnegativeGammaComplexMeasure)

theorem stationary_spectrum_mixing_deletion :
    stationarySpectrumMixingData gammaTwoStationaryRealization =
      stationarySpectrumMixingData gammaThreeStationaryRealization ∧
    (∀ x : LaguerreWeightedHilbert,
      complexStrongIntegral nonnegativeGammaComplexMeasure
        (fun s => laguerreHeatOperator s.val s.property x) =
          laguerreSquaredResolvent 1 (by norm_num) x) ∧
    (∀ x : GammaShapeThreeWeightedHilbert,
      complexStrongIntegral nonnegativeGammaComplexMeasure
        (fun s => gammaShapeThreeHeat s.val x) =
          gammaShapeThreeSquaredResolvent 1 (by norm_num) x) ∧
    stationaryCoordinateLaw gammaTwoStationaryRealization ≠
      stationaryCoordinateLaw gammaThreeStationaryRealization := by
  have hmix :=
    (gamma_shapes_two_three_common_mixing nonnegativeGammaComplexMeasure).mpr rfl
  refine ⟨?_, hmix.1, hmix.2, ?_⟩
  · simp only [stationarySpectrumMixingData]
    rw [gamma_two_stationary_spectrum, gamma_three_stationary_spectrum]
  · exact Ne.symm gamma_shape_three_coordinate_law_ne_shape_two

theorem stationary_spectrum_mixing_no_decoder {R : Type*}
    (s : IntrinsicObject) (r : R) :
    ¬ ∃ decode : (IntrinsicObject × R) ×
        (Set ℂ × ComplexMeasure OpNonnegativeRay) → Measure ℝ,
      ∀ P : NativeGammaStationaryRealization,
        decode ((s, r), stationarySpectrumMixingData P) =
          stationaryCoordinateLaw P := by
  apply retained_context_deletion stationarySpectrumMixingData
    stationaryCoordinateLaw (s, r)
  exact ⟨gammaTwoStationaryRealization, gammaThreeStationaryRealization,
    stationary_spectrum_mixing_deletion.1,
    stationary_spectrum_mixing_deletion.2.2.2⟩

/-- The original native-bundle boundary assembly. The extension
CompleteScalarBoundary in SigmaClosureCompleteBoundary adds the normalized
intrinsic deletion and the native integral-versus-rational K⁰ witness. -/
structure ScalarBoundaryWithNativeBundle (s : IntrinsicObject) (R : Type*) (r : R) : Prop where
  placementScale :
    ¬ ∃ decode : (IntrinsicObject × R) × ℝ → ScalarFunction,
      ∀ P : Placement, decode ((s, r), P.a) = P.presentation
  placementOffset :
    ¬ ∃ decode : (IntrinsicObject × R) × ℝ → ScalarFunction,
      ∀ P : Placement, decode ((s, r), P.μ) = P.presentation
  coordinateMarking :
    ¬ ∃ decode : IntrinsicObject × R → CoordinateMarking,
      ∀ e : CoordinateMarking, decode (s, r) = e
  vectorLaw :
    ¬ ∃ decode : (IntrinsicObject × R) × Measure ℝ →
        Measure (EuclideanSpace ℝ (Fin 4)),
      ∀ P : VectorLawPacket, decode ((s, r), vectorRadius P) = P.val
  treeLaw :
    ¬ ∃ decode : (IntrinsicObject × R) × PMF ℕ → PMF IncreasingRootedTree,
      ∀ P : PMF IncreasingRootedTree,
        decode ((s, r), P.map IncreasingRootedTree.order) = P
  stationaryLaw :
    ¬ ∃ decode : (IntrinsicObject × R) ×
        (Set ℂ × ComplexMeasure OpNonnegativeRay) → Measure ℝ,
      ∀ P : NativeGammaStationaryRealization,
        decode ((s, r), stationarySpectrumMixingData P) =
          stationaryCoordinateLaw P
  processIncrements :
    ¬ ∃ decode : (IntrinsicObject × R) × Measure ℝ → Prop,
      ∀ P : ProcessPacket, decode ((s, r), P.timeOne) = P.independent
  matrixFamily :
    ¬ ∃ decode : (IntrinsicObject × R) × (ℝ → ℝ) → MatrixFamily,
      ∀ F, decode ((s, r), matrixSeed F) = F
  arithmeticLabels :
    ¬ ∃ decode : IntrinsicObject × R → (ℕ+ → ℕ+),
      ∀ E : ℕ+ ≃* ℕ+, decode (s, r) = E
  spatialObservable :
    ¬ ∃ decode : IntrinsicObject × R → (Plane → ℝ),
      ∀ f : Plane → ℝ, (∀ x, 0 ≤ f x) → OrthogonallyAdditive f →
        decode (s, r) = f
  spatialDimension :
    ¬ ∃ decode : IntrinsicObject × R → ℕ,
      ∀ P : SpatialPacket, (∀ x, 0 ≤ P.observable x) →
        OrthogonallyAdditive P.observable → decode (s, r) = P.dimension
  nativeComplexBundles :
    ¬ Nonempty RealProjectiveComplexLineTensorSquareIsomorphism
  spatialRigidity :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V],
      (2 : Cardinal) ≤ Module.rank ℝ V → (f : V → ℝ) →
      OrthogonallyAdditive f → (∀ x, 0 ≤ f x) →
      ∃! c : ℝ, 0 ≤ c ∧ ∀ x, f x = c * ‖x‖ ^ 2
  radialCancellation :
    ∀ (D : ℝ) (f : ℝ → ℝ),
      DifferentiableOn ℝ f (Set.Ioi 0) → ∀ (x f₂ : ℝ),
      0 < x → f x ≠ 0 → HasDerivAt (deriv f) f₂ x →
      ((deriv (deriv (fun y => radialWeight ((D - 1) / 2) y * f y)) x /
        (radialWeight ((D - 1) / 2) x * f x) -
        (deriv (deriv f) x / f x + (D - 1) / x * (deriv f x / f x)) = 0) ↔
        D = 1 ∨ D = 3)
  radialDimensionThree :
    ∀ (D : ℝ), 2 ≤ D → ∀ (f : ℝ → ℝ),
      DifferentiableOn ℝ f (Set.Ioi 0) → ∀ (x f₂ : ℝ),
      0 < x → f x ≠ 0 → HasDerivAt (deriv f) f₂ x →
      ((deriv (deriv (fun y => radialWeight ((D - 1) / 2) y * f y)) x /
        (radialWeight ((D - 1) / 2) x * f x) -
        (deriv (deriv f) x / f x + (D - 1) / x * (deriv f x / f x)) = 0) ↔
        D = 3)
  radialProfileNotIdentified :
    (∀ x > 0, deriv (deriv (fun y => radialWeight 1 y)) x /
      radialWeight 1 x = 0) ∧
      ¬ (∀ x > 0, (1 : ℝ) = H x)

theorem scalar_boundary_with_native_bundle {R : Type*}
    (s : IntrinsicObject) (r : R) : ScalarBoundaryWithNativeBundle s R r where
  placementScale := no_placement_decoder_without_scale (s, r)
  placementOffset := no_placement_decoder_without_offset (s, r)
  coordinateMarking := coordinate_marking_no_decoder s r
  vectorLaw := vector_packet_no_decoder s r
  treeLaw := tree_packet_no_decoder s r
  stationaryLaw := stationary_spectrum_mixing_no_decoder s r
  processIncrements := process_packet_no_decoder s r
  matrixFamily := matrix_packet_no_decoder s r
  arithmeticLabels := arithmetic_packet_no_decoder s r
  spatialObservable := no_spatial_observable_decoder (s, r)
  spatialDimension := no_spatial_dimension_decoder (s, r)
  nativeComplexBundles := real_projective_complex_line_not_isomorphic_tensor_square
  spatialRigidity := by
    intro V _ _ hdim f hf hpos
    exact spatial_observable_reconstruction hdim f hf hpos
  radialCancellation := spatial_radial_cancellation
  radialDimensionThree := spatial_radial_dimension_three
  radialProfileNotIdentified := radial_cancellation_does_not_identify_profile

end
end Sigma.Closure
