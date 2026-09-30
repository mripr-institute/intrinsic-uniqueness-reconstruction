import SigmaClosureCompletePresentations
import SigmaClosureNormalizedPerturbation
import SigmaClosureBoundary
import SigmaClosureThom
import SigmaRealProjectiveRationalCharacteristic
import Mathlib.Logic.Equiv.Option

namespace Sigma.Closure
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

/-- An external selection retains its carrier along with the selected object.
Dependent records such as a base together with its bundle fit in one packet. -/
structure ExternalSelection where
  Carrier : Type
  selected : Carrier

/-- One complete intrinsic certificate, optional placement, and the requested
packets reconstruct the marked target. The arbitrary packet type may contain
a dependent family of ExternalSelection records; no carrier is forgotten. -/
def sufficientDecomposition (K : Type) [Field K] [CharZero K]
    (A : CompletePresentation K) (Packets : Type*) :
    ((completePresentation K A).data.Solution × Option Placement × Packets) ≃
      (IntrinsicObject × Option (Set.range Placement.presentation) × Packets) :=
  Equiv.prodCongr (completePresentation K A).reconstruction.symm
    (Equiv.prodCongr (Equiv.optionCongr placementEquivalence) (Equiv.refl Packets))

theorem sufficient_decomposition_roundtrips (K : Type) [Field K] [CharZero K]
    (A : CompletePresentation K) (Packets : Type*) :
    (∀ x, (sufficientDecomposition K A Packets).symm
      (sufficientDecomposition K A Packets x) = x) ∧
    (∀ y, sufficientDecomposition K A Packets
      ((sufficientDecomposition K A Packets).symm y) = y) :=
  ⟨(sufficientDecomposition K A Packets).symm_apply_apply,
    (sufficientDecomposition K A Packets).apply_symm_apply⟩

/-- The relaxed intrinsic deletion class, without an alternative complete
certificate or linked scalar-identifying realization. -/
def RelaxedIntrinsicConditions (J : ℝ → ℝ) : Prop :=
  (∀ t > 0, AnalyticAt ℝ J t) ∧ StrictConvexOn ℝ (Ioi 0) J ∧
    J 1 = 0 ∧ deriv J 1 = 0 ∧ deriv (deriv J) 1 = 1 ∧
    (∫ t : ℝ in Ioi 0, Real.exp (-1 - J t)) = 1

theorem intrinsic_relaxed_conditions : RelaxedIntrinsicConditions I := by
  have he : perturbedIntrinsic 0 0 = I := by funext t; simp [perturbedIntrinsic]
  rw [← he]
  obtain ⟨η, hη, hc⟩ := perturbed_intrinsic_strictConvex_near_zero
  have ha := perturbed_intrinsic_anchors 0 0
  refine ⟨fun _ ht => perturbed_intrinsic_analytic 0 0 ht,
    hc 0 0 (by simpa using hη) (by simpa using hη),
    ha.1, ha.2.1, ha.2.2, ?_⟩
  rw [← perturbation_mass_integral, perturbation_mass_zero]

theorem intrinsic_packet_no_decoder {R : Type*} (retained : R) :
    ¬ ∃ decode : R → ScalarFunction,
      ∀ J : ℝ → ℝ, RelaxedIntrinsicConditions J →
        decode retained = fun t : PositiveCoordinate => J t := by
  obtain ⟨J, hJ, hconvex, h1, hd1, hd2, hmass, _, _, hne⟩ :=
    normalized_intrinsic_deletion_witness
  rintro ⟨decode, hdecode⟩
  apply hne
  have he := (hdecode J ⟨hJ, hconvex, h1, hd1, hd2, hmass⟩).symm.trans
    (hdecode I intrinsic_relaxed_conditions)
  intro t ht
  exact congrFun he ⟨t, ht⟩

/-- All deletion witnesses with an arbitrary common retained context. The
rational characteristic clause concerns the actual native K⁰ group, and
applies in particular to the ordinary normalized Chern character. -/
structure CompleteScalarBoundary (s : IntrinsicObject) (R : Type*) (r : R)
    extends ScalarBoundaryWithNativeBundle s R r : Prop where
  intrinsicShape :
    ¬ ∃ decode : R → ScalarFunction,
      ∀ J : ℝ → ℝ, RelaxedIntrinsicConditions J →
        decode r = fun t : PositiveCoordinate => J t
  rationalCharacteristic :
    ∀ (H : Type) [AddCommGroup H] [Module ℚ H]
      (χ : FiniteComplexBundle.K0 RealProjectivePlane →+ H),
      ¬ ∃ decode : ((IntrinsicObject × R) × H) →
          FiniteComplexBundle.K0 RealProjectivePlane,
        ∀ V : FiniteComplexBundle RealProjectivePlane,
          decode ((s, r), χ (FiniteComplexBundle.kClass V)) =
            FiniteComplexBundle.kClass V
  integralLineCharacteristic :
    ∀ (H : Type) (c : FiniteComplexBundle RealProjectivePlane → H),
      (∀ V W : FiniteComplexBundle RealProjectivePlane,
        Module.finrank ℂ V.Model = 1 → Module.finrank ℂ W.Model = 1 →
        c V = c W → Nonempty (FiniteComplexBundle.Iso V W)) →
      ¬ ∃ decode : IntrinsicObject × R → H,
        ∀ V : FiniteComplexBundle RealProjectivePlane,
          Module.finrank ℂ V.Model = 1 → decode (s, r) = c V
  orthogonalComposition :
    ∃ f g : Plane → ℝ, (∀ x, 0 ≤ f x) ∧ (∀ x, 0 ≤ g x) ∧
      OrthogonallyAdditive f ∧ ¬ OrthogonallyAdditive g
  radialScale :
    ∃ f g : Plane → ℝ, (∀ x, 0 ≤ f x) ∧ (∀ x, 0 ≤ g x) ∧
      OrthogonallyAdditive f ∧ OrthogonallyAdditive g ∧ f ≠ g

theorem complete_scalar_boundary {R : Type*} (s : IntrinsicObject) (r : R) :
    CompleteScalarBoundary s R r where
  toScalarBoundaryWithNativeBundle := scalar_boundary_with_native_bundle s r
  intrinsicShape := intrinsic_packet_no_decoder r
  rationalCharacteristic := fun _ _ _ χ => real_projective_scalar_rational_data_no_k0_decoder χ (s, r)
  integralLineCharacteristic := fun _ c hc =>
    real_projective_integral_characteristic_no_decoder c hc (s, r)
  orthogonalComposition := plane_composition_deletion
  radialScale := plane_scale_deletion

/-- Global C/D: every complete certificate yields the sufficient marked
decomposition, and every declared deletion has a native witness. Canonical
recipe existence and uniqueness is the imported fixed_context_native_closure
theorem, with all six contexts and their stated foundations. -/
theorem global_relative_irredundancy (K : Type) [Field K] [CharZero K]
    (A : CompletePresentation K) (Packets : Type*) :
    Nonempty (((completePresentation K A).data.Solution × Option Placement × Packets) ≃
      (IntrinsicObject × Option (Set.range Placement.presentation) × Packets)) ∧
    (∀ (s : IntrinsicObject) (r : Packets), CompleteScalarBoundary s Packets r) :=
  ⟨⟨sufficientDecomposition K A Packets⟩, fun s r => complete_scalar_boundary s r⟩

end
end Sigma.Closure
