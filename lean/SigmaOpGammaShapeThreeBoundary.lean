import SigmaOpGammaShapeThreeNativeBoundary
import SigmaOpGammaShapeTwoMixing
import SigmaOpGammaShapeThreeInvariants

namespace Sigma
noncomputable section
open MeasureTheory Set
set_option maxHeartbeats 800000

theorem gamma_shape_three_resolvent_compact (a : ℝ) (ha : 0 < a) :
    IsCompactOperator (gammaShapeThreeResolvent a ha) := by
  exact ((laguerre_resolvent_compact a ha).comp_clm
    gammaShapeUnitary.symm.toLinearIsometry.toContinuousLinearMap).continuous_comp
      gammaShapeUnitary.continuous

/-- The generic mixing inverse is the same actual shift inverse used in the
spectral trace and determinant results. -/
theorem gamma_shape_three_native_resolvent_eq :
    gammaShapeThreeResolventOne = gammaShapeThreeResolvent 1 (by norm_num) :=
  operator_two_sided_resolvents_unique gammaShapeThreeSpectralOperator 1 _ _
    (op_nonnegative_shift_resolvent gammaShapeThreeSpectralOperator
      gamma_shape_three_spectral_selfAdjoint gamma_shape_three_spectral_nonnegative)
    (gamma_shape_three_resolvent 1 (by norm_num))

theorem gamma_shape_three_common_mixing_iff (μ : ComplexMeasure OpNonnegativeRay) :
    (∀ x : GammaShapeThreeWeightedHilbert,
      complexStrongIntegral μ (fun s => gammaShapeThreeHeat s.val x) =
        gammaShapeThreeSquaredResolvent 1 (by norm_num) x) ↔
      μ = nonnegativeGammaComplexMeasure := by
  exact (forall_equations_congr
    (fun x => gammaShapeThreeResolventOne (gammaShapeThreeResolventOne x))
    (gammaShapeThreeSquaredResolvent 1 (by norm_num))
    (fun x => complexStrongIntegral μ (fun s => gammaShapeThreeHeat s.val x))
    (operator_square_apply_eq _ _ gamma_shape_three_native_resolvent_eq)).symm.trans
      (gamma_shape_three_complex_mixing_iff μ)

theorem gamma_shapes_two_three_common_mixing (μ : ComplexMeasure OpNonnegativeRay) :
    ((∀ x : LaguerreWeightedHilbert,
      complexStrongIntegral μ (fun s => laguerreHeatOperator s.val s.property x) =
        laguerreSquaredResolvent 1 (by norm_num) x) ∧
     (∀ x : GammaShapeThreeWeightedHilbert,
      complexStrongIntegral μ (fun s => gammaShapeThreeHeat s.val x) =
        gammaShapeThreeSquaredResolvent 1 (by norm_num) x)) ↔
      μ = nonnegativeGammaComplexMeasure := by
  exact common_iff_intersection (gamma_shape_two_common_mixing_iff μ)
    (gamma_shape_three_common_mixing_iff μ)

end
end Sigma
