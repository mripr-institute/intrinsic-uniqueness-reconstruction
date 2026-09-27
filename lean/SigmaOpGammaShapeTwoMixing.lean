import SigmaOpGammaShapeThreeEvolution
import SigmaOpResolventUnique

namespace Sigma
noncomputable section
open MeasureTheory Set
set_option maxHeartbeats 800000

theorem gamma_shape_two_native_resolvent_eq :
    opNonnegativeResolvent laguerreCanonicalOperator laguerre_canonical_selfAdjoint
      laguerre_canonical_nonnegative = laguerreResolvent 1 (by norm_num) :=
  operator_two_sided_resolvents_unique laguerreCanonicalOperator 1 _ _
    (op_nonnegative_shift_resolvent laguerreCanonicalOperator
      laguerre_canonical_selfAdjoint laguerre_canonical_nonnegative)
    (laguerre_canonical_positive_shift_resolvent 1 (by norm_num))

theorem gamma_shape_two_heat_on_ray (s : OpNonnegativeRay) :
    opNonnegativeHeat laguerreCanonicalOperator laguerre_canonical_selfAdjoint
      laguerre_canonical_nonnegative s.val = laguerreHeatOperator s.val s.property :=
  laguerre_canonical_heat_eq s.val s.property

theorem gamma_shape_two_common_mixing_iff (μ : ComplexMeasure OpNonnegativeRay) :
    (∀ x : LaguerreWeightedHilbert,
      complexStrongIntegral μ (fun s => laguerreHeatOperator s.val s.property x) =
        laguerreSquaredResolvent 1 (by norm_num) x) ↔
      μ = nonnegativeGammaComplexMeasure := by
  have h := gamma_shape_two_complex_mixing_iff μ
  simpa only [gamma_shape_two_heat_on_ray, gamma_shape_two_native_resolvent_eq,
    laguerreSquaredResolvent, ContinuousLinearMap.comp_apply] using h

end
end Sigma
