import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The Hausdorff measure-uniqueness argument used in final:O4, O5, and O6.
The objects are actual finite Borel measures and Bochner integrals.
-/

namespace Sigma
noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal

abbrev OpUnitInterval := Set.Icc (0 : ℝ) 1

theorem op_continuous_integrable (μ : Measure OpUnitInterval) [IsFiniteMeasure μ]
    (f : C(OpUnitInterval, ℝ)) : Integrable f μ :=
  (BoundedContinuousFunction.mkOfCompact f).integrable μ

def opCompactIntegral (μ : Measure OpUnitInterval) [IsFiniteMeasure μ] :
    C(OpUnitInterval, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := by
        intro f g
        exact integral_add (op_continuous_integrable μ f) (op_continuous_integrable μ g)
      map_smul' := by
        intro c f
        simp only [ContinuousMap.smul_apply, RingHom.id_apply, integral_smul] }
    (μ univ).toReal
    (by
      intro f
      simpa only [mul_comm] using
        norm_integral_le_of_norm_le_const (μ := μ)
          (Filter.Eventually.of_forall f.norm_coe_le_norm))

@[simp] theorem opCompactIntegral_apply (μ : Measure OpUnitInterval) [IsFiniteMeasure μ]
    (f : C(OpUnitInterval, ℝ)) : opCompactIntegral μ f = ∫ x, f x ∂μ := rfl

theorem op_polynomial_integrable (μ : Measure OpUnitInterval) [IsFiniteMeasure μ]
    (p : Polynomial ℝ) : Integrable (fun x : OpUnitInterval => p.eval (x : ℝ)) μ :=
  op_continuous_integrable μ (p.toContinuousMapOn _)

theorem op_moments_identify_polynomial_integrals
    (μ ν : Measure OpUnitInterval) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : ∀ n : ℕ, ∫ x : OpUnitInterval, (x : ℝ) ^ n ∂μ =
      ∫ x : OpUnitInterval, (x : ℝ) ^ n ∂ν)
    (p : Polynomial ℝ) :
    ∫ x : OpUnitInterval, p.eval (x : ℝ) ∂μ =
      ∫ x : OpUnitInterval, p.eval (x : ℝ) ∂ν := by
  induction p using Polynomial.induction_on' with
  | h_add p q hp hq =>
      simp only [Polynomial.eval_add]
      rw [integral_add (op_polynomial_integrable μ p) (op_polynomial_integrable μ q),
        integral_add (op_polynomial_integrable ν p) (op_polynomial_integrable ν q), hp, hq]
  | h_monomial n a =>
      simp only [Polynomial.eval_monomial, integral_mul_left, hm n]

theorem op_moments_identify_continuous_integrals
    (μ ν : Measure OpUnitInterval) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : ∀ n : ℕ, ∫ x : OpUnitInterval, (x : ℝ) ^ n ∂μ =
      ∫ x : OpUnitInterval, (x : ℝ) ^ n ∂ν)
    (f : C(OpUnitInterval, ℝ)) : ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
  have hc : IsClosed {g : C(OpUnitInterval, ℝ) |
      opCompactIntegral μ g = opCompactIntegral ν g} :=
    isClosed_eq (opCompactIntegral μ).continuous (opCompactIntegral ν).continuous
  have hsub : (polynomialFunctions (Set.Icc (0 : ℝ) 1) :
      Set C(OpUnitInterval, ℝ)) ⊆
      {g | opCompactIntegral μ g = opCompactIntegral ν g} := by
    rw [polynomialFunctions_coe]
    rintro g ⟨p, rfl⟩
    exact op_moments_identify_polynomial_integrals μ ν hm p
  have hf := continuousMap_mem_polynomialFunctions_closure (0 : ℝ) 1 f
  exact (closure_minimal hsub hc) hf

/-- Hausdorff uniqueness for finite Borel measures on the actual compact interval. -/
theorem operator_hausdorff_moment_unique
    (μ ν : Measure OpUnitInterval) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : ∀ n : ℕ, ∫ x : OpUnitInterval, (x : ℝ) ^ n ∂μ =
      ∫ x : OpUnitInterval, (x : ℝ) ^ n ∂ν) : μ = ν := by
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro f
  apply (ENNReal.toReal_eq_toReal
    (ne_of_lt (f.lintegral_lt_top_of_nnreal μ))
    (ne_of_lt (f.lintegral_lt_top_of_nnreal ν))).mp
  rw [f.toReal_lintegral_coe_eq_integral μ, f.toReal_lintegral_coe_eq_integral ν]
  exact op_moments_identify_continuous_integrals μ ν hm
    ⟨fun x => (f x : ℝ), NNReal.continuous_coe.comp f.continuous⟩

abbrev OpNonnegativeRay := Set.Ici (0 : ℝ)

def opExpCoordinate (s : OpNonnegativeRay) : OpUnitInterval :=
  ⟨Real.exp (-(s : ℝ)), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr s.property)⟩

def opLogCoordinate (y : OpUnitInterval) : OpNonnegativeRay :=
  ⟨-Real.log (y : ℝ), neg_nonneg.mpr (Real.log_nonpos y.property.1 y.property.2)⟩

theorem opExpCoordinate_continuous : Continuous opExpCoordinate := by
  exact (Real.continuous_exp.comp continuous_subtype_val.neg).subtype_mk _

theorem opLogCoordinate_measurable : Measurable opLogCoordinate := by
  exact (Real.measurable_log.comp measurable_subtype_coe).neg.subtype_mk

theorem opLogCoordinate_leftInverse :
    Function.LeftInverse opLogCoordinate opExpCoordinate := by
  intro s
  apply Subtype.ext
  simp [opLogCoordinate, opExpCoordinate]

/-- Discrete Laplace observations identify actual finite nonnegative-time measures.
This is the measure-uniqueness component of final:O5; no spectral or
measure-uniqueness assertion is assumed. -/
theorem operator_nonnegative_mixing_measure_unique
    (μ ν : Measure OpNonnegativeRay) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n : ℕ, ∫ s : OpNonnegativeRay, Real.exp (-(n : ℝ) * s) ∂μ =
      ∫ s : OpNonnegativeRay, Real.exp (-(n : ℝ) * s) ∂ν) : μ = ν := by
  have hf := opExpCoordinate_continuous.measurable
  have hm : μ.map opExpCoordinate = ν.map opExpCoordinate := by
    apply operator_hausdorff_moment_unique
    intro n
    rw [integral_map hf.aemeasurable
        (continuous_subtype_val.pow n).measurable.aestronglyMeasurable,
      integral_map hf.aemeasurable
        (continuous_subtype_val.pow n).measurable.aestronglyMeasurable]
    have he : (fun s : OpNonnegativeRay => ((opExpCoordinate s : OpUnitInterval) : ℝ) ^ n) =
        (fun s : OpNonnegativeRay => Real.exp (-(n : ℝ) * s)) := by
      funext s
      simp only [opExpCoordinate]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he]
    exact h n
  have hb := congrArg (fun ρ : Measure OpUnitInterval => ρ.map opLogCoordinate) hm
  simp only [Measure.map_map opLogCoordinate_measurable hf] at hb
  have hi : opLogCoordinate ∘ opExpCoordinate = id :=
    funext opLogCoordinate_leftInverse
  simpa only [hi, Measure.map_id] using hb

end
end Sigma
