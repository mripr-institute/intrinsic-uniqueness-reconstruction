import SigmaPresentations
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.Prod

namespace Sigma
noncomputable section
open Filter MeasureTheory
open scoped Topology

def gammaCharacteristic (x : ℝ) : ℂ := (1 - Complex.I * (x : ℂ))⁻¹ ^ 2

def residualCharacteristic (c x : ℝ) : ℂ :=
  ((1 - Complex.I * ((c * x : ℝ) : ℂ)) / (1 - Complex.I * (x : ℂ))) ^ 2

theorem characteristic_denominator_ne_zero (x : ℝ) :
    (1 - Complex.I * (x : ℂ)) ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  simp at hh

theorem residual_characteristic_telescopes (c x : ℝ) (n : ℕ) :
    residualCharacteristic c (c ^ n * x) *
        ((1 - Complex.I * ((c ^ n * x : ℝ) : ℂ)) /
          (1 - Complex.I * (x : ℂ))) ^ 2 =
      ((1 - Complex.I * ((c ^ (n + 1) * x : ℝ) : ℂ)) /
        (1 - Complex.I * (x : ℂ))) ^ 2 := by
  unfold residualCharacteristic
  rw [← mul_pow]
  have h0 := characteristic_denominator_ne_zero (c ^ n * x)
  have h1 := characteristic_denominator_ne_zero x
  rw [pow_succ]
  push_cast
  push_cast at h0 h1
  field_simp
  ring

theorem linked_characteristic_iteration (φ : ℝ → ℂ) (c : ℝ)
    (hlink : ∀ x, φ x = φ (c * x) * residualCharacteristic c x)
    (x : ℝ) (n : ℕ) :
    φ x = φ (c ^ n * x) *
      ((1 - Complex.I * ((c ^ n * x : ℝ) : ℂ)) /
        (1 - Complex.I * (x : ℂ))) ^ 2 := by
  induction n with
  | zero => simp [characteristic_denominator_ne_zero]
  | succ n ih =>
      rw [ih, hlink (c ^ n * x), mul_assoc, residual_characteristic_telescopes]
      congr 2
      rw [pow_succ]
      ring

/-- The exact P9 contraction inverse, with continuity only at the origin.
No positivity, support, moments, or analyticity of the candidate function is assumed. -/
theorem linked_characteristic_rigidity (φ : ℝ → ℂ) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcontinuous : ContinuousAt φ 0) (hzero : φ 0 = 1)
    (hlink : ∀ x, φ x = φ (c * x) * residualCharacteristic c x) :
    φ = gammaCharacteristic := by
  funext x
  have hp : Tendsto (fun n : ℕ => c ^ n * x) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const x
  have hφ : Tendsto (fun n : ℕ => φ (c ^ n * x)) atTop (𝓝 (1 : ℂ)) := by
    simpa [hzero] using hcontinuous.tendsto.comp hp
  have hz : Tendsto (fun n : ℕ => ((c ^ n * x : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hp
  have hnum : Tendsto (fun n : ℕ =>
      (1 - Complex.I * ((c ^ n * x : ℝ) : ℂ)) /
        (1 - Complex.I * (x : ℂ))) atTop
        (𝓝 ((1 - Complex.I * (x : ℂ))⁻¹)) := by
    have hconstant : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 (1 : ℂ)) :=
      tendsto_const_nhds
    simpa using ((hconstant.sub (hz.const_mul Complex.I)).div_const
      (1 - Complex.I * (x : ℂ)))
  have hout := hφ.mul (hnum.pow 2)
  have hout' : Tendsto (fun _ : ℕ => φ x) atTop (𝓝 (gammaCharacteristic x)) := by
    convert hout.congr' (Filter.Eventually.of_forall
      (fun n => (linked_characteristic_iteration φ c hlink x n).symm)) using 1
    simp [gammaCharacteristic]
  exact tendsto_nhds_unique tendsto_const_nhds hout'

theorem gamma_characteristic_link (c x : ℝ) :
    gammaCharacteristic x =
      gammaCharacteristic (c * x) * residualCharacteristic c x := by
  unfold gammaCharacteristic residualCharacteristic
  have h0 := characteristic_denominator_ne_zero (c * x)
  have h1 := characteristic_denominator_ne_zero x
  push_cast at h0
  field_simp [h0, h1]

theorem residual_characteristic_at_one (x : ℝ) :
    residualCharacteristic 1 x = 1 := by
  simp [residualCharacteristic, characteristic_denominator_ne_zero]

theorem endpoint_one_does_not_restrict (φ : ℝ → ℂ) (x : ℝ) :
    φ x = φ (1 * x) * residualCharacteristic 1 x := by
  simp [residual_characteristic_at_one]

/-- The actual characteristic integral of a measure on the whole real line. -/
def probabilityCharacteristic (μ : Measure ℝ) (x : ℝ) : ℂ :=
  ∫ t, Complex.exp (((x * t : ℝ) : ℂ) * Complex.I) ∂μ

theorem probability_characteristic_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    probabilityCharacteristic μ 0 = 1 := by
  simp [probabilityCharacteristic]

theorem probability_characteristic_continuous (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Continuous (probabilityCharacteristic μ) := by
  unfold probabilityCharacteristic
  apply continuous_of_dominated (bound := fun _ : ℝ => (1 : ℝ))
  · intro x
    exact ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
      continuous_const).cexp.aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall (fun t => by
      rw [Complex.norm_eq_abs, Complex.abs_exp_ofReal_mul_I])
  · exact integrable_const 1
  · exact Filter.Eventually.of_forall (fun t =>
      ((Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).mul
        continuous_const).cexp)

/-- P9 with a genuine characteristic integral. The assumptions are precisely the
linked factorization alternative in the theorem, not measure identification. -/
theorem linked_probability_characteristic (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hlink : ∀ x, probabilityCharacteristic μ x =
      probabilityCharacteristic μ (c * x) * residualCharacteristic c x) :
    probabilityCharacteristic μ = gammaCharacteristic := by
  exact linked_characteristic_rigidity _ c hc0 hc1
    (probability_characteristic_continuous μ).continuousAt
    (probability_characteristic_zero μ) hlink

/-- Addition of independently selected coordinates, encoded by the product measure. -/
def independentAffineSum (μ ν : Measure ℝ) (c : ℝ) : Measure ℝ :=
  Measure.map (fun z : ℝ × ℝ => c * z.1 + z.2) (μ.prod ν)

instance independentAffineSum_is_probability (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (c : ℝ) :
    IsProbabilityMeasure (independentAffineSum μ ν c) := by
  unfold independentAffineSum
  exact MeasureTheory.isProbabilityMeasure_map
    ((measurable_const.mul measurable_fst).add measurable_snd).aemeasurable

theorem independent_affine_sum_characteristic (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c x : ℝ) :
    probabilityCharacteristic (independentAffineSum μ ν c) x =
      probabilityCharacteristic μ (c * x) * probabilityCharacteristic ν x := by
  unfold probabilityCharacteristic independentAffineSum
  have hmap : Measurable (fun z : ℝ × ℝ => c * z.1 + z.2) :=
    (measurable_const.mul measurable_fst).add measurable_snd
  have hint : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (((x * t : ℝ) : ℂ) * Complex.I))
      (Measure.map (fun z : ℝ × ℝ => c * z.1 + z.2) (μ.prod ν)) :=
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
      continuous_const).cexp.aestronglyMeasurable
  rw [integral_map hmap.aemeasurable hint]
  have he : (fun z : ℝ × ℝ => Complex.exp (((x * (c * z.1 + z.2) : ℝ) : ℂ) * Complex.I)) =
      (fun z : ℝ × ℝ =>
        Complex.exp (((c * x * z.1 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((x * z.2 : ℝ) : ℂ) * Complex.I)) := by
    funext z
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  exact integral_prod_mul
    (fun t : ℝ => Complex.exp (((c * x * t : ℝ) : ℂ) * Complex.I))
    (fun t : ℝ => Complex.exp (((x * t : ℝ) : ℂ) * Complex.I))

/-- P9 from a genuine independent-sum law, with no support or moment premise on μ. -/
theorem independent_decomposition_forces_characteristic
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hresidual : probabilityCharacteristic ν = residualCharacteristic c)
    (hdecomp : independentAffineSum μ ν c = μ) :
    probabilityCharacteristic μ = gammaCharacteristic := by
  apply linked_probability_characteristic μ c hc0 hc1
  intro x
  rw [← hdecomp, independent_affine_sum_characteristic]
  rw [hdecomp, hresidual]

end
end Sigma
