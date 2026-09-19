import SigmaProbCompletionSamples
import SigmaProbSupport
import SigmaProbCompletionLevyRegularity

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

def gammaDriftedProbability (d : ℝ) : Measure ℝ :=
  gammaProbability.map (fun t => d+t)

instance gamma_drifted_probability (d : ℝ) : IsProbabilityMeasure (gammaDriftedProbability d) :=
  isProbabilityMeasure_map (measurable_const.add measurable_id).aemeasurable

theorem gamma_drifted_probability_mean (d : ℝ) :
    (∫ t, t ∂gammaDriftedProbability d) = d+2 := by
  have hm : Measurable (fun t : ℝ => d+t) := by fun_prop
  rw [gammaDriftedProbability, integral_map hm.aemeasurable
    (show AEStronglyMeasurable (fun t : ℝ => t) _ from continuous_id.aestronglyMeasurable)]
  have hi : Integrable (fun t : ℝ => t) gammaProbability := by
    simpa using gamma_probability_monomial_integrable 1
  rw [integral_add (integrable_const d) hi, gamma_probability_mean]
  simp

theorem topological_support_translation (μ : Measure ℝ) (d x : ℝ) :
    x ∈ topologicalMeasureSupport (μ.map (fun t => d+t)) ↔
      x-d ∈ topologicalMeasureSupport μ := by
  change (∀ U : Set ℝ, IsOpen U → x ∈ U → 0 < μ.map (fun t => d+t) U) ↔
    ∀ V : Set ℝ, IsOpen V → x-d ∈ V → 0 < μ V
  have hm : Measurable (fun t : ℝ => d+t) := by fun_prop
  constructor
  · intro h V hV hx
    have hh := h ((fun y : ℝ => y-d) ⁻¹' V)
      (hV.preimage (continuous_id.sub continuous_const)) hx
    have hmV : MeasurableSet ((fun y : ℝ => y-d) ⁻¹' V) :=
      (hV.preimage (continuous_id.sub continuous_const)).measurableSet
    rw [Measure.map_apply hm hmV] at hh
    have he : (fun t : ℝ => d+t) ⁻¹' ((fun y : ℝ => y-d) ⁻¹' V) = V := by
      ext t
      simp only [mem_preimage]
      rw [add_sub_cancel_left]
    rwa [he] at hh
  · intro h U hU hx
    rw [Measure.map_apply hm hU.measurableSet]
    apply h ((fun t : ℝ => d+t) ⁻¹' U)
      (hU.preimage (continuous_const.add continuous_id))
    simpa only [mem_preimage, add_sub_cancel] using hx

theorem gamma_drifted_probability_support (d : ℝ) :
    topologicalMeasureSupport (gammaDriftedProbability d) = Ici d := by
  ext x
  rw [gammaDriftedProbability, topological_support_translation,
    gamma_probability_topological_support]
  simp only [mem_Ici]
  exact sub_nonneg

theorem gamma_drifted_probability_support_infimum (d : ℝ) :
    IsGLB (topologicalMeasureSupport (gammaDriftedProbability d)) d := by
  rw [gamma_drifted_probability_support]
  exact isGLB_Ici

theorem gamma_drift_zero_iff_mean_two (d : ℝ) :
    d = 0 ↔ (∫ t, t ∂gammaDriftedProbability d) = 2 := by
  rw [gamma_drifted_probability_mean]
  constructor <;> intro h <;> linarith

theorem gamma_drift_zero_iff_support_infimum_zero (d : ℝ) :
    d = 0 ↔ IsGLB (topologicalMeasureSupport (gammaDriftedProbability d)) 0 := by
  constructor
  · intro h
    simpa [h] using gamma_drifted_probability_support_infimum 0
  · intro h
    exact (gamma_drifted_probability_support_infimum d).unique h

theorem gamma_drifted_probability_nonnegative (d : ℝ) (hd : 0 ≤ d) :
    ∀ᵐ t ∂gammaDriftedProbability d, 0 ≤ t := by
  have hm : Measurable (fun t : ℝ => d+t) := by fun_prop
  rw [gammaDriftedProbability, ae_map_iff hm.aemeasurable
    measurableSet_Ici]
  have hg : ∀ᵐ t ∂gammaProbability, 0 ≤ t := by
    rw [← gamma_completion_one]
    exact gamma_completion_nonnegative 1
  filter_upwards [hg] with t ht
  exact add_nonneg hd ht

theorem gamma_drifted_probability_laplace (d l : ℝ) (hl : 0 ≤ l) :
    realLaplace (gammaDriftedProbability d) l =
      Real.exp (-(d*l+gammaLaplaceExponent l)) := by
  have hm : Measurable (fun t : ℝ => d+t) := by fun_prop
  have hf : AEStronglyMeasurable (fun t : ℝ => Real.exp (-(l*t)))
      (gammaDriftedProbability d) :=
    (continuous_const.mul continuous_id).neg.rexp.aestronglyMeasurable
  rw [realLaplace, gammaDriftedProbability,
    integral_map hm.aemeasurable hf]
  have he : (fun t : ℝ => Real.exp (-(l*(d+t)))) =
      fun t => Real.exp (-(d*l))*Real.exp (-(l*t)) := by
    funext t
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, integral_mul_left]
  change Real.exp (-(d*l))*realLaplace gammaProbability l = _
  rw [← gamma_completion_one, gamma_completion_laplace 1 l hl, ← Real.exp_add]
  simp only [NNReal.coe_one, mul_one, gammaLaplaceExponent]
  congr 1
  ring

theorem gamma_drifted_probability_unique (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (d : ℝ) (hd : 0 ≤ d)
    (hl : ∀ l : ℝ, 0 ≤ l → realLaplace μ l = Real.exp (-(d*l+gammaLaplaceExponent l))) :
    μ = gammaDriftedProbability d := by
  apply nonnegative_integer_laplace_unique _ _ hμ (gamma_drifted_probability_nonnegative d hd)
  intro n
  rw [hl n (Nat.cast_nonneg n), gamma_drifted_probability_laplace d n (Nat.cast_nonneg n)]

def gammaDriftCompletion (d : ℝ) (r : ℝ≥0) : Measure ℝ :=
  (gammaCompletion r).map (fun t => d*(r:ℝ)+t)

instance gamma_drift_completion_probability (d : ℝ) (r : ℝ≥0) :
    IsProbabilityMeasure (gammaDriftCompletion d r) :=
  isProbabilityMeasure_map (measurable_const.add measurable_id).aemeasurable

theorem gamma_drift_completion_zero (d : ℝ) : gammaDriftCompletion d 0 = Measure.dirac 0 := by
  simp [gammaDriftCompletion, gamma_completion_zero]

theorem gamma_drift_completion_one (d : ℝ) : gammaDriftCompletion d 1 = gammaDriftedProbability d := by
  simp [gammaDriftCompletion, gamma_completion_one, gammaDriftedProbability]

theorem gamma_drift_completion_nonnegative (d : ℝ) (hd : 0 ≤ d) (r : ℝ≥0) :
    ∀ᵐ t ∂gammaDriftCompletion d r, 0 ≤ t := by
  have hm : Measurable (fun t : ℝ => d*(r:ℝ)+t) := by fun_prop
  rw [gammaDriftCompletion, ae_map_iff hm.aemeasurable measurableSet_Ici]
  filter_upwards [gamma_completion_nonnegative r] with t ht
  exact add_nonneg (mul_nonneg hd r.coe_nonneg) ht

theorem gamma_drift_completion_laplace (d : ℝ) (r : ℝ≥0) (l : ℝ) (hl : 0 ≤ l) :
    realLaplace (gammaDriftCompletion d r) l =
      Real.exp (-(r:ℝ)*(d*l+gammaLaplaceExponent l)) := by
  have hm : Measurable (fun t : ℝ => d*(r:ℝ)+t) := by fun_prop
  have hf : AEStronglyMeasurable (fun t : ℝ => Real.exp (-(l*t)))
      (gammaDriftCompletion d r) :=
    (continuous_const.mul continuous_id).neg.rexp.aestronglyMeasurable
  rw [realLaplace, gammaDriftCompletion, integral_map hm.aemeasurable hf]
  have he : (fun t : ℝ => Real.exp (-(l*(d*(r:ℝ)+t)))) =
      fun t => Real.exp (-(d*(r:ℝ)*l))*Real.exp (-(l*t)) := by
    funext t
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, integral_mul_left]
  change Real.exp (-(d*(r:ℝ)*l))*realLaplace (gammaCompletion r) l = _
  rw [gamma_completion_laplace r l hl, ← Real.exp_add]
  unfold gammaLaplaceExponent
  congr 1
  ring

theorem gamma_drift_completion_convolution (d : ℝ) (hd : 0 ≤ d) (r s : ℝ≥0) :
    (gammaDriftCompletion d r).conv (gammaDriftCompletion d s) = gammaDriftCompletion d (r+s) := by
  have he : (gammaDriftCompletion d r).conv (gammaDriftCompletion d s) =
      independentAffineSum (gammaDriftCompletion d r) (gammaDriftCompletion d s) 1 := by
    simp only [Measure.conv, independentAffineSum, one_mul]
  rw [he]
  apply nonnegative_integer_laplace_unique _ _
    (independent_sum_nonnegative _ _ (gamma_drift_completion_nonnegative d hd r)
      (gamma_drift_completion_nonnegative d hd s)) (gamma_drift_completion_nonnegative d hd (r+s))
  intro n
  rw [independent_affine_sum_laplace, one_mul,
    gamma_drift_completion_laplace d r n (Nat.cast_nonneg n),
    gamma_drift_completion_laplace d s n (Nat.cast_nonneg n),
    gamma_drift_completion_laplace d (r+s) n (Nat.cast_nonneg n), ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem gamma_drifted_probability_distinct {d e : ℝ} (hne : d ≠ e) :
    gammaDriftedProbability d ≠ gammaDriftedProbability e := by
  intro h
  have hh := congrArg (fun ρ : Measure ℝ => ∫ t, t ∂ρ) h
  dsimp only at hh
  rw [gamma_drifted_probability_mean, gamma_drifted_probability_mean] at hh
  apply hne
  linarith

theorem BernsteinRepresentation.gamma_levy_exponent (B : BernsteinRepresentation)
    (hL : B.levy = gammaCompletionLevyMeasure) (l : ℝ) (hl : 0 ≤ l) :
    B.exponent l = B.killing+B.drift*l+gammaLaplaceExponent l := by
  have hg := gamma_bernstein_representation_exponent l hl
  simp only [BernsteinRepresentation.exponent, gammaBernsteinRepresentation,
    zero_add, zero_mul] at hg
  simp only [BernsteinRepresentation.exponent, hL, hg]

theorem bernstein_probability_excludes_killing (B : BernsteinRepresentation)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (ht : realLaplace μ 0 = Real.exp (-B.exponent 0)) : B.killing = 0 := by
  simp only [realLaplace, zero_mul, neg_zero, Real.exp_zero, integral_const, measure_univ,
    ENNReal.one_toReal, smul_eq_mul, mul_one, BernsteinRepresentation.exponent,
    mul_zero, add_zero, sub_self, integral_zero] at ht
  have he : -B.killing = 0 := Real.exp_injective (by simpa using ht.symm)
  linarith

theorem probability_with_gamma_levy_is_shifted_gamma (B : BernsteinRepresentation)
    (hL : B.levy = gammaCompletionLevyMeasure) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t)
    (ht : ∀ l : ℝ, 0 ≤ l → realLaplace μ l = Real.exp (-B.exponent l)) :
    B.killing = 0 ∧ μ = gammaDriftedProbability B.drift := by
  have hk := bernstein_probability_excludes_killing B μ (ht 0 le_rfl)
  refine ⟨hk, gamma_drifted_probability_unique μ hμ B.drift B.drift_nonnegative ?_⟩
  intro l hl
  rw [ht l hl, B.gamma_levy_exponent hL l hl, hk, zero_add]

theorem gamma_drifted_probability_zero : gammaDriftedProbability 0 = gammaProbability := by
  simp only [gammaDriftedProbability, zero_add]
  exact Measure.map_id

/-- All four drift tests, and their identification of the actual probability
convolution family. The probability premise derives the absence of killing. -/
theorem gamma_levy_drift_characterization (B : BernsteinRepresentation)
    (hL : B.levy = gammaCompletionLevyMeasure) (μ : ℝ≥0 → Measure ℝ)
    (hp : ∀ r, IsProbabilityMeasure (μ r)) (hs : ∀ r, ∀ᵐ t ∂μ r, 0 ≤ t)
    (hc : ∀ r s, (μ r).conv (μ s) = μ (r+s))
    (ht : ∀ l : ℝ, 0 ≤ l → realLaplace (μ 1) l = Real.exp (-B.exponent l)) :
    B.killing = 0 ∧
    (B.drift = 0 ↔ μ = gammaCompletion) ∧
    (B.drift = 0 ↔ Tendsto (fun l : ℝ => B.exponent l/l) atTop (𝓝 0)) ∧
    (B.drift = 0 ↔ IsGLB (topologicalMeasureSupport (μ 1)) 0) ∧
    (B.drift = 0 ↔ (∫ t, t ∂μ 1) = 2) := by
  letI := hp 1
  obtain ⟨hk,hm⟩ := probability_with_gamma_levy_is_shifted_gamma B hL (μ 1) (hs 1) ht
  refine ⟨hk, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro hd
      apply gamma_completion_unique μ hp hs
      · intro r s
        simpa only [Measure.conv, independentAffineSum, one_mul] using hc r s
      · rw [hm, hd, gamma_drifted_probability_zero]
    · intro he
      have hm' : gammaDriftedProbability B.drift = gammaProbability := by
        rw [← hm, he, gamma_completion_one]
      have hi := congrArg (fun ρ : Measure ℝ => ∫ t, t ∂ρ) hm'
      dsimp only at hi
      rw [gamma_drifted_probability_mean, gamma_probability_mean] at hi
      linarith
  · have he : (fun l : ℝ => B.exponent l/l) =ᶠ[atTop]
        (fun l : ℝ => (B.drift*l+gammaLaplaceExponent l)/l) := by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with l hl
      rw [B.gamma_levy_exponent hL l hl, hk, zero_add]
    rw [tendsto_congr' he]
    exact gamma_drift_zero_iff_sublinear B.drift
  · rw [hm]
    exact gamma_drift_zero_iff_support_infimum_zero B.drift
  · rw [hm]
    exact gamma_drift_zero_iff_mean_two B.drift

/-- Changing the nonnegative drift preserves the actual Lévy measure. -/
def gammaDriftBernsteinRepresentation (d : ℝ) (hd : 0 ≤ d) : BernsteinRepresentation where
  killing := 0
  drift := d
  killing_nonnegative := le_rfl
  drift_nonnegative := hd
  levy := gammaCompletionLevyMeasure
  levy_positive_support := gamma_completion_levy_positive_support
  levy_integrable := gamma_completion_levy_integrability

theorem gamma_drift_completion_levy_representation (d : ℝ) (hd : 0 ≤ d)
    (r : ℝ≥0) (l : ℝ) (hl : 0 ≤ l) :
    realLaplace (gammaDriftCompletion d r) l =
      Real.exp (-(r:ℝ)*(gammaDriftBernsteinRepresentation d hd).exponent l) := by
  rw [gamma_drift_completion_laplace d r l hl,
    (gammaDriftBernsteinRepresentation d hd).gamma_levy_exponent rfl l hl]
  simp only [gammaDriftBernsteinRepresentation, zero_add]

theorem gamma_drift_completions_distinct {d e : ℝ} (hne : d ≠ e) :
    gammaDriftCompletion d ≠ gammaDriftCompletion e := by
  intro h
  have hh := congrFun h 1
  rw [gamma_drift_completion_one, gamma_drift_completion_one] at hh
  exact gamma_drifted_probability_distinct hne hh

end
end Sigma
