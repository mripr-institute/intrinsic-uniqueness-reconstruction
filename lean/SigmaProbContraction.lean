import SigmaProbDeficit
import SigmaOpMixing
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Sigma
noncomputable section
open Filter MeasureTheory Set
open scoped Topology

def negativeDetector (x : ℝ) : ℝ := max 0 (-x) / (1 + max 0 (-x))

theorem negative_detector_continuous : Continuous negativeDetector := by
  apply Continuous.div (continuous_const.max continuous_id.neg)
    (continuous_const.add (continuous_const.max continuous_id.neg))
  intro x
  exact ne_of_gt (by have := le_max_left (0 : ℝ) (-x); positivity)

theorem negative_detector_bounds (x : ℝ) : 0 ≤ negativeDetector x ∧ negativeDetector x ≤ 1 := by
  have hq : 0 ≤ max 0 (-x) := le_max_left _ _
  unfold negativeDetector
  constructor
  · positivity
  · apply (div_le_one (by positivity : 0 < 1 + max 0 (-x))).mpr
    linarith

theorem negative_detector_nonnegative {x : ℝ} (hx : 0 ≤ x) : negativeDetector x = 0 := by
  simp [negativeDetector, max_eq_left (neg_nonpos.mpr hx)]

theorem negative_detector_antitone : Antitone negativeDetector := by
  intro x y hxy
  have hm : max 0 (-y) ≤ max 0 (-x) := max_le_max_left 0 (neg_le_neg hxy)
  have hx : 0 ≤ max 0 (-x) := le_max_left _ _
  have hy : 0 ≤ max 0 (-y) := le_max_left _ _
  unfold negativeDetector
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

theorem negative_detector_strict_contraction (c x : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hx : x < 0) :
    negativeDetector (c * x) < negativeDetector x := by
  have hcx : 0 ≤ -(c * x) := neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hc0 hx.le)
  have hnx : 0 ≤ -x := (neg_pos.mpr hx).le
  unfold negativeDetector
  rw [max_eq_right hcx, max_eq_right hnx]
  apply (div_lt_div_iff₀ (by linarith) (by linarith)).mpr
  have hp := mul_pos (sub_pos.mpr hc1) (neg_pos.mpr hx)
  nlinarith

theorem negative_detector_affine_le (c x y : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hy : 0 ≤ y) :
    negativeDetector (c * x + y) ≤ negativeDetector x := by
  by_cases hx : x < 0
  · exact le_trans (negative_detector_antitone (by linarith))
      (negative_detector_strict_contraction c x hc0 hc1 hx).le
  · have hx0 := le_of_not_gt hx
    rw [negative_detector_nonnegative hx0,
      negative_detector_nonnegative (add_nonneg (mul_nonneg hc0 hx0) hy)]

theorem negative_detector_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable negativeDetector μ := by
  apply (integrable_const (1 : ℝ)).mono' negative_detector_continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (negative_detector_bounds x).1]
    exact (negative_detector_bounds x).2)

/-- A real-line stationary affine contraction with nonnegative independent noise has
nonnegative support. The bounded detector avoids assuming any moment of the source. -/
theorem independent_contraction_positive_support
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hν : ∀ᵐ y ∂ν, 0 ≤ y) (hdecomp : independentAffineSum μ ν c = μ) :
    ∀ᵐ x ∂μ, 0 ≤ x := by
  let A : ℝ × ℝ → ℝ := fun z => negativeDetector z.1
  let B : ℝ × ℝ → ℝ := fun z => negativeDetector (c * z.1 + z.2)
  have hAc : Continuous A := negative_detector_continuous.comp continuous_fst
  have hBc : Continuous B := negative_detector_continuous.comp
    ((continuous_const.mul continuous_fst).add continuous_snd)
  have hAi : Integrable A (μ.prod ν) := by
    apply (integrable_const (1 : ℝ)).mono' hAc.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (negative_detector_bounds z.1).1]
      exact (negative_detector_bounds z.1).2)
  have hBi : Integrable B (μ.prod ν) := by
    apply (integrable_const (1 : ℝ)).mono' hBc.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (negative_detector_bounds (c*z.1+z.2)).1]
      exact (negative_detector_bounds (c*z.1+z.2)).2)
  have hA : (∫ z, A z ∂μ.prod ν) = ∫ x, negativeDetector x ∂μ := by
    simpa [A] using (integral_prod_mul (μ := μ) (ν := ν)
      negativeDetector (fun _ : ℝ => (1 : ℝ)))
  have hB : (∫ z, B z ∂μ.prod ν) = ∫ x, negativeDetector x ∂μ := by
    have hmap : Measurable (fun z : ℝ × ℝ => c * z.1 + z.2) :=
      (measurable_const.mul measurable_fst).add measurable_snd
    have he := integral_map (μ := μ.prod ν) hmap.aemeasurable
      negative_detector_continuous.aestronglyMeasurable
    change (∫ x, negativeDetector x ∂independentAffineSum μ ν c) = ∫ z, B z ∂μ.prod ν at he
    rw [hdecomp] at he
    exact he.symm
  have hνprod : ∀ᵐ z : ℝ × ℝ ∂μ.prod ν, 0 ≤ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae (isClosed_le continuous_const continuous_snd).measurableSet).mpr
    exact Filter.Eventually.of_forall (fun _ => hν)
  have hnonneg : 0 ≤ᵐ[μ.prod ν] (fun z => A z - B z) := by
    filter_upwards [hνprod] with z hz
    exact sub_nonneg.mpr (negative_detector_affine_le c z.1 z.2 hc0 hc1 hz)
  have hzero : (∫ z, A z - B z ∂μ.prod ν) = 0 := by
    rw [integral_sub hAi hBi, hA, hB, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg (hAi.sub hBi)).mp hzero
  have hxprod : ∀ᵐ z : ℝ × ℝ ∂μ.prod ν, 0 ≤ z.1 := by
    filter_upwards [hνprod, hae] with z hz he
    by_contra hn
    have hx : z.1 < 0 := lt_of_not_ge hn
    have hlt : B z < A z := lt_of_le_of_lt
      (negative_detector_antitone (by linarith : c * z.1 ≤ c * z.1 + z.2))
      (negative_detector_strict_contraction c z.1 hc0 hc1 hx)
    change A z - B z = 0 at he
    linarith
  filter_upwards [Measure.ae_ae_of_ae_prod hxprod] with x hx
  obtain ⟨y, hy⟩ := hx.exists
  exact hy

def realLaplace (μ : Measure ℝ) (s : ℝ) : ℝ := ∫ t, Real.exp (-(s * t)) ∂μ
def gammaResidualLaplace (c s : ℝ) : ℝ := ((1 + c * s) / (1 + s)) ^ 2

theorem independent_affine_sum_laplace (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c s : ℝ) :
    realLaplace (independentAffineSum μ ν c) s =
      realLaplace μ (c * s) * realLaplace ν s := by
  unfold realLaplace independentAffineSum
  have hm : Measurable (fun z : ℝ × ℝ => c * z.1 + z.2) :=
    (measurable_const.mul measurable_fst).add measurable_snd
  have hcont : Continuous (fun t : ℝ => Real.exp (-(s * t))) :=
    (continuous_const.mul continuous_id).neg.rexp
  rw [integral_map hm.aemeasurable hcont.aestronglyMeasurable]
  have hf : (fun z : ℝ × ℝ => Real.exp (-(s * (c * z.1 + z.2)))) =
      (fun z : ℝ × ℝ => Real.exp (-(c * s * z.1)) * Real.exp (-(s * z.2))) := by
    funext z
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hf]
  exact integral_prod_mul (fun t : ℝ => Real.exp (-(c * s * t)))
    (fun t : ℝ => Real.exp (-(s * t)))

theorem nonnegative_laplace_contraction_limit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (c s : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (hs : 0 ≤ s) :
    Tendsto (fun n : ℕ => realLaplace μ (c ^ n * s)) atTop (𝓝 1) := by
  have hp : Tendsto (fun n : ℕ => c ^ n * s) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const s
  have hi : Tendsto (fun n : ℕ => ∫ t, Real.exp (-(c ^ n * s * t)) ∂μ)
      atTop (𝓝 (∫ _ : ℝ, (1 : ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1 : ℝ))
    · intro n
      exact (continuous_const.mul continuous_id).neg.rexp.aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      filter_upwards [hμ] with t ht
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
        (mul_nonneg (mul_nonneg (pow_nonneg hc0 _) hs) ht))
    · exact Filter.Eventually.of_forall (fun t => by
        have he := Real.continuous_exp.continuousAt.tendsto.comp (hp.mul_const t).neg
        simpa only [Function.comp_def, zero_mul, neg_zero, Real.exp_zero] using he)
  simpa [realLaplace] using hi

theorem linked_laplace_iteration (L : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hlink : ∀ s ≥ 0, L s = L (c * s) * gammaResidualLaplace c s)
    (s : ℝ) (hs : 0 ≤ s) (n : ℕ) :
    L s = L (c ^ n * s) * ((1 + c ^ n * s) / (1 + s)) ^ 2 := by
  induction n with
  | zero => simp [ne_of_gt (by linarith : 0 < 1 + s)]
  | succ n ih =>
    rw [ih, hlink (c ^ n * s) (mul_nonneg (pow_nonneg hc _) hs)]
    have hne : 1 + c ^ n * s ≠ 0 := ne_of_gt (by positivity)
    have hne0 : 1 + s ≠ 0 := ne_of_gt (by positivity)
    have harg : c * (c ^ n * s) = c ^ (n + 1) * s := by rw [pow_succ]; ring
    rw [harg]
    unfold gammaResidualLaplace
    field_simp [hne, hne0]
    ring
    simp

/-- The measure-valued P9 inverse. Positive support is derived from stationarity;
no moments or initial support restrictions are imposed on the real-line source. -/
theorem independent_gamma_residual_identifies_real_line_law
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hν : ∀ᵐ y ∂ν, 0 ≤ y)
    (hresidual : ∀ s ≥ 0, realLaplace ν s = gammaResidualLaplace c s)
    (hdecomp : independentAffineSum μ ν c = μ) : μ = gammaProbability := by
  have hμ := independent_contraction_positive_support μ ν c hc0 hc1 hν hdecomp
  have hlink : ∀ s ≥ 0, realLaplace μ s =
      realLaplace μ (c * s) * gammaResidualLaplace c s := by
    intro s hs
    have he := independent_affine_sum_laplace μ ν c s
    rw [hdecomp, hresidual s hs] at he
    exact he
  have hL : ∀ s ≥ 0, realLaplace μ s = (1 + s)⁻¹ ^ 2 := by
    intro s hs
    have hp : Tendsto (fun n : ℕ => c ^ n * s) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const s
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hr := ((hconst.add hp).div_const (1 + s)).pow 2
    have hl := (nonnegative_laplace_contraction_limit μ hμ c s hc0 hc1 hs).mul hr
    have hlim : Tendsto (fun _ : ℕ => realLaplace μ s) atTop (𝓝 ((1+s)⁻¹ ^ 2)) := by
      convert hl.congr' (Filter.Eventually.of_forall (fun n =>
        (linked_laplace_iteration (realLaplace μ) c hc0 hlink s hs n).symm)) using 1
      simp
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  apply operator_full_line_mixing_characterization
  intro n
  simpa [realLaplace, neg_mul, one_div] using hL (n : ℝ) (Nat.cast_nonneg n)

end
end Sigma
