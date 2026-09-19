import SigmaSelfConcordance
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.FundThmCalculus

namespace Sigma
noncomputable section
open Filter Set MeasureTheory
open scoped Topology

theorem sc_intrinsic_deriv {t : ℝ} (ht : 0 < t) : deriv I t = 1 - 1 / t :=
  (SigmaBase.potential_hasDerivAt ht).deriv

theorem sc_intrinsic_second_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deriv I) (1 / t ^ (2 : ℕ)) t := by
  have hd : HasDerivAt (fun x : ℝ => 1 - 1 / x) (1 / t ^ (2 : ℕ)) t := by
    convert (reciprocal_hasDerivAt ht).neg using 1
    · funext x
      ring
    · ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
  exact sc_intrinsic_deriv hx

theorem sc_intrinsic_curvature {t : ℝ} (ht : 0 < t) :
    scCurvature I t = 1 / t ^ (2 : ℕ) := (sc_intrinsic_second_hasDerivAt ht).deriv

theorem sc_intrinsic_third_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (scCurvature I) (-2 / t ^ (3 : ℕ)) t := by
  have hd := (hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id t).pow 2)
    (pow_ne_zero _ (ne_of_gt ht))
  have hh : HasDerivAt (fun x : ℝ => 1 / x ^ (2 : ℕ)) (-2 / t ^ (3 : ℕ)) t := by
    convert hd using 1
    field_simp
    ring
  apply hh.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
  exact sc_intrinsic_curvature hx

theorem sc_intrinsic_third_derivative {t : ℝ} (ht : 0 < t) :
    scThirdDerivative I t = -2 / t ^ (3 : ℕ) :=
  (sc_intrinsic_third_hasDerivAt ht).deriv

theorem sc_intrinsic_hessian_sqrt {t : ℝ} (ht : 0 < t) :
    Real.sqrt (scCurvature I t) = 1 / t := by
  rw [sc_intrinsic_curvature ht, Real.sqrt_div (by norm_num), Real.sqrt_one,
    Real.sqrt_sq ht.le]

theorem sc_intrinsic_signed_equality {t : ℝ} (ht : 0 < t) :
    scThirdDerivative I t = -2 * (scCurvature I t) ^ (3 / 2 : ℝ) := by
  have hp : 0 ≤ scCurvature I t := by rw [sc_intrinsic_curvature ht]; positivity
  rw [sc_intrinsic_third_derivative ht, sc_rpow_three_halves hp,
    sc_intrinsic_hessian_sqrt ht]
  ring

theorem sc_intrinsic_C3 : ContDiffOn ℝ 3 I (Ioi 0) := by
  exact (contDiffOn_id.sub contDiffOn_const).sub
    (contDiffOn_id.log (fun t ht => ne_of_gt ht))

theorem sc_intrinsic_calibration :
    I 1 = 0 ∧ deriv I 1 = 0 ∧ scCurvature I 1 = 1 ∧
      ∀ t > 0, 0 < scCurvature I t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [I, SigmaBase.potential]
  · rw [sc_intrinsic_deriv (by norm_num)]
    norm_num
  · rw [sc_intrinsic_curvature (by norm_num)]
    norm_num
  · intro t ht
    rw [sc_intrinsic_curvature ht]
    positivity

/-- Euclidean speed in logarithmic coordinates is the actual Hessian speed. -/
theorem sc_hessian_speed {t v : ℝ} (ht : 0 < t) :
    Real.sqrt (scCurvature I t) * |v| = |v / t| := by
  rw [sc_intrinsic_hessian_sqrt ht, abs_div, abs_of_pos ht]
  ring

def scPathLength (g : ℝ → ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, |deriv g u / g u|

/-- A lower bound for every positive differentiable path with integrable
logarithmic velocity. The length is a genuine interval integral. -/
theorem sc_positive_path_length_lower_bound (g : ℝ → ℝ)
    (hp : ∀ u ∈ Icc (0 : ℝ) 1, 0 < g u)
    (hd : ∀ u ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ g u)
    (hi : IntervalIntegrable (fun u => deriv g u / g u) volume 0 1) :
    |Real.log (g 1) - Real.log (g 0)| ≤ scPathLength g := by
  have hlog : ∀ u ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun u => Real.log (g u)) (deriv g u / g u) u := by
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := by simpa using hu
    exact (hd u hu').hasDerivAt.log (ne_of_gt (hp u hu'))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hlog hi
  have hb := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun u => deriv g u / g u) (show (0 : ℝ) ≤ 1 by norm_num)
  rw [he] at hb
  simpa only [Real.norm_eq_abs, scPathLength] using hb

def scLogSegment (s t u : ℝ) : ℝ :=
  Real.exp ((1 - u) * Real.log s + u * Real.log t)

theorem scLogSegment_positive (s t u : ℝ) : 0 < scLogSegment s t u := Real.exp_pos _

theorem scLogSegment_endpoints {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    scLogSegment s t 0 = s ∧ scLogSegment s t 1 = t := by
  simp [scLogSegment, Real.exp_log hs, Real.exp_log ht]

theorem scLogSegment_hasDerivAt (s t u : ℝ) :
    HasDerivAt (scLogSegment s t)
      ((Real.log t - Real.log s) * scLogSegment s t u) u := by
  have hd := ((((hasDerivAt_id u).const_sub 1).mul_const (Real.log s)).add
    ((hasDerivAt_id u).mul_const (Real.log t))).exp
  convert hd using 1
  simp only [scLogSegment, id_eq]
  ring

theorem scLogSegment_log_velocity (s t u : ℝ) :
    deriv (scLogSegment s t) u / scLogSegment s t u = Real.log t - Real.log s := by
  rw [(scLogSegment_hasDerivAt s t u).deriv]
  exact mul_div_cancel_right₀ _ (ne_of_gt (scLogSegment_positive s t u))

theorem scLogSegment_length (s t : ℝ) :
    scPathLength (scLogSegment s t) = |Real.log t - Real.log s| := by
  unfold scPathLength
  simp_rw [scLogSegment_log_velocity]
  simp

/-- This set consists of actual positive-path lengths, not assumed distances. -/
def scPositivePathLengths (s t : ℝ) : Set ℝ :=
  {L | ∃ g : ℝ → ℝ,
    (∀ u ∈ Icc (0 : ℝ) 1, 0 < g u) ∧
    (∀ u ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ g u) ∧
    IntervalIntegrable (fun u => deriv g u / g u) volume 0 1 ∧
    g 0 = s ∧ g 1 = t ∧ L = scPathLength g}

theorem sc_hessian_path_distance {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    IsLeast (scPositivePathLengths s t) |Real.log (t / s)| := by
  have he : Real.log (t / s) = Real.log t - Real.log s :=
    Real.log_div (ne_of_gt ht) (ne_of_gt hs)
  constructor
  · refine ⟨scLogSegment s t, (fun u _ => scLogSegment_positive s t u),
      (fun u _ => (scLogSegment_hasDerivAt s t u).differentiableAt), ?_,
      (scLogSegment_endpoints hs ht).1, (scLogSegment_endpoints hs ht).2, ?_⟩
    · simp_rw [scLogSegment_log_velocity]
      exact intervalIntegrable_const
    · rw [scLogSegment_length, he]
  · rintro L ⟨g,hp,hd,hi,h0,h1,rfl⟩
    have hb := sc_positive_path_length_lower_bound g hp hd hi
    simpa only [h0, h1, he] using hb

/-- The path integral above is exactly the length for the intrinsic Hessian. -/
theorem scPathLength_eq_hessian_length (g : ℝ → ℝ)
    (hp : ∀ u ∈ Icc (0 : ℝ) 1, 0 < g u) :
    scPathLength g = ∫ u in (0 : ℝ)..1,
      Real.sqrt (scCurvature I (g u)) * |deriv g u| := by
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc (0 : ℝ) 1 := by simpa using hu
  exact (sc_hessian_speed (v := deriv g u) (hp u hu')).symm

abbrev scPositiveRay := Ioi (0 : ℝ)

/-- A native metric transported by the injective logarithmic coordinate. -/
def scHessianMetric : MetricSpace scPositiveRay :=
  MetricSpace.induced (fun t : scPositiveRay => Real.log (t : ℝ))
    (by
      intro s t he
      apply Subtype.ext
      exact Real.log_injOn_pos s.property t.property he) inferInstance

theorem sc_native_metric_distance (s t : scPositiveRay) :
    @dist scPositiveRay scHessianMetric.toDist s t =
      |Real.log ((t : ℝ) / (s : ℝ))| := by
  change |Real.log (s : ℝ) - Real.log (t : ℝ)| = _
  rw [Real.log_div (ne_of_gt t.property) (ne_of_gt s.property)]
  exact abs_sub_comm _ _

/-- The native metric distance is the attained infimum of actual Hessian lengths. -/
theorem sc_native_hessian_path_distance (s t : scPositiveRay) :
    IsLeast (scPositivePathLengths (s : ℝ) (t : ℝ))
      (@dist scPositiveRay scHessianMetric.toDist s t) := by
  rw [sc_native_metric_distance]
  exact sc_hessian_path_distance s.property t.property

theorem sc_inversion_reverses_order {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    1 / t < 1 / s := one_div_lt_one_div_of_lt hs hst

theorem sc_distance_inversion {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    |Real.log ((1 / t) / (1 / s))| = |Real.log (t / s)| := by
  have he : (1 / t) / (1 / s) = s / t := by field_simp
  rw [he, Real.log_div (ne_of_gt hs) (ne_of_gt ht),
    Real.log_div (ne_of_gt ht) (ne_of_gt hs)]
  exact abs_sub_comm _ _

theorem sc_symmetrization_distance {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    I (t / s) + I (s / t) =
      4 * Real.sinh (|Real.log (t / s)| / 2) ^ (2 : ℕ) := by
  have hratio : 0 < t / s := div_pos ht hs
  have hsum : I (t / s) + I (s / t) = t / s + s / t - 2 := by
    unfold I SigmaBase.potential
    rw [Real.log_div (ne_of_gt ht) (ne_of_gt hs),
      Real.log_div (ne_of_gt hs) (ne_of_gt ht)]
    ring
  have hc : 2 * Real.cosh (Real.log (t / s)) = t / s + s / t := by
    rw [Real.cosh_eq, Real.exp_log hratio, Real.exp_neg, Real.exp_log hratio, inv_div]
    ring
  have hh := Real.cosh_two_mul (|Real.log (t / s)| / 2)
  rw [show 2 * (|Real.log (t / s)| / 2) = |Real.log (t / s)| by ring,
    Real.cosh_abs, Real.cosh_sq] at hh
  rw [hsum]
  linarith

/-- The exact gradient/Hessian ratio rules out every finite barrier parameter. -/
theorem sc_gradient_hessian_ratio {t : ℝ} (ht : 0 < t) :
    (deriv I t) ^ (2 : ℕ) / scCurvature I t = (t - 1) ^ (2 : ℕ) := by
  rw [sc_intrinsic_deriv ht, sc_intrinsic_curvature ht]
  field_simp

theorem sc_no_finite_barrier_parameter :
    ¬ ∃ ν : ℝ, ∀ t > 0, (deriv I t) ^ (2 : ℕ) ≤ ν * scCurvature I t := by
  rintro ⟨ν,hν⟩
  have hn := hν 1 (by norm_num)
  rw [sc_intrinsic_deriv (by norm_num), sc_intrinsic_curvature (by norm_num)] at hn
  norm_num at hn
  have ht : 0 < ν + 2 := by linarith
  have hp : 0 < scCurvature I (ν + 2) := by rw [sc_intrinsic_curvature ht]; positivity
  have hb := (div_le_iff₀ hp).mpr (hν (ν + 2) ht)
  rw [sc_gradient_hessian_ratio ht] at hb
  nlinarith [sq_nonneg ν]

def scQuadratic (t : ℝ) : ℝ := (t - 1) ^ (2 : ℕ) / 2

theorem scQuadratic_hasDerivAt (t : ℝ) : HasDerivAt scQuadratic (t - 1) t := by
  convert (((hasDerivAt_id t).sub_const 1).pow 2).div_const 2 using 1
  simp only [id_eq]
  ring

theorem scQuadratic_deriv : deriv scQuadratic = fun t => t - 1 := by
  funext t
  exact (scQuadratic_hasDerivAt t).deriv

theorem scQuadratic_second_derivative : scCurvature scQuadratic = fun _ => 1 := by
  funext t
  rw [scCurvature, scQuadratic_deriv]
  exact ((hasDerivAt_id t).sub_const 1).deriv

theorem scQuadratic_third_derivative : scThirdDerivative scQuadratic = fun _ => 0 := by
  funext t
  rw [scThirdDerivative, scQuadratic_second_derivative]
  exact (hasDerivAt_const t (1 : ℝ)).deriv

theorem scQuadratic_calibrated_inequality :
    ContDiffOn ℝ 3 scQuadratic (Ioi 0) ∧
    scQuadratic 1 = 0 ∧ deriv scQuadratic 1 = 0 ∧ scCurvature scQuadratic 1 = 1 ∧
    (∀ t > 0, 0 < scCurvature scQuadratic t) ∧
    (∀ t > 0, |scThirdDerivative scQuadratic t| ≤
      2 * (scCurvature scQuadratic t) ^ (3 / 2 : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((contDiffOn_id.sub contDiffOn_const).pow 2).div_const 2
  · norm_num [scQuadratic]
  · simp [scQuadratic_deriv]
  · simp [scQuadratic_second_derivative]
  · intro t ht
    simp [scQuadratic_second_derivative]
  · intro t ht
    simp [scQuadratic_second_derivative, scQuadratic_third_derivative]

theorem scQuadratic_not_intrinsic : ¬ ∀ t > 0, scQuadratic t = I t := by
  intro he
  have h1 : ∀ t > 0, deriv scQuadratic t = deriv I t := by
    intro t ht
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    exact he x hx
  have h2 : scCurvature scQuadratic 2 = scCurvature I 2 := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioi.mem_nhds (show (0 : ℝ) < 2 by norm_num)] with x hx
    exact h1 x hx
  rw [scQuadratic_second_derivative, sc_intrinsic_curvature (by norm_num)] at h2
  norm_num at h2

end
end Sigma
