import SigmaRadialOUBrownian
import SigmaProbGaussianEntropy
import Mathlib.Probability.Variance
import Mathlib.Probability.IdentDistrib

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped BigOperators

theorem gaussian_kernel_fourth_moment (b : ℝ) (hb : 0 < b) :
    (∫ t : ℝ, t ^ 4 * Real.exp (-b * t ^ 2)) =
      (3 / (2 * b)) * (∫ t : ℝ, t ^ 2 * Real.exp (-b * t ^ 2)) := by
  have h₂ : Integrable (fun t : ℝ => t ^ 2 * Real.exp (-b * t ^ 2)) := by
    simpa only [Real.rpow_two] using integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 2)
  have h₃ : Integrable (fun t : ℝ => t ^ 3 * Real.exp (-b * t ^ 2)) := by
    simpa only [Real.rpow_natCast] using
      integrable_rpow_mul_exp_neg_mul_sq (s := (3 : ℕ)) hb (by norm_num)
  have h₄ : Integrable (fun t : ℝ => t ^ 4 * Real.exp (-b * t ^ 2)) := by
    simpa only [Real.rpow_natCast] using
      integrable_rpow_mul_exp_neg_mul_sq (s := (4 : ℕ)) hb (by norm_num)
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => t ^ 3 * Real.exp (-b * t ^ 2))
      (3 * (t ^ 2 * Real.exp (-b * t ^ 2)) -
        (2 * b) * (t ^ 4 * Real.exp (-b * t ^ 2))) t := by
    convert ((hasDerivAt_id t).pow 3).mul
      ((((hasDerivAt_id t).pow 2).const_mul (-b)).exp) using 1 <;>
      simp only [id_eq] <;> ring
  have hi := integral_eq_zero_of_hasDerivAt_of_integrable hd
    ((h₂.const_mul 3).sub (h₄.const_mul (2 * b))) h₃
  rw [integral_sub (h₂.const_mul 3) (h₄.const_mul (2 * b)),
    integral_mul_left, integral_mul_left] at hi
  have hn : 2 * b ≠ 0 := by positivity
  apply mul_left_cancel₀ hn
  rw [← mul_assoc, mul_div_cancel₀ 3 hn]
  linarith

theorem gaussian_zero_fourth_moment (v : ℝ≥0) (hv : 0 < v) :
    (∫ t : ℝ, t ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  let b : ℝ := 1 / (2 * (v : ℝ))
  let K : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  have hb : 0 < b := by dsimp [b]; positivity
  have he : gaussianPDFReal 0 v = (fun t : ℝ => K * Real.exp (-b * t ^ 2)) := by
    funext t
    simp only [gaussianPDFReal, sub_zero, K, b]
    congr 2
    ring
  have hmoment (n : ℕ) :
      (∫ t : ℝ, t ^ n ∂gaussianReal 0 v) =
        K * (∫ t : ℝ, t ^ n * Real.exp (-b * t ^ 2)) := by
    rw [gaussian_integral v hv, he, ← integral_mul_left]
    congr 1
    funext t
    ring
  have hs := gaussian_zero_second_moment v hv
  rw [hmoment 2] at hs
  have hr : 3 / (2 * b) = 3 * (v : ℝ) := by
    dsimp [b]
    field_simp
    ring
  rw [hmoment 4, gaussian_kernel_fourth_moment b hb, hr]
  calc
    K * (3 * (v : ℝ) * (∫ t : ℝ, t ^ 2 * Real.exp (-b * t ^ 2))) =
      3 * (v : ℝ) * (K * (∫ t : ℝ, t ^ 2 * Real.exp (-b * t ^ 2))) := by ring
    _ = 3 * (v : ℝ) ^ 2 := by rw [hs]; ring

theorem gaussian_zero_fourth_integrable (v : ℝ≥0) (hv : 0 < v) :
    Integrable (fun t : ℝ => t ^ 4) (gaussianReal 0 v) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussian_zero_fourth_moment v hv]
  positivity

theorem gaussian_zero_square_memLp (v : ℝ≥0) :
    Memℒp (fun t : ℝ => t ^ 2) 2 (gaussianReal 0 v) := by
  by_cases hv : v = 0
  · subst v
    rw [gaussianReal_zero_var]
    apply (memℒp_two_iff_integrable_sq (by fun_prop)).mpr
    apply (integrable_const (0 : ℝ)).congr
    filter_upwards [ae_eq_dirac (fun t : ℝ => (t ^ 2) ^ 2)] with t ht
    simpa using ht.symm
  · apply (memℒp_two_iff_integrable_sq (by fun_prop)).mpr
    simpa only [← pow_mul] using gaussian_zero_fourth_integrable v (pos_iff_ne_zero.mpr hv)

theorem gaussian_zero_square_mean (v : ℝ≥0) :
    (∫ t : ℝ, t ^ 2 ∂gaussianReal 0 v) = (v : ℝ) := by
  by_cases hv : v = 0
  · subst v
    simp [gaussianReal_zero_var]
  · exact gaussian_zero_second_moment v (pos_iff_ne_zero.mpr hv)

theorem gaussian_zero_square_variance (v : ℝ≥0) :
    variance (fun t : ℝ => t ^ 2) (gaussianReal 0 v) = 2 * (v : ℝ) ^ 2 := by
  by_cases hv : v = 0
  · subst v
    simp [gaussianReal_zero_var, variance, evariance, lintegral_dirac]
  · rw [variance_def' (gaussian_zero_square_memLp v)]
    simp only [Pi.pow_apply, ← pow_mul]
    rw [gaussian_zero_fourth_moment v (pos_iff_ne_zero.mpr hv), gaussian_zero_square_mean]
    ring

/-- The squared Gaussian norm has finite second moment, including zero
variance. This transports the integral calculation to an actual random
variable on any supplied probability space. -/
theorem gaussian_square_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : Measurable X) (v : ℝ≥0)
    (hlaw : P.map X = gaussianReal 0 v) :
    IdentDistrib (fun ω => X ω ^ 2) (fun t : ℝ => t ^ 2) P (gaussianReal 0 v) := by
  have h : IdentDistrib X (fun t : ℝ => t) P (gaussianReal 0 v) :=
    ⟨hX.aemeasurable, measurable_id.aemeasurable, by simpa using hlaw⟩
  exact h.sq

/-- Exact variance of a finite sum of squared independent Gaussian
increments. In the Brownian application the variances are the actual time
steps, so this is the quantitative quadratic-variation estimate. -/
theorem gaussian_square_sum_variance {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → ℝ) (v : ι → ℝ≥0)
    (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i))
    (hindep : Pairwise (fun i j => IndepFun (X i) (X j) P)) :
    variance (fun ω => ∑ i, X i ω ^ 2) P = ∑ i, 2 * (v i : ℝ) ^ 2 := by
  classical
  have hm (i : ι) : Memℒp (fun ω => X i ω ^ 2) 2 P :=
    (gaussian_square_identDistrib (hX i) (v i) (hlaw i)).symm.memℒp_snd
      (gaussian_zero_square_memLp (v i))
  have hi (i j : ι) (hij : i ≠ j) :
      IndepFun (fun ω => X i ω ^ 2) (fun ω => X j ω ^ 2) P :=
    (hindep hij).comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have he := IndepFun.variance_sum (s := Finset.univ) (fun i _ => hm i)
    (fun i _ j _ hij => hi i j hij)
  simp only [Finset.sum_fn] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  rw [(gaussian_square_identDistrib (hX i) (v i) (hlaw i)).variance_eq,
    gaussian_zero_square_variance]

theorem gaussian_square_sum_mean {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → ℝ) (v : ι → ℝ≥0)
    (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i)) :
    (∫ ω, ∑ i, X i ω ^ 2 ∂P) = ∑ i, (v i : ℝ) := by
  have hm (i : ι) : Memℒp (fun ω => X i ω ^ 2) 2 P :=
    (gaussian_square_identDistrib (hX i) (v i) (hlaw i)).symm.memℒp_snd
      (gaussian_zero_square_memLp (v i))
  rw [integral_finset_sum _ (fun i _ => (hm i).integrable (by norm_num))]
  apply Finset.sum_congr rfl
  intro i _
  rw [(gaussian_square_identDistrib (hX i) (v i) (hlaw i)).integral_eq,
    gaussian_zero_square_mean]

theorem gaussian_square_sum_centered_second_moment {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → ℝ) (v : ι → ℝ≥0)
    (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i))
    (hindep : Pairwise (fun i j => IndepFun (X i) (X j) P)) :
    (∫ ω, ((∑ i, X i ω ^ 2) - ∑ i, (v i : ℝ)) ^ 2 ∂P) =
      ∑ i, 2 * (v i : ℝ) ^ 2 := by
  have hm : Memℒp (fun ω => ∑ i, X i ω ^ 2) 2 P :=
    memℒp_finset_sum _ (fun i _ =>
      (gaussian_square_identDistrib (hX i) (v i) (hlaw i)).symm.memℒp_snd
        (gaussian_zero_square_memLp (v i)))
  have he := hm.variance_eq
  rw [gaussian_square_sum_mean P X v hX hlaw,
    gaussian_square_sum_variance P X v hX hlaw hindep] at he
  exact he.symm

end
end Sigma
