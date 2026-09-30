import SigmaRadialBrownianProduct
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology

theorem real_eLpNorm_two_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : Ω → ℝ} (hf : Memℒp f 2 P) :
    eLpNorm f 2 P = (ENNReal.ofReal (∫ ω, f ω ^ 2 ∂P)) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_nnnorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  norm_num only [ENNReal.toReal_ofNat]
  congr 1
  rw [ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
    (Eventually.of_forall (fun ω => sq_nonneg (f ω)))]
  apply lintegral_congr_ae
  filter_upwards with ω
  rw [← ofReal_norm_eq_coe_nnnorm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f ω)) (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_two, Real.norm_eq_abs, sq_abs]

theorem tendstoInMeasure_of_mean_square {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) P) (hg : AEStronglyMeasurable g P)
    (hm : ∀ n, Memℒp (fun ω => f n ω - g ω) 2 P)
    (he : Tendsto (fun n => ∫ ω, (f n ω - g ω) ^ 2 ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P f atTop g := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hf hg
  have ht := (ENNReal.continuous_ofReal.tendsto 0).comp he
  have hr := ht.ennrpow_const (1 / 2 : ℝ)
  change Tendsto (fun n => eLpNorm (fun ω => f n ω - g ω) 2 P) atTop (𝓝 0)
  simp_rw [real_eLpNorm_two_integral (hm _)]
  simpa only [Function.comp_apply, ENNReal.ofReal_zero,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hr

variable {Ω : Type*} [MeasurableSpace Ω] {D : ℕ} {P : Measure Ω}
  {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D)}

theorem radial_brownian_increment_norm_square_identDistrib
    (hB : IsRadialBrownian D P B) (s t : ℝ≥0) (hst : s ≤ t) :
    IdentDistrib (fun ω => ‖B t ω - B s ω‖ ^ 2)
      (fun z : EuclideanSpace ℝ (Fin D) => ‖z‖ ^ 2)
      P (radialBrownianGaussian D (t-s)) := by
  have h : IdentDistrib (fun ω => B t ω - B s ω)
      (fun z : EuclideanSpace ℝ (Fin D) => z) P (radialBrownianGaussian D (t-s)) :=
    ⟨((hB.measurable t).sub (hB.measurable s)).aemeasurable,
      measurable_id.aemeasurable, by simpa using hB.increment_law s t hst⟩
  exact h.comp (measurable_norm.pow_const 2)

/-- The literal sum of squared native vector increments on a finite time
partition. No bracket or quadratic-variation value is assumed. -/
def radialBrownianQuadraticSum (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D))
    {n : ℕ} (t : Fin (n+1) → ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i : Fin n, ‖B (t i.succ) ω - B (t i.castSucc) ω‖ ^ 2

theorem radial_brownian_quadratic_sum_memLp (hB : IsRadialBrownian D P B)
    {n : ℕ} (t : Fin (n+1) → ℝ≥0) (ht : Monotone t) :
    Memℒp (radialBrownianQuadraticSum B t) 2 P := by
  apply memℒp_finset_sum
  intro i _
  exact (radial_brownian_increment_norm_square_identDistrib hB _ _
    (ht (by exact Nat.le_succ i.val))).symm.memℒp_snd
      (radial_brownian_gaussian_norm_square_memLp D _)

theorem radial_brownian_quadratic_sum_mean (hB : IsRadialBrownian D P B)
    {n : ℕ} (t : Fin (n+1) → ℝ≥0) (ht : Monotone t) :
    (∫ ω, radialBrownianQuadraticSum B t ω ∂P) =
      (D : ℝ) * ∑ i : Fin n, ((t i.succ - t i.castSucc : ℝ≥0) : ℝ) := by
  letI := hB.probability
  have hd (i : Fin n) := radial_brownian_increment_norm_square_identDistrib hB
    (t i.castSucc) (t i.succ) (ht (by exact Nat.le_succ i.val))
  unfold radialBrownianQuadraticSum
  rw [integral_finset_sum _ (fun i _ =>
    ((hd i).symm.memℒp_snd (radial_brownian_gaussian_norm_square_memLp D _)).integrable
      (by norm_num)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [(hd i).integral_eq, radial_brownian_gaussian_norm_square_mean]

theorem radial_brownian_quadratic_sum_variance (hB : IsRadialBrownian D P B)
    {n : ℕ} (t : Fin (n+1) → ℝ≥0) (ht : Monotone t) :
    variance (radialBrownianQuadraticSum B t) P =
      2 * (D : ℝ) * ∑ i : Fin n, ((t i.succ - t i.castSucc : ℝ≥0) : ℝ) ^ 2 := by
  letI := hB.probability
  have hd (i : Fin n) := radial_brownian_increment_norm_square_identDistrib hB
    (t i.castSucc) (t i.succ) (ht (by exact Nat.le_succ i.val))
  have hm (i : Fin n) :=
    (hd i).symm.memℒp_snd (radial_brownian_gaussian_norm_square_memLp D _)
  have he := IndepFun.variance_sum (s := Finset.univ) (fun i _ => hm i)
    (fun i _ j _ hij => ((hB.independent_increments n t ht).indepFun hij).comp
      (measurable_norm.pow_const 2) (measurable_norm.pow_const 2))
  simp only [Finset.sum_fn] at he
  unfold radialBrownianQuadraticSum
  rw [he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [(hd i).variance_eq, radial_brownian_gaussian_norm_square_variance]

/-- Exact mean-square error on an arbitrary finite partition. Independence
of the actual Gaussian increments supplies every cross-term cancellation. -/
theorem radial_brownian_quadratic_sum_error (hB : IsRadialBrownian D P B)
    {n : ℕ} (t : Fin (n+1) → ℝ≥0) (ht : Monotone t) :
    (∫ ω, (radialBrownianQuadraticSum B t ω -
      (D : ℝ) * ∑ i : Fin n, ((t i.succ - t i.castSucc : ℝ≥0) : ℝ)) ^ 2 ∂P) =
      2 * (D : ℝ) * ∑ i : Fin n, ((t i.succ - t i.castSucc : ℝ≥0) : ℝ) ^ 2 := by
  letI := hB.probability
  have he := (radial_brownian_quadratic_sum_memLp hB t ht).variance_eq
  rw [radial_brownian_quadratic_sum_mean hB t ht,
    radial_brownian_quadratic_sum_variance hB t ht] at he
  exact he.symm

def radialBrownianUniformTimes (T : ℝ≥0) (n : ℕ) (i : Fin (n+1)) : ℝ≥0 :=
  T * (i.val : ℝ≥0) / n

theorem radial_brownian_uniform_times_monotone (T : ℝ≥0) (n : ℕ) :
    Monotone (radialBrownianUniformTimes T n) := by
  intro i j hij
  unfold radialBrownianUniformTimes
  gcongr
  exact_mod_cast hij

theorem radial_brownian_uniform_times_step (T : ℝ≥0) (n : ℕ) (i : Fin n) :
    radialBrownianUniformTimes T n i.succ - radialBrownianUniformTimes T n i.castSucc =
      T / n := by
  simp [radialBrownianUniformTimes, Nat.cast_add, mul_add, add_div]

theorem radial_brownian_uniform_quadratic_error (hB : IsRadialBrownian D P B)
    (T : ℝ≥0) (n : ℕ) (hn : 0 < n) :
    (∫ ω, (radialBrownianQuadraticSum B (radialBrownianUniformTimes T n) ω -
      (D : ℝ) * (T : ℝ)) ^ 2 ∂P) = 2 * (D : ℝ) * (T : ℝ) ^ 2 / n := by
  have he := radial_brownian_quadratic_sum_error hB (radialBrownianUniformTimes T n)
    (radial_brownian_uniform_times_monotone T n)
  simp only [radial_brownian_uniform_times_step, NNReal.coe_div, NNReal.coe_natCast,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at he
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcancel : (n : ℝ) * ((T : ℝ) / n) = (T : ℝ) := by field_simp
  rw [hcancel] at he
  rw [he]
  field_simp
  ring

theorem radial_brownian_quadratic_variation_mean_square (hB : IsRadialBrownian D P B)
    (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ ω,
      (radialBrownianQuadraticSum B (radialBrownianUniformTimes T n) ω -
        (D : ℝ) * (T : ℝ)) ^ 2 ∂P) atTop (𝓝 0) := by
  have he : (fun n : ℕ => ∫ ω,
      (radialBrownianQuadraticSum B (radialBrownianUniformTimes T n) ω -
        (D : ℝ) * (T : ℝ)) ^ 2 ∂P) =ᶠ[atTop]
      (fun n : ℕ => 2 * (D : ℝ) * (T : ℝ) ^ 2 / n) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact radial_brownian_uniform_quadratic_error hB T n hn
  apply Tendsto.congr' he.symm
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

theorem radial_brownian_quadratic_variation_in_probability (hB : IsRadialBrownian D P B)
    (T : ℝ≥0) :
    TendstoInMeasure P (fun n => radialBrownianQuadraticSum B (radialBrownianUniformTimes T n))
      atTop (fun _ => (D : ℝ) * (T : ℝ)) := by
  letI := hB.probability
  have hm (n : ℕ) := radial_brownian_quadratic_sum_memLp hB
    (radialBrownianUniformTimes T n) (radial_brownian_uniform_times_monotone T n)
  exact tendstoInMeasure_of_mean_square (fun n => (hm n).aestronglyMeasurable)
    aestronglyMeasurable_const (fun n => (hm n).sub (memℒp_const _))
    (radial_brownian_quadratic_variation_mean_square hB T)

end
end Sigma
