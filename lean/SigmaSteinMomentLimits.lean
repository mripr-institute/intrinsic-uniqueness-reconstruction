import SigmaSteinMomentBounds
import SigmaOpMomentInverse

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem weak_stein_moments_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hw : WeakGammaStein μ) (k : ℕ) : Integrable (fun t : ℝ => t^k) μ := by
  apply ((integrable_const (1 : ℝ)).add (weak_stein_even_moments_integrable μ hw k)).mono'
  · exact (continuous_id.pow k).aestronglyMeasurable
  · filter_upwards with t
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [Nat.mul_comm 2 k,pow_mul]
    nlinarith [sq_nonneg (|t^k|-1),sq_abs (t^k)]

theorem steinCutoff_tendsto (t : ℝ) : Tendsto (fun R : ℝ => steinCutoff R t) atTop (𝓝 1) := by
  have hr : Tendsto (fun R : ℝ => t/R) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.const_mul t :
      Tendsto (fun R : ℝ => t*R⁻¹) atTop (𝓝 (t*0)))
  have h0 : (steinBump : ℝ → ℝ) 0 = 1 := by
    apply steinBump.one_of_mem_closedBall
    norm_num [steinBump,Metric.mem_closedBall,Real.dist_eq]
  simpa only [steinCutoff,h0] using steinBump.continuous.continuousAt.tendsto.comp hr

theorem steinCutoffSlope_tendsto (t : ℝ) :
    Tendsto (fun R : ℝ => steinCutoffSlope R t) atTop (𝓝 0) := by
  have hr : Tendsto (fun R : ℝ => t/R) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.const_mul t :
      Tendsto (fun R : ℝ => t*R⁻¹) atTop (𝓝 (t*0)))
  have hc := ((steinBump.contDiff : ContDiff ℝ ∞ (steinBump : ℝ → ℝ)).continuous_deriv (by simp)).continuousAt.tendsto.comp hr
  simpa only [steinCutoffSlope,zero_mul] using hr.mul hc

theorem steinPolynomialTest_tendsto (k : ℕ) (t : ℝ) :
    Tendsto (fun R : ℝ => t*deriv (steinPolynomialTest k R) t+(2-t)*steinPolynomialTest k R t)
      atTop (𝓝 (((k : ℝ)+2)*t^k-t^(k+1))) := by
  simp_rw [steinPolynomialTest_expression]
  have hc := steinCutoff_tendsto t
  have hd := steinCutoffSlope_tendsto t
  have hh := ((hc.pow 2).const_mul (((k : ℝ)+2)*t^k)).sub
    ((hc.pow 2).const_mul (t^(k+1)))
  simpa only [one_pow,mul_one,mul_zero,add_zero] using hh.add ((hc.const_mul (2*t^k)).mul hd)

theorem steinPolynomialTest_uniform_bound (k : ℕ) (R t K : ℝ)
    (hK : 0 ≤ K) (hd : |steinCutoffSlope R t| ≤ K) :
    ‖t*deriv (steinPolynomialTest k R) t+(2-t)*steinPolynomialTest k R t‖ ≤
      ((k : ℝ)+2+2*K)*|t^k|+|t^(k+1)| := by
  rw [steinPolynomialTest_expression,Real.norm_eq_abs]
  have hc := steinCutoff_bounds R t
  have hcs : (steinCutoff R t)^2 ≤ 1 := by nlinarith
  have hnn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc
    _ ≤ |((k : ℝ)+2)*t^k*(steinCutoff R t)^2|+
        |t^(k+1)*(steinCutoff R t)^2|+|2*t^k*steinCutoff R t*steinCutoffSlope R t| :=
      le_trans (abs_add_le _ _) (add_le_add_right (abs_sub _ _) _)
    _ = ((k : ℝ)+2)*|t^k| *(steinCutoff R t)^2+
        |t^(k+1)| *(steinCutoff R t)^2+2*|t^k| *steinCutoff R t*|steinCutoffSlope R t| := by
      simp only [abs_mul,abs_pow,abs_of_nonneg hc.1,abs_of_nonneg (by positivity : 0 ≤ (k : ℝ)+2),
        abs_of_pos (by norm_num : (0 : ℝ)<2)]
    _ ≤ ((k : ℝ)+2)*|t^k|+|t^(k+1)|+2*|t^k| *K := by
      apply add_le_add
      · exact add_le_add (mul_le_of_le_one_right (by positivity) hcs)
          (mul_le_of_le_one_right (abs_nonneg _) hcs)
      · exact le_trans (mul_le_mul_of_nonneg_left hd (mul_nonneg (by positivity) hc.1))
          (by nlinarith [mul_nonneg (show 0 ≤ 2*|t^k| *K by positivity) (show 0 ≤ 1-steinCutoff R t by linarith)])
    _ = _ := by ring

theorem weak_stein_moment_recurrence (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hw : WeakGammaStein μ) (k : ℕ) :
    (∫ t : ℝ, t^(k+1) ∂μ) = ((k : ℝ)+2)*(∫ t : ℝ, t^k ∂μ) := by
  obtain ⟨K,hK,hbd⟩ := steinCutoffSlope_uniform_bound
  let B := fun t : ℝ => ((k : ℝ)+2+2*K)*|t^k|+|t^(k+1)|
  have hIB : Integrable B μ :=
    ((weak_stein_moments_integrable μ hw k).abs.const_mul _).add
      (weak_stein_moments_integrable μ hw (k+1)).abs
  have hlim := tendsto_integral_filter_of_dominated_convergence B
    (F := fun R t : ℝ => t*deriv (steinPolynomialTest k R) t+(2-t)*steinPolynomialTest k R t)
    (f := fun t : ℝ => ((k : ℝ)+2)*t^k-t^(k+1))
    (Eventually.of_forall (fun R => by
      have hc := steinPolynomialTest_contDiff k R
      exact (continuous_id.mul (hc.continuous_deriv (by simp)) |>.add
        ((continuous_const.sub continuous_id).mul hc.continuous)).aestronglyMeasurable))
    (Eventually.of_forall (fun R => Eventually.of_forall (fun t =>
      steinPolynomialTest_uniform_bound k R t K hK.le (hbd R t)))) hIB
    (Eventually.of_forall (steinPolynomialTest_tendsto k))
  have hz : Tendsto (fun R : ℝ => ∫ t : ℝ,
      t*deriv (steinPolynomialTest k R) t+(2-t)*steinPolynomialTest k R t ∂μ) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact (hw _ (steinPolynomialTest_contDiff k R) (steinPolynomialTest_hasCompactSupport k hR)).symm
  have he := tendsto_nhds_unique hlim hz
  rw [integral_sub ((weak_stein_moments_integrable μ hw k).const_mul _)
    (weak_stein_moments_integrable μ hw (k+1)),integral_mul_left] at he
  linarith

theorem weak_stein_factorial_moments (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hw : WeakGammaStein μ) : OpFactorialMoments μ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    change (∫ t : ℝ, t^(n+1) ∂μ) = (((n+1)+1).factorial : ℝ)
    rw [weak_stein_moment_recurrence μ hw n,ih,Nat.factorial_succ (n+1)]
    push_cast
    ring

/-- The full real-line compact-test characterization, with no assumed support or moments. -/
theorem weak_stein_characterization (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    WeakGammaStein μ ↔ μ = gammaProbability := by
  constructor
  · intro hw
    exact operator_full_line_factorial_moment_unique μ (weak_stein_factorial_moments μ hw)
  · exact weak_stein_of_eq_gamma μ

end
end Sigma
