import SigmaSteinCutoff

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The energy inequality used to bootstrap moments has no tail assumptions. -/
theorem stein_square_bound (A B L K : ℝ) (hK : 0 ≤ K) (hL : |L| ≤ K) :
    A^2 ≤ K^2*B^2-2*(A*B*L-A^2) := by
  have hsq : L^2 ≤ K^2 := by
    have hll := (abs_le.mp hL).1
    have hlu := (abs_le.mp hL).2
    nlinarith [mul_nonneg (show 0 ≤ K-L by linarith) (show 0 ≤ K+L by linarith)]
  nlinarith [sq_nonneg (A-B*L),mul_nonneg (sq_nonneg B) (sub_nonneg.mpr hsq)]

theorem stein_even_cutoff_bound (n : ℕ) (R t K : ℝ) (hK : 0 ≤ K)
    (hd : |steinCutoffSlope R t| ≤ K) :
    t^(2*(n+1))*(steinCutoff R t)^2 ≤ (2*(n : ℝ)+3+2*K)^2*t^(2*n)-
      2*(t*deriv (steinPolynomialTest (2*n+1) R) t+(2-t)*steinPolynomialTest (2*n+1) R t) := by
  let c := steinCutoff R t
  let d := steinCutoffSlope R t
  let L := (2*(n : ℝ)+3)*c+2*d
  have hc := steinCutoff_bounds R t
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hco : 0 ≤ 2*(n : ℝ)+3 := by positivity
  have hL : |L| ≤ 2*(n : ℝ)+3+2*K := by
    calc
      |L| ≤ |(2*(n : ℝ)+3)*c|+|2*d| := abs_add_le _ _
      _ = (2*(n : ℝ)+3)*c+2*|d| := by
        rw [abs_mul,abs_of_nonneg hco,abs_of_nonneg hc.1,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
      _ ≤ (2*(n : ℝ)+3)+2*K := add_le_add
        (mul_le_of_le_one_right hco hc.2) (mul_le_mul_of_nonneg_left hd (by norm_num))
  have hh := stein_square_bound (t^(n+1)*c) (t^n) L (2*(n : ℝ)+3+2*K)
    (by positivity) hL
  have hev : t^(2*n) = (t^n)^2 := by rw [Nat.mul_comm 2 n,pow_mul]
  have hnxt : t^(2*(n+1)) = (t^(n+1))^2 := by rw [Nat.mul_comm 2 (n+1),pow_mul]
  have hodd : t^(2*n+1) = t^(n+1)*t^n := by rw [pow_add,hev,pow_one,pow_succ]; ring
  rw [steinPolynomialTest_expression]
  rw [show 2*n+1+1=2*(n+1) by omega,hev,hnxt,hodd]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  change _ ≤ _-2*(((2*(n : ℝ)+1)+2)*(t^(n+1)*t^n)*c^2-
    (t^(n+1))^2*c^2+2*(t^(n+1)*t^n)*c*d)
  dsimp [L] at hh
  nlinarith only [hh]

theorem weak_stein_next_even_moment (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hw : WeakGammaStein μ) (n : ℕ) (hi : Integrable (fun t : ℝ => t^(2*n)) μ) :
    Integrable (fun t : ℝ => t^(2*(n+1))) μ := by
  obtain ⟨K,hK,hbd⟩ := steinCutoffSlope_uniform_bound
  let M := (2*(n : ℝ)+3+2*K)^2*(∫ t : ℝ, t^(2*n) ∂μ)
  have hcutbound : ∀ R > 0,
      (∫ t : ℝ, t^(2*(n+1))*(steinCutoff R t)^2 ∂μ) ≤ M := by
    intro R hR
    have hicut : Integrable (fun t : ℝ => t^(2*(n+1))*(steinCutoff R t)^2) μ :=
      (steinPolynomialTest_contDiff (2*(n+1)) R).continuous.integrable_of_hasCompactSupport
        (steinPolynomialTest_hasCompactSupport _ hR)
    have hitest := stein_test_integrable μ (steinPolynomialTest (2*n+1) R)
      (steinPolynomialTest_contDiff _ R) (steinPolynomialTest_hasCompactSupport _ hR)
    have hh := integral_mono hicut ((hi.const_mul ((2*(n : ℝ)+3+2*K)^2)).sub (hitest.const_mul 2))
      (fun t => stein_even_cutoff_bound n R t K hK.le (hbd R t))
    simp only [Pi.sub_apply] at hh
    rw [integral_sub (hi.const_mul _) (hitest.const_mul _),integral_mul_left,integral_mul_left,
      hw _ (steinPolynomialTest_contDiff _ R) (steinPolynomialTest_hasCompactSupport _ hR)] at hh
    simpa [M] using hh
  apply (aecover_Icc (μ := μ) tendsto_neg_atTop_atBot tendsto_id).integrable_of_integral_bounded_of_nonneg_ae M
  · intro R
    exact (continuous_id.pow (2*(n+1))).continuousOn.integrableOn_compact isCompact_Icc
  · filter_upwards with t
    rw [Nat.mul_comm 2 (n+1),pow_mul]
    exact sq_nonneg _
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have he : (∫ t : ℝ in Icc (-R) R, t^(2*(n+1)) ∂μ) =
        ∫ t : ℝ in Icc (-R) R, t^(2*(n+1))*(steinCutoff R t)^2 ∂μ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      dsimp only
      rw [steinCutoff_one hR (abs_le.mpr ht),one_pow,mul_one]
    change (∫ t : ℝ in Icc (-R) R, t^(2*(n+1)) ∂μ) ≤ M
    rw [he]
    apply le_trans _ (hcutbound R hR)
    apply setIntegral_le_integral
    · exact (steinPolynomialTest_contDiff (2*(n+1)) R).continuous.integrable_of_hasCompactSupport
        (steinPolynomialTest_hasCompactSupport _ hR)
    · filter_upwards with t
      rw [Nat.mul_comm 2 (n+1),pow_mul]
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem weak_stein_even_moments_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hw : WeakGammaStein μ) : ∀ n : ℕ, Integrable (fun t : ℝ => t^(2*n)) μ := by
  intro n
  induction n with
  | zero => simpa using (integrable_const (1 : ℝ))
  | succ n ih => exact weak_stein_next_even_moment μ hw n ih

end
end Sigma
