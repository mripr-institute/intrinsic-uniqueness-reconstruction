import SigmaRadialBrownianQuadraticVariation

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology InnerProductSpace

theorem finite_successive_difference_sum {n : ℕ} (f : Fin (n+1) → ℝ) :
    (∑ i : Fin n, (f i.succ - f i.castSucc)) = f (Fin.last n) - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have he := ih (fun i => f i.succ)
    simp only [Fin.succ_castSucc] at he
    rw [he]
    simp only [Fin.succ_last, Fin.castSucc_zero]
    ring

/-- The exact discrete identity behind the quadratic Itô formula. -/
theorem finite_inner_increment_sum {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {n : ℕ} (x : Fin (n+1) → V) :
    (∑ i : Fin n, ⟪x i.castSucc, x i.succ - x i.castSucc⟫_ℝ) =
      (‖x (Fin.last n)‖ ^ 2 - ‖x 0‖ ^ 2 -
        ∑ i : Fin n, ‖x i.succ - x i.castSucc‖ ^ 2) / 2 := by
  have hi (i : Fin n) : ⟪x i.castSucc, x i.succ - x i.castSucc⟫_ℝ =
      (‖x i.succ‖ ^ 2 - ‖x i.castSucc‖ ^ 2 - ‖x i.succ - x i.castSucc‖ ^ 2) / 2 := by
    rw [norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm (x i.succ) (x i.castSucc)]
    ring
  simp_rw [hi]
  rw [← Finset.sum_div, Finset.sum_sub_distrib,
    finite_successive_difference_sum (fun i => ‖x i‖ ^ 2)]

theorem tendstoInMeasure_sub_half {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (h : TendstoInMeasure P f atTop g) (a : Ω → ℝ) :
    TendstoInMeasure P (fun n ω => (a ω - f n ω) / 2) atTop
      (fun ω => (a ω - g ω) / 2) := by
  intro ε hε
  have he (n : ℕ) : {ω | ε ≤ dist ((a ω - f n ω) / 2) ((a ω - g ω) / 2)} =
      {ω | 2 * ε ≤ dist (f n ω) (g ω)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Real.dist_eq]
    have ha : (a ω - f n ω) / 2 - (a ω - g ω) / 2 = -(f n ω - g ω) / 2 := by ring
    rw [ha, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).trans (by rw [mul_comm])
  simp_rw [he]
  exact h (2 * ε) (by positivity)

variable {Ω : Type*} [MeasurableSpace Ω] {D : ℕ} {P : Measure Ω}
  {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D)}

def radialBrownianSelfSum (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D))
    {n : ℕ} (t : Fin (n+1) → ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i : Fin n, ⟪B (t i.castSucc) ω, B (t i.succ) ω - B (t i.castSucc) ω⟫_ℝ

/-- The stochastic integral of the Brownian position against its own
increments. Its definition is justified below by convergence of actual
left-point stochastic sums, rather than an assumed Itô identity. -/
def radialBrownianSelfIntegral (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D))
    (T : ℝ≥0) (ω : Ω) : ℝ :=
  (‖B T ω‖ ^ 2 - ‖B 0 ω‖ ^ 2 - (D : ℝ) * (T : ℝ)) / 2

theorem radial_brownian_self_sum_uniform (T : ℝ≥0) (n : ℕ) (hn : 0 < n) (ω : Ω) :
    radialBrownianSelfSum B (radialBrownianUniformTimes T n) ω =
      (‖B T ω‖ ^ 2 - ‖B 0 ω‖ ^ 2 -
        radialBrownianQuadraticSum B (radialBrownianUniformTimes T n) ω) / 2 := by
  unfold radialBrownianSelfSum radialBrownianQuadraticSum
  rw [finite_inner_increment_sum (fun i => B (radialBrownianUniformTimes T n i) ω)]
  have hn' : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  simp [radialBrownianUniformTimes, hn']

theorem radial_brownian_self_integral_limit (hB : IsRadialBrownian D P B) (T : ℝ≥0) :
    TendstoInMeasure P (fun n => radialBrownianSelfSum B (radialBrownianUniformTimes T n))
      atTop (radialBrownianSelfIntegral B T) := by
  have h := tendstoInMeasure_sub_half
    (radial_brownian_quadratic_variation_in_probability hB T)
    (fun ω => ‖B T ω‖ ^ 2 - ‖B 0 ω‖ ^ 2)
  apply TendstoInMeasure.congr' (h_left := ?_) (h_right := Filter.EventuallyEq.rfl) h
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact Eventually.of_forall (fun ω => (radial_brownian_self_sum_uniform T n hn ω).symm)

/-- The quadratic Itô identity now accompanies a proved stochastic-integral
limit on the actual Brownian probability space. -/
theorem radial_brownian_energy_ito (hB : IsRadialBrownian D P B) (T : ℝ≥0) :
    TendstoInMeasure P (fun n => radialBrownianSelfSum B (radialBrownianUniformTimes T n))
      atTop (radialBrownianSelfIntegral B T) ∧
    ∀ ω, ‖B T ω‖ ^ 2 / 2 = ‖B 0 ω‖ ^ 2 / 2 + (D : ℝ) * (T : ℝ) / 2 +
      radialBrownianSelfIntegral B T ω := by
  refine ⟨radial_brownian_self_integral_limit hB T, ?_⟩
  intro ω
  unfold radialBrownianSelfIntegral
  ring

theorem radial_brownian_self_integral_measurable (hB : IsRadialBrownian D P B) (T : ℝ≥0) :
    Measurable (radialBrownianSelfIntegral B T) :=
  ((((hB.measurable T).norm.pow_const 2).sub ((hB.measurable 0).norm.pow_const 2)).sub_const
    ((D : ℝ) * (T : ℝ))).div_const 2

theorem radial_brownian_self_integral_continuous (hB : IsRadialBrownian D P B) :
    ∀ᵐ ω ∂P, Continuous (fun T => radialBrownianSelfIntegral B T ω) := by
  filter_upwards [hB.continuous] with ω hω
  exact (((hω.norm.pow 2).sub continuous_const).sub
    (continuous_const.mul continuous_subtype_val)).div_const 2

theorem radial_brownian_self_integral_zero (ω : Ω) : radialBrownianSelfIntegral B 0 ω = 0 := by
  simp [radialBrownianSelfIntegral]

end
end Sigma
