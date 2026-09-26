import SigmaOpLaguerreResolventTrace
import SigmaProbEulerProduct
import Mathlib.Analysis.Calculus.SmoothSeries

/-! The digamma normalization and sign in paper `final:O4-resolvents`.
The digamma function is the actual logarithmic derivative of `Real.Gamma`.
Its convergent expansion is derived by differentiating Euler's log-Gamma
product locally, with a summable uniform derivative bound.
-/

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology

def realDigamma (a : ℝ) : ℝ := deriv Real.Gamma a / Real.Gamma a

theorem euler_log_gamma_positive_derivative (n : ℕ) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun x : ℝ => eulerLogGammaTerm (1-x) n)
      (((n:ℝ)+1)⁻¹-((n:ℝ)+a)⁻¹) a := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  have hna : 0 < (n:ℝ)+a := by positivity
  have he : 1-(1-a)/((n:ℝ)+1) = ((n:ℝ)+a)/((n:ℝ)+1) := by
    field_simp
    ring
  have hp : 0 < 1-(1-a)/((n:ℝ)+1) := by rw [he]; exact div_pos hna hn
  have hd := (((hasDerivAt_const a 1).sub
    (((hasDerivAt_const a 1).sub (hasDerivAt_id a)).div_const ((n:ℝ)+1))).log hp.ne').neg.sub
    (((hasDerivAt_const a 1).sub (hasDerivAt_id a)).div_const ((n:ℝ)+1))
  convert hd using 1
  · simp only [id_eq, he]
    field_simp [hn.ne', hna.ne']
    ring

private theorem reciprocal_difference_bound (n : ℕ) {a c M : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hca : c ≤ a) (hM : |a-1| ≤ M) :
    ‖((n:ℝ)+1)⁻¹-((n:ℝ)+a)⁻¹‖ ≤ M * (1 / ((n:ℝ)+c)^2) := by
  have hnc : 0 < (n:ℝ)+c := by positivity
  have hn1 : 0 < (n:ℝ)+1 := by positivity
  have hna : 0 < (n:ℝ)+a := hnc.trans_le (by linarith)
  have he : ((n:ℝ)+1)⁻¹-((n:ℝ)+a)⁻¹ =
      (a-1)/(((n:ℝ)+1)*((n:ℝ)+a)) := by field_simp
  have hden : ((n:ℝ)+c)^2 ≤ ((n:ℝ)+1)*((n:ℝ)+a) := by
    calc
      _ = ((n:ℝ)+c)*((n:ℝ)+c) := pow_two _
      _ ≤ _ := mul_le_mul (by linarith) (by linarith) hnc.le hn1.le
  rw [he, Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hn1 hna)]
  calc
    _ ≤ M / (((n:ℝ)+1)*((n:ℝ)+a)) :=
      div_le_div_of_nonneg_right hM (mul_pos hn1 hna).le
    _ ≤ M / ((n:ℝ)+c)^2 :=
      div_le_div_of_nonneg_left ((abs_nonneg _).trans hM) (sq_pos_of_pos hnc) hden
    _ = _ := by ring

/-- Differentiation of the Euler product at any positive real argument. -/
theorem log_gamma_euler_product_hasDerivAt {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun x : ℝ => Real.log (Real.Gamma x)-
      Real.eulerMascheroniConstant*(1-x))
      (∑' n : ℕ, (((n:ℝ)+1)⁻¹-((n:ℝ)+a)⁻¹)) a := by
  let c := min (a/2) 1
  let M := a+2
  have hc : 0 < c := lt_min (by linarith) zero_lt_one
  have hs := (operator_squared_resolvent_eigenvalues_summable c hc).mul_left M
  have hmem : a ∈ Ioo (a/2) (a+1) := by constructor <;> linarith
  have hd := hasDerivAt_tsum_of_isPreconnected hs isOpen_Ioo (convex_Ioo _ _).isPreconnected
    (g := fun n x => eulerLogGammaTerm (1-x) n)
    (g' := fun n x => ((n:ℝ)+1)⁻¹-((n:ℝ)+x)⁻¹)
    (fun n x hx => euler_log_gamma_positive_derivative n (by linarith [hx.1]))
    (fun n x hx => reciprocal_difference_bound n hc (min_le_right _ _)
      ((min_le_left _ _).trans hx.1.le) (by
        rw [abs_le]
        dsimp [M]
        constructor <;> linarith [hx.1, hx.2]))
    hmem (log_gamma_euler_product (1-a) (by linarith)).summable hmem
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with x hx
  have he := (log_gamma_euler_product (1-x) (by linarith [hx.1])).tsum_eq
  simpa only [sub_sub_cancel] using he.symm

/-- The actual logarithmic derivative of Gamma has the normalized convergent
digamma expansion, with Euler's constant retained. -/
theorem real_digamma_series {a : ℝ} (ha : 0 < a) :
    realDigamma a = -Real.eulerMascheroniConstant +
      ∑' n : ℕ, (((n:ℝ)+1)⁻¹-((n:ℝ)+a)⁻¹) := by
  have hG : DifferentiableAt ℝ Real.Gamma a :=
    Real.differentiableAt_Gamma (fun n => ne_of_gt (by
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith))
  have hd := (hG.hasDerivAt.log (Real.Gamma_pos_of_pos ha).ne').sub
    (((hasDerivAt_const a 1).sub (hasDerivAt_id a)).const_mul
      Real.eulerMascheroniConstant)
  have he := hd.unique (log_gamma_euler_product_hasDerivAt ha)
  simp only [realDigamma]
  simp only [sub_self, zero_sub, mul_neg, mul_one, sub_neg_eq_add] at he
  linarith

theorem real_digamma_series_summable {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => (((n:ℝ)+1)⁻¹-((n:ℝ)+a)⁻¹)) := by
  apply Summable.of_norm_bounded _
    ((operator_squared_resolvent_eigenvalues_summable (min a 1)
      (lt_min ha zero_lt_one)).mul_left |a-1|)
  intro n
  exact reciprocal_difference_bound n (lt_min ha zero_lt_one)
    (min_le_right _ _) (min_le_left _ _) le_rfl

/-- The sign is fixed by subtracting the two normalized expansions. -/
theorem real_digamma_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∑' n : ℕ, (((n:ℝ)+a)⁻¹-((n:ℝ)+b)⁻¹)) = realDigamma b-realDigamma a := by
  rw [real_digamma_series hb, real_digamma_series ha]
  have he := tsum_sub (real_digamma_series_summable hb) (real_digamma_series_summable ha)
  calc
    _ = ∑' n : ℕ, ((((n:ℝ)+1)⁻¹-((n:ℝ)+b)⁻¹)-
        (((n:ℝ)+1)⁻¹-((n:ℝ)+a)⁻¹)) := by
      apply tsum_congr
      intro n
      ring
    _ = _ := by rw [he]; ring

/-- The trace of the difference of the native resolvents is exactly the
paper's digamma difference, for arbitrary positive shifts. -/
theorem laguerre_resolvent_difference_trace_digamma (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    nuclearTrace (laguerreResolvent a ha-laguerreResolvent b hb)
      (laguerre_resolvent_difference_nuclear a b ha hb) =
      ((realDigamma b-realDigamma a : ℝ) : ℂ) := by
  rw [laguerre_resolvent_difference_trace, ← Complex.ofReal_tsum, real_digamma_sub ha hb]

end
end Sigma
