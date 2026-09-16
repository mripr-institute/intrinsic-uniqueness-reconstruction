import SigmaProbLevyIntegral
import SigmaProbSurvival
import SigmaProbMGFUnique

namespace Sigma
noncomputable section

open Filter MeasureTheory Set
open scoped Topology ENNReal

/-- The probability Stieltjes transform used in `final:P5-stieltjes`. -/
def probabilityStieltjes (μ : Measure ℝ) (z : ℝ) : ℝ :=
  ∫ t : ℝ, (t + z)⁻¹ ∂μ

/-- The real exponential integral occurring in the explicit Gamma transform. -/
def expIntegralOne (z : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi z, Real.exp (-u) / u

/-- Alternating derivative inequalities on the positive ray. -/
def CompletelyMonotoneOnPositive (f : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∀ x : ℝ, 0 < x →
    0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n f x

/-- A concrete derivative tower on the positive ray. -/
def DerivativeTowerOnPositive (f : ℝ → ℝ) (d : ℕ → ℝ → ℝ) : Prop :=
  d 0 = f ∧ ∀ n : ℕ, ∀ x : ℝ, 0 < x → HasDerivAt (d n) (d (n + 1) x) x

theorem derivativeTower_iteratedDeriv {f : ℝ → ℝ} {d : ℕ → ℝ → ℝ}
    (h : DerivativeTowerOnPositive f d) (n : ℕ) (x : ℝ) (hx : 0 < x) :
    iteratedDeriv n f x = d n x := by
  induction n generalizing x with
  | zero => simp [iteratedDeriv_zero, h.1]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv n f =ᶠ[𝓝 x] d n := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        exact ih y hy
      rw [heq.deriv_eq, (h.2 n x hx).deriv]

def gammaLaplaceFunction (x : ℝ) : ℝ := (1 + x)⁻¹ ^ 2

def gammaLaplaceDerivative (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * ((n + 1).factorial : ℝ) * (1 + x)⁻¹ ^ (n + 2)

theorem gamma_laplace_derivative_tower :
    DerivativeTowerOnPositive gammaLaplaceFunction gammaLaplaceDerivative := by
  constructor
  · funext x
    simp [gammaLaplaceDerivative, gammaLaplaceFunction]
  · intro n x hx
    have hne : 1 + x ≠ 0 := ne_of_gt (by linarith)
    have hinv : HasDerivAt (fun y : ℝ => (1 + y)⁻¹) (-((1 + x)⁻¹ ^ 2)) x := by
      have h := ((hasDerivAt_const x 1).add (hasDerivAt_id x)).inv hne
      convert h using 1 <;> field_simp [hne] <;> ring
    have hp := hinv.pow (n + 2)
    unfold gammaLaplaceDerivative
    convert hp.const_mul ((-1 : ℝ) ^ n * ((n + 1).factorial : ℝ)) using 1
    · rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        show n + 1 + 2 = n + 3 by omega,
        show n + 2 - 1 = n + 1 by omega,
        Nat.factorial_succ]
      push_cast
      rw [show n + 3 = (n + 1) + 2 by omega, pow_add, pow_succ]
      ring

theorem gamma_laplace_completely_monotone :
    CompletelyMonotoneOnPositive gammaLaplaceFunction := by
  intro n x hx
  rw [derivativeTower_iteratedDeriv gamma_laplace_derivative_tower n x hx]
  unfold gammaLaplaceDerivative
  have hpos : 0 < (1 + x)⁻¹ := inv_pos.mpr (by linarith)
  rw [show (-1 : ℝ) ^ n *
      ((-1 : ℝ) ^ n * ((n + 1).factorial : ℝ) * (1 + x)⁻¹ ^ (n + 2)) =
      (((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n)) *
        (((n + 1).factorial : ℝ) * (1 + x)⁻¹ ^ (n + 2)) by ring]
  exact mul_nonneg (mul_self_nonneg _)
    (mul_nonneg (by positivity) (pow_nonneg hpos.le _))

theorem intrinsic_density_derivative (x : ℝ) :
    HasDerivAt SigmaPresentations.density ((1 - x) * Real.exp (-x)) x := by
  unfold SigmaPresentations.density
  convert (hasDerivAt_id x).mul (((hasDerivAt_id x).neg).exp) using 1 <;>
    simp only [id_eq] <;> ring

theorem intrinsic_density_not_completely_monotone :
    ¬ CompletelyMonotoneOnPositive SigmaPresentations.density := by
  intro h
  have hh := h 1 (1 / 2 : ℝ) (by norm_num)
  rw [iteratedDeriv_one, (intrinsic_density_derivative (1 / 2 : ℝ)).deriv] at hh
  norm_num at hh
  nlinarith [Real.exp_pos (-(1 / 2 : ℝ))]

theorem gamma_survival_second_derivative (x : ℝ) :
    iteratedDeriv 2 gammaSurvival x = (x - 1) * Real.exp (-x) := by
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  have hfirst : deriv gammaSurvival = fun y => -SigmaPresentations.density y := by
    funext y
    exact (gamma_survival_derivative y).deriv
  rw [hfirst]
  have hd := (intrinsic_density_derivative x).neg
  convert hd.deriv using 1 <;> ring

theorem gamma_survival_not_completely_monotone :
    ¬ CompletelyMonotoneOnPositive gammaSurvival := by
  intro h
  have hh := h 2 (1 / 2 : ℝ) (by norm_num)
  rw [gamma_survival_second_derivative] at hh
  norm_num at hh
  nlinarith [Real.exp_pos (-(1 / 2 : ℝ))]

theorem expIntegralOne_shift (z : ℝ) :
    expIntegralOne z = Real.exp (-z) *
      ∫ t : ℝ in Ioi 0, Real.exp (-t) / (t + z) := by
  have htranslate := (measurePreserving_add_right volume z).setIntegral_image_emb
    (Homeomorph.addRight z).isClosedEmbedding.measurableEmbedding
    (fun u : ℝ => Real.exp (-u) / u) (Ioi (0 : ℝ))
  have himage : (fun t : ℝ => t + z) '' Ioi 0 = Ioi z := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact by simpa using add_lt_add_right ht z
    · intro hu
      refine ⟨u - z, ?_, by ring⟩
      simpa using sub_pos.mpr hu
  rw [himage] at htranslate
  rw [expIntegralOne, htranslate, ← integral_mul_left]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change Real.exp (-(t + z)) / (t + z) =
    Real.exp (-z) * (Real.exp (-t) / (t + z))
  rw [show -(t + z) = -z + -t by ring, Real.exp_add]
  ring

theorem gamma_stieltjes_integral_formula (z : ℝ) (hz : 0 < z) :
    probabilityStieltjes gammaProbability z =
      1 - z * Real.exp z * expIntegralOne z := by
  rw [probabilityStieltjes, gamma_probability_integral]
  have h_exp : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
    simpa using positive_rate_exponential_integrable 1 (by norm_num)
  have h_quot : IntegrableOn (fun t : ℝ => Real.exp (-t) / (t + z)) (Ioi 0) := by
    apply (h_exp.const_mul (1 / z)).mono'
    · exact (((Real.continuous_exp.comp continuous_neg).measurable.div
        (continuous_id.add continuous_const).measurable).aestronglyMeasurable)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := mem_Ioi.mp ht
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos (add_pos ht hz)]
      have hden : z ≤ t + z := by linarith
      have hinv : (t + z)⁻¹ ≤ z⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hz hden
      rw [div_eq_mul_inv, one_div]
      calc
        Real.exp (-t) * (t + z)⁻¹ ≤ Real.exp (-t) * z⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le
        _ = z⁻¹ * Real.exp (-t) := mul_comm _ _
  have hsplit :
      (∫ t : ℝ in Ioi 0, SigmaPresentations.density t * (t + z)⁻¹) =
        (∫ t : ℝ in Ioi 0, Real.exp (-t)) -
          z * ∫ t : ℝ in Ioi 0, Real.exp (-t) / (t + z) := by
    rw [← integral_mul_left, ← integral_sub h_exp (h_quot.const_mul z)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [SigmaPresentations.density]
    have hn : t + z ≠ 0 := (add_pos ht hz).ne'
    field_simp
    ring
  rw [hsplit]
  have hexp : (∫ t : ℝ in Ioi 0, Real.exp (-t)) = 1 := by
    simpa using positive_rate_exponential_integral 1 (by norm_num)
  rw [hexp]
  rw [expIntegralOne_shift z]
  have he : Real.exp z * Real.exp (-z) = 1 := by rw [← Real.exp_add]; simp
  rw [mul_assoc z (Real.exp z) _, ← mul_assoc (Real.exp z) (Real.exp (-z)),
    he, one_mul]

end
end Sigma
