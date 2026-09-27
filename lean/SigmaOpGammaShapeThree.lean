import SigmaOpLaguerreOrthogonal
import SigmaProbGammaTransforms

namespace Sigma
noncomputable section
open MeasureTheory Polynomial ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal
set_option maxHeartbeats 800000

/-- The paper's second actual coordinate probability, Gamma shape three and rate one. -/
def gammaShapeThreeProbability : Measure ℝ := gammaMeasure 3 1

instance gamma_shape_three_is_probability : IsProbabilityMeasure gammaShapeThreeProbability :=
  isProbabilityMeasureGamma (by norm_num) (by norm_num)

theorem gamma_shape_three_pdf (t : ℝ) :
    gammaPDFReal 3 1 t = if 0 ≤ t then t^2 * Real.exp (-t) / 2 else 0 := by
  have hg : Real.Gamma 3 = 2 := by
    simp
  norm_num [gammaPDFReal, hg, Real.rpow_two]
  split_ifs <;> ring

theorem gamma_shape_three_integral (f : ℝ → ℝ) :
    (∫ t, f t ∂gammaShapeThreeProbability) =
      ∫ t : ℝ in Ioi 0, (t^2 * Real.exp (-t) / 2) * f t := by
  change (∫ t, f t ∂volume.withDensity
    (fun t => ((Real.toNNReal (gammaPDFReal 3 1 t) : ℝ≥0) : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul
    ((measurable_gammaPDFReal 3 1).real_toNNReal)]
  have hfun : (fun t => Real.toNNReal (gammaPDFReal 3 1 t) • f t) =
      (Ici (0 : ℝ)).indicator (fun t => (t^2 * Real.exp (-t) / 2) * f t) := by
    funext t
    rw [NNReal.smul_def, smul_eq_mul,
      Real.coe_toNNReal _ (gammaPDFReal_nonneg (by norm_num) (by norm_num) t),
      gamma_shape_three_pdf]
    by_cases ht : 0 ≤ t <;> simp [ht]
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

theorem gamma_shape_three_moments (n : ℕ) :
    (∫ t : ℝ, t^n ∂gammaShapeThreeProbability) = ((n+2).factorial : ℝ) / 2 := by
  rw [gamma_shape_three_integral]
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (n : ℝ)+3) (r := 1) (by positivity) (by norm_num)
  have hg : Real.Gamma ((n : ℝ)+3) = ((n+2).factorial : ℝ) := by
    convert Real.Gamma_nat_eq_factorial (n+2) using 1
    push_cast
    ring
  rw [one_div_one, Real.one_rpow, one_mul, hg] at hi
  rw [← hi, ← integral_div]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have he : (n : ℝ)+3-1 = ((n+2 : ℕ) : ℝ) := by push_cast; ring
  dsimp only
  rw [he, Real.rpow_natCast]
  rw [pow_add]
  ring

theorem gamma_shape_three_monomial_integrable (n : ℕ) :
    Integrable (fun t : ℝ => t^n) gammaShapeThreeProbability := by
  by_contra h
  have he := gamma_shape_three_moments n
  rw [integral_undef h] at he
  have hp : (0 : ℝ) < (n+2).factorial := by positivity
  linarith

theorem gamma_shape_three_mean : (∫ t : ℝ, t ∂gammaShapeThreeProbability) = 3 := by
  have h := gamma_shape_three_moments 1
  norm_num [Nat.factorial] at h
  exact h

theorem gamma_shape_three_coordinate_law_ne_shape_two :
    gammaShapeThreeProbability ≠ gammaProbability := by
  intro h
  have he := gamma_shape_three_mean
  rw [h, gamma_probability_mean] at he
  norm_num at he

theorem gamma_shape_three_polynomial_integrable (P : Polynomial ℝ) :
    Integrable (fun t : ℝ => P.eval t) gammaShapeThreeProbability := by
  have h := P.as_sum_support_C_mul_X_pow
  have he : (fun t : ℝ => P.eval t) = fun t => ∑ k ∈ P.support, P.coeff k * t^k := by
    funext t
    conv_lhs => rw [h]
    simp [Polynomial.eval_finset_sum]
  rw [he]
  exact integrable_finset_sum _ (fun k _ =>
    (gamma_shape_three_monomial_integrable k).const_mul _)

theorem gamma_shape_three_polynomial_integral (P : Polynomial ℝ) :
    (∫ t : ℝ, P.eval t ∂gammaShapeThreeProbability) =
      laguerreFactorialMoment (X^2 * P) / 2 := by
  induction P using Polynomial.induction_on' with
  | h_add P Q hP hQ =>
    simp only [eval_add, integral_add (gamma_shape_three_polynomial_integrable P)
      (gamma_shape_three_polynomial_integrable Q), mul_add, map_add, hP, hQ]
    ring
  | h_monomial n a =>
    rw [show X^2 * monomial n a = monomial (n+2) a by
      rw [←C_mul_X_pow_eq_monomial, ←C_mul_X_pow_eq_monomial, pow_add]; ring]
    simp only [eval_monomial, integral_mul_left, gamma_shape_three_moments,
      laguerre_factorial_moment_monomial]
    ring

/-- `L_n^(2)` is the negative derivative of the already formalized `L_(n+1)^(1)`. -/
def gammaShapeThreeLaguerrePolynomial (n : ℕ) : Polynomial ℝ :=
  -(opLaguerrePolynomial (n+1)).derivative

def gammaShapeThreeLaguerre (n : ℕ) (t : ℝ) : ℝ :=
  (gammaShapeThreeLaguerrePolynomial n).eval t

theorem gamma_shape_three_laguerre_polynomial_ode (n : ℕ) :
    X * (gammaShapeThreeLaguerrePolynomial n).derivative.derivative +
      (C 3-X) * (gammaShapeThreeLaguerrePolynomial n).derivative +
      C (n : ℝ) * gammaShapeThreeLaguerrePolynomial n = 0 := by
  have h := congrArg Polynomial.derivative (op_laguerre_polynomial_ode (n+1))
  simp only [derivative_add, derivative_mul, derivative_X, derivative_sub,
    derivative_C, derivative_zero, one_mul, zero_sub, neg_mul, zero_mul, add_zero] at h
  unfold gammaShapeThreeLaguerrePolynomial
  simp only [derivative_neg]
  push_cast at h
  simp only [map_add, map_one] at h
  simp only [map_ofNat] at h ⊢
  norm_num at h ⊢
  linear_combination -h

theorem gamma_shape_three_laguerre_derivative (n : ℕ) :
    deriv (gammaShapeThreeLaguerre n) =
      fun t => (gammaShapeThreeLaguerrePolynomial n).derivative.eval t := by
  funext t
  exact (gammaShapeThreeLaguerrePolynomial n).deriv

theorem gamma_shape_three_laguerre_second_derivative (n : ℕ) :
    deriv (deriv (gammaShapeThreeLaguerre n)) =
      fun t => (gammaShapeThreeLaguerrePolynomial n).derivative.derivative.eval t := by
  rw [gamma_shape_three_laguerre_derivative]
  funext t
  exact (gammaShapeThreeLaguerrePolynomial n).derivative.deriv

theorem gamma_shape_three_laguerre_native_eigenvalue (n : ℕ) (t : ℝ) :
    -t * deriv (deriv (gammaShapeThreeLaguerre n)) t -
      (3-t) * deriv (gammaShapeThreeLaguerre n) t =
        (n : ℝ) * gammaShapeThreeLaguerre n t := by
  have h := congrArg (Polynomial.eval t) (gamma_shape_three_laguerre_polynomial_ode n)
  rw [gamma_shape_three_laguerre_second_derivative, gamma_shape_three_laguerre_derivative]
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_zero] at h
  dsimp [gammaShapeThreeLaguerre]
  linarith

theorem gamma_shape_three_laguerre_coeff (n k : ℕ) :
    (gammaShapeThreeLaguerrePolynomial n).coeff k =
      -(k+1 : ℝ) * opLaguerreCoefficient (n+1) (k+1) := by
  simp only [gammaShapeThreeLaguerrePolynomial, coeff_neg, coeff_derivative,
    op_laguerre_polynomial_coeff, nsmul_eq_mul, mul_comm]
  ring

theorem gamma_shape_three_laguerre_degree_le (n : ℕ) :
    (gammaShapeThreeLaguerrePolynomial n).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [gamma_shape_three_laguerre_coeff,
    op_laguerre_coefficient_above (n+1) (k+1) (by omega), mul_zero]

theorem gamma_shape_three_laguerre_leading_ne_zero (n : ℕ) :
    (gammaShapeThreeLaguerrePolynomial n).coeff n ≠ 0 := by
  rw [gamma_shape_three_laguerre_coeff]
  exact mul_ne_zero (neg_ne_zero.mpr (by positivity))
    (opLaguerre_leading_coefficient_ne_zero (n+1))

theorem gamma_shape_three_laguerre_zero : gammaShapeThreeLaguerrePolynomial 0 = 1 := by
  norm_num [gammaShapeThreeLaguerrePolynomial, opLaguerrePolynomial,
    opLaguerreCoefficient, Finset.sum_range_succ, derivative_monomial]

/-- The weighted Green identity for actual polynomial Gamma-two integrals. -/
theorem gamma_shape_three_laguerre_green (n : ℕ) (Q : Polynomial ℝ) :
    laguerreFactorialMoment (X^2 * (opLaguerrePolynomial n).derivative * Q.derivative) =
      (n : ℝ) * laguerreFactorialMoment (X * opLaguerrePolynomial n * Q) := by
  have h := laguerre_factorial_moment_integration_by_parts
    (X^2 * (opLaguerrePolynomial n).derivative) Q (by simp [mul_coeff_zero])
  have hw : laguerreWeightedDerivative (X^2 * (opLaguerrePolynomial n).derivative) =
      -C (n : ℝ) * X * opLaguerrePolynomial n := by
    have ho := op_laguerre_polynomial_ode n
    simp only [map_natCast, map_ofNat] at ho
    dsimp [laguerreWeightedDerivative]
    simp only [derivative_mul, derivative_pow, derivative_X, one_mul]
    simp only [map_natCast, map_ofNat]
    linear_combination X * ho
  rw [hw] at h
  have he : -C (n : ℝ) * X * opLaguerrePolynomial n * Q =
      -(n : ℝ) • (X * opLaguerrePolynomial n * Q) := by
    rw [smul_eq_C_mul, map_neg]
    ring
  rw [he, LinearMap.map_smul] at h
  dsimp only [smul_eq_mul] at h
  linarith

/-- The exact Gamma-three orthogonality integral and squared norms. -/
theorem gamma_shape_three_laguerre_pair_integral (n m : ℕ) :
    (∫ t : ℝ, gammaShapeThreeLaguerre n t * gammaShapeThreeLaguerre m t
      ∂gammaShapeThreeProbability) =
        if n = m then (n+1 : ℝ) * (n+2) / 2 else 0 := by
  have he : (fun t => gammaShapeThreeLaguerre n t * gammaShapeThreeLaguerre m t) =
      fun t => (gammaShapeThreeLaguerrePolynomial n * gammaShapeThreeLaguerrePolynomial m).eval t := by
    funext t
    simp [gammaShapeThreeLaguerre]
  rw [he, gamma_shape_three_polynomial_integral]
  have hp : X^2 * (gammaShapeThreeLaguerrePolynomial n * gammaShapeThreeLaguerrePolynomial m) =
      X^2 * (opLaguerrePolynomial (n+1)).derivative * (opLaguerrePolynomial (m+1)).derivative := by
    unfold gammaShapeThreeLaguerrePolynomial
    ring
  rw [hp, gamma_shape_three_laguerre_green]
  have hi := gamma_polynomial_integral_factorial_moment
    (opLaguerrePolynomial (n+1) * opLaguerrePolynomial (m+1))
  rw [show X * opLaguerrePolynomial (n+1) * opLaguerrePolynomial (m+1) =
    X * (opLaguerrePolynomial (n+1) * opLaguerrePolynomial (m+1)) by ring, ← hi]
  simp only [eval_mul, op_laguerre_polynomial_eval]
  rw [op_laguerre_pair_integral]
  by_cases hnm : n = m
  · simp [hnm]
    ring
  · simp [hnm]

abbrev GammaShapeThreeWeightedHilbert := Lp ℂ 2 gammaShapeThreeProbability

theorem gamma_shape_three_complex_polynomial_mem_l2 (P : Polynomial ℝ) :
    Memℒp (fun t : ℝ => Complex.ofReal (P.eval t)) 2 gammaShapeThreeProbability := by
  have hc : Continuous (fun t : ℝ => Complex.ofReal (P.eval t)) :=
    Complex.continuous_ofReal.comp P.continuous
  apply (memℒp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hi := gamma_shape_three_polynomial_integrable (P*P)
  convert hi using 1
  funext t
  rw [Polynomial.eval_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, pow_two]

def gammaShapeThreeL2Vector (n : ℕ) : GammaShapeThreeWeightedHilbert :=
  (gamma_shape_three_complex_polynomial_mem_l2 (gammaShapeThreeLaguerrePolynomial n)).toLp
    (fun t => (gammaShapeThreeLaguerre n t : ℂ))

theorem gamma_shape_three_l2_inner (n m : ℕ) :
    @inner ℂ GammaShapeThreeWeightedHilbert _ (gammaShapeThreeL2Vector n) (gammaShapeThreeL2Vector m) =
      if n = m then ((n+1 : ℂ) * (n+2) / 2) else 0 := by
  rw [L2.inner_def]
  have he : (fun t => @inner ℂ ℂ _ (gammaShapeThreeL2Vector n t) (gammaShapeThreeL2Vector m t))
      =ᵐ[gammaShapeThreeProbability]
        (fun t => Complex.ofReal (gammaShapeThreeLaguerre n t * gammaShapeThreeLaguerre m t)) := by
    filter_upwards [(gamma_shape_three_complex_polynomial_mem_l2 (gammaShapeThreeLaguerrePolynomial n)).coeFn_toLp,
      (gamma_shape_three_complex_polynomial_mem_l2 (gammaShapeThreeLaguerrePolynomial m)).coeFn_toLp] with t hn hm
    change gammaShapeThreeL2Vector n t = _ at hn
    change gammaShapeThreeL2Vector m t = _ at hm
    rw [hn, hm]
    simp [RCLike.inner_apply, mul_comm, gammaShapeThreeLaguerre]
  rw [integral_congr_ae he]
  have hc := Complex.ofRealCLM.integral_comp_comm
    (gamma_shape_three_polynomial_integrable
      (gammaShapeThreeLaguerrePolynomial n * gammaShapeThreeLaguerrePolynomial m))
  simp only [eval_mul] at hc
  change (∫ t : ℝ, Complex.ofReal (gammaShapeThreeLaguerre n t * gammaShapeThreeLaguerre m t)
    ∂gammaShapeThreeProbability) = Complex.ofReal
      (∫ t : ℝ, gammaShapeThreeLaguerre n t * gammaShapeThreeLaguerre m t
        ∂gammaShapeThreeProbability) at hc
  rw [hc, gamma_shape_three_laguerre_pair_integral]
  split_ifs <;> simp

def normalizedGammaShapeThreeL2Vector (n : ℕ) : GammaShapeThreeWeightedHilbert :=
  ((Real.sqrt ((n+1 : ℝ)*(n+2)/2) : ℂ)⁻¹) • gammaShapeThreeL2Vector n

theorem normalized_gamma_shape_three_l2_orthonormal :
    Orthonormal ℂ normalizedGammaShapeThreeL2Vector := by
  rw [orthonormal_iff_ite]
  intro n m
  simp only [normalizedGammaShapeThreeL2Vector, inner_smul_left, inner_smul_right,
    gamma_shape_three_l2_inner]
  by_cases h : n = m
  · subst m
    simp only [ite_true, map_inv₀, Complex.conj_ofReal]
    have hs : (Real.sqrt ((n+1 : ℝ)*(n+2)/2) : ℂ)^2 = ((n+1 : ℂ)*(n+2)/2) := by
      have hreal := Real.sq_sqrt (by positivity : (0:ℝ)≤(n+1 : ℝ)*(n+2)/2)
      have hcomplex := congrArg Complex.ofReal hreal
      push_cast at hcomplex
      exact hcomplex
    have hn : (Real.sqrt ((n+1 : ℝ)*(n+2)/2) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by positivity : (0:ℝ)<(n+1 : ℝ)*(n+2)/2))
    rw [← hs]
    have halg (z : ℂ) (hz : z ≠ 0) : z⁻¹ * (z⁻¹ * z^2) = 1 := by
      field_simp
      ring
    exact halg _ hn
  · simp [h]

end
end Sigma
