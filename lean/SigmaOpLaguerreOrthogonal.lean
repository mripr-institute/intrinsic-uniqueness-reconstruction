import SigmaOpLaguerreL2

namespace Sigma
noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators ComplexConjugate

/-- The exponential factorial-moment functional on real polynomials. -/
def laguerreFactorialMoment : Polynomial ℝ →ₗ[ℝ] ℝ :=
  Polynomial.lsum (fun n => (n.factorial : ℝ) • LinearMap.id)

@[simp] theorem laguerre_factorial_moment_monomial (n : ℕ) (a : ℝ) :
    laguerreFactorialMoment (monomial n a) = a * (n.factorial : ℝ) := by
  simp [laguerreFactorialMoment, Polynomial.lsum, mul_comm]

theorem laguerre_factorial_moment_derivative (P : Polynomial ℝ) :
    laguerreFactorialMoment P.derivative = laguerreFactorialMoment P - P.coeff 0 := by
  induction P using Polynomial.induction_on' with
  | h_add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ]; ring
  | h_monomial n a =>
    cases n with
    | zero => simp [laguerreFactorialMoment, Polynomial.lsum]
    | succ n =>
      simp [derivative_monomial, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one]
      ring

theorem laguerre_factorial_moment_integration_by_parts (P Q : Polynomial ℝ)
    (hP : P.coeff 0 = 0) :
    laguerreFactorialMoment (laguerreWeightedDerivative P * Q) =
      -laguerreFactorialMoment (P * Q.derivative) := by
  have h := laguerre_factorial_moment_derivative (P * Q)
  simp only [derivative_mul, map_add, mul_coeff_zero, hP, zero_mul, sub_zero] at h
  simp only [laguerreWeightedDerivative, LinearMap.sub_apply, LinearMap.one_apply,
    sub_mul, map_sub]
  linarith

theorem laguerre_factorial_moment_iterated_integration_by_parts (n : ℕ)
    (P Q : Polynomial ℝ) (hP : ∀ k < n, P.coeff k = 0) :
    laguerreFactorialMoment (((laguerreWeightedDerivative ^ n) P) * Q) =
      (-1 : ℝ)^n * laguerreFactorialMoment (P * (Polynomial.derivative^[n]) Q) := by
  induction n generalizing P Q with
  | zero => simp
  | succ n ih =>
    have hw : ∀ k < n, (laguerreWeightedDerivative P).coeff k = 0 := by
      intro k hk
      simp [laguerreWeightedDerivative, coeff_derivative, hP k (by omega),
        hP (k+1) (by omega)]
    rw [pow_succ, LinearMap.mul_apply, ih _ Q hw,
      laguerre_factorial_moment_integration_by_parts P _ (hP 0 (by omega)),
      Function.iterate_succ_apply']
    ring

theorem gamma_polynomial_integral_factorial_moment (P : Polynomial ℝ) :
    (∫ t : ℝ, P.eval t ∂gammaProbability) =
      laguerreFactorialMoment (X * P) := by
  induction P using Polynomial.induction_on' with
  | h_add P Q hP hQ =>
    simp only [eval_add, integral_add (gamma_polynomial_integrable P)
      (gamma_polynomial_integrable Q), mul_add, map_add, hP, hQ]
  | h_monomial n a =>
    rw [show X * monomial n a = monomial (n+1) a by
      rw [←C_mul_X_pow_eq_monomial, ←C_mul_X_pow_eq_monomial, pow_succ]; ring]
    simp only [eval_monomial, integral_mul_left, gamma_probability_moments,
      laguerre_factorial_moment_monomial]

theorem op_laguerre_polynomial_rodrigues_integral (n : ℕ) (Q : Polynomial ℝ) :
    (n.factorial : ℝ) * (∫ t : ℝ, opLaguerre n t * Q.eval t ∂gammaProbability) =
      (-1 : ℝ)^n * laguerreFactorialMoment (X^(n+1) * (Polynomial.derivative^[n]) Q) := by
  have h := laguerre_factorial_moment_iterated_integration_by_parts n (X^(n+1)) Q
    (fun k hk => by simp [coeff_X_pow, show k ≠ n+1 by omega])
  rw [laguerre_rodrigues_polynomial] at h
  rw [show C (n.factorial : ℝ) * X * opLaguerrePolynomial n * Q =
    (n.factorial : ℝ) • (X * (opLaguerrePolynomial n * Q)) by
      rw [smul_eq_C_mul]; ring, LinearMap.map_smul] at h
  rw [←gamma_polynomial_integral_factorial_moment] at h
  simpa only [eval_mul, op_laguerre_polynomial_eval, smul_eq_mul] using h

theorem op_laguerre_polynomial_natDegree_le (n : ℕ) :
    (opLaguerrePolynomial n).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [op_laguerre_polynomial_coeff, op_laguerre_coefficient_above n k hk]

theorem op_laguerre_pair_integral_zero {m n : ℕ} (hmn : m < n) :
    (∫ t : ℝ, opLaguerre n t * opLaguerre m t ∂gammaProbability) = 0 := by
  have hd : (Polynomial.derivative^[n]) (opLaguerrePolynomial m) = 0 :=
    iterate_derivative_eq_zero ((op_laguerre_polynomial_natDegree_le m).trans_lt hmn)
  have h := op_laguerre_polynomial_rodrigues_integral n (opLaguerrePolynomial m)
  simp only [op_laguerre_polynomial_eval, hd, mul_zero, map_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast Nat.factorial_ne_zero n)

theorem op_laguerre_polynomial_top_derivative (n : ℕ) :
    (Polynomial.derivative^[n]) (opLaguerrePolynomial n) = C ((-1 : ℝ)^n) := by
  ext k
  rw [coeff_iterate_derivative, op_laguerre_polynomial_coeff]
  cases k with
  | zero =>
    simp only [zero_add, Nat.descFactorial_self, opLaguerre_leading_coefficient,
      nsmul_eq_mul, coeff_C_zero]
    field_simp
  | succ k =>
    rw [op_laguerre_coefficient_above n (k+1+n) (by omega)]
    rw [coeff_C, if_neg (Nat.succ_ne_zero k), smul_zero]

theorem op_laguerre_squared_integral (n : ℕ) :
    (∫ t : ℝ, opLaguerre n t * opLaguerre n t ∂gammaProbability) = n+1 := by
  have h := op_laguerre_polynomial_rodrigues_integral n (opLaguerrePolynomial n)
  rw [op_laguerre_polynomial_top_derivative,
    show X^(n+1) * C ((-1 : ℝ)^n) = monomial (n+1) ((-1 : ℝ)^n) by
      rw [←C_mul_X_pow_eq_monomial]; ring,
    laguerre_factorial_moment_monomial] at h
  simp only [op_laguerre_polynomial_eval] at h
  have hs : (-1 : ℝ)^n * (-1 : ℝ)^n = 1 := by
    rw [←mul_pow]; simp
  rw [←mul_assoc, hs, one_mul, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one] at h
  apply (mul_left_cancel₀ (show (n.factorial : ℝ) ≠ 0 by
    exact_mod_cast Nat.factorial_ne_zero n))
  rw [h]
  ring

theorem op_laguerre_pair_integral (n m : ℕ) :
    (∫ t : ℝ, opLaguerre n t * opLaguerre m t ∂gammaProbability) =
      if n = m then (n+1 : ℝ) else 0 := by
  rcases lt_trichotomy n m with h | rfl | h
  · rw [if_neg (ne_of_lt h)]
    simpa only [mul_comm] using op_laguerre_pair_integral_zero h
  · simp only [ite_true, op_laguerre_squared_integral]
  · rw [if_neg (ne_of_gt h)]
    exact op_laguerre_pair_integral_zero h

theorem laguerre_l2_inner (n m : ℕ) :
    @inner ℂ LaguerreWeightedHilbert _ (laguerreL2Vector n) (laguerreL2Vector m) =
      if n = m then (n+1 : ℂ) else 0 := by
  rw [L2.inner_def]
  have he : (fun t => @inner ℂ ℂ _ (laguerreL2Vector n t) (laguerreL2Vector m t)) =ᵐ[gammaProbability]
      (fun t => Complex.ofReal (opLaguerre n t * opLaguerre m t)) := by
    filter_upwards [(op_laguerre_complex_mem_l2 n).coeFn_toLp,
      (op_laguerre_complex_mem_l2 m).coeFn_toLp] with t hn hm
    change (laguerreL2Vector n) t = _ at hn
    change (laguerreL2Vector m) t = _ at hm
    rw [hn, hm]
    simp [RCLike.inner_apply, mul_comm]
  rw [integral_congr_ae he]
  have hc := Complex.ofRealCLM.integral_comp_comm
    (gamma_polynomial_integrable (opLaguerrePolynomial n * opLaguerrePolynomial m))
  simp only [eval_mul, op_laguerre_polynomial_eval] at hc
  change (∫ t : ℝ, Complex.ofReal (opLaguerre n t * opLaguerre m t) ∂gammaProbability) =
    Complex.ofReal (∫ t : ℝ, opLaguerre n t * opLaguerre m t ∂gammaProbability) at hc
  rw [hc, op_laguerre_pair_integral]
  split_ifs <;> simp

/-- The paper's normalized Laguerre functions form an orthonormal family in
the actual complex Hilbert space with measure `t * exp (-t) dt` on `(0,∞)`.
No completeness or self-adjoint-domain conclusion is asserted here. -/
theorem normalized_laguerre_l2_orthonormal :
    Orthonormal ℂ normalizedLaguerreL2Vector := by
  rw [orthonormal_iff_ite]
  intro n m
  simp only [normalizedLaguerreL2Vector, inner_smul_left, inner_smul_right,
    laguerre_l2_inner]
  by_cases h : n = m
  · subst m
    simp only [ite_true, map_inv₀, Complex.conj_ofReal]
    have hs : (Real.sqrt (n+1 : ℝ) : ℂ)^2 = (n+1 : ℂ) := by
      norm_cast
      exact Real.sq_sqrt (by positivity)
    have hn : (Real.sqrt (n+1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by positivity : (0:ℝ)<n+1)))
    rw [←hs]
    field_simp
    ring
  · simp [h]

theorem normalized_laguerre_l2_norm (n : ℕ) :
    ‖normalizedLaguerreL2Vector n‖ = 1 := normalized_laguerre_l2_orthonormal.1 n

theorem op_laguerre_pair_integrable (n m : ℕ) :
    Integrable (fun t : ℝ => opLaguerre n t * opLaguerre m t) gammaProbability := by
  simpa only [eval_mul, op_laguerre_polynomial_eval] using
    gamma_polynomial_integrable (opLaguerrePolynomial n * opLaguerrePolynomial m)

/-- The literal weighted orthogonality integral in the paper, including mode zero. -/
theorem op_laguerre_weighted_pair_integral (n m : ℕ) :
    (∫ t : ℝ in Set.Ioi 0, (t * Real.exp (-t)) *
      (opLaguerre n t * opLaguerre m t)) = if n = m then (n+1 : ℝ) else 0 := by
  simpa only [gamma_probability_integral, SigmaPresentations.density] using
    op_laguerre_pair_integral n m

end
end Sigma
