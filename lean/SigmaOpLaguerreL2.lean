import SigmaOpLaguerreDifferential
import Mathlib.MeasureTheory.Function.L2Space

namespace Sigma
noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators

theorem gamma_polynomial_integrable (P : Polynomial ℝ) :
    Integrable (fun t : ℝ => P.eval t) gammaProbability := by
  have h := P.as_sum_support_C_mul_X_pow
  have he : (fun t : ℝ => P.eval t)=fun t =>
      ∑ k ∈ P.support, P.coeff k*t^k := by
    funext t
    conv_lhs => rw [h]
    simp [Polynomial.eval_finset_sum]
  rw [he]
  apply integrable_finset_sum
  intro k hk
  exact (gamma_probability_monomial_integrable k).const_mul (P.coeff k)

theorem gamma_complex_polynomial_mem_l2 (P : Polynomial ℝ) :
    Memℒp (fun t : ℝ => Complex.ofReal (P.eval t)) 2 gammaProbability := by
  have hc : Continuous (fun t : ℝ => Complex.ofReal (P.eval t)) := Complex.continuous_ofReal.comp P.continuous
  apply (memℒp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hi := gamma_polynomial_integrable (P^2)
  simpa only [Polynomial.eval_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs] using hi

theorem op_laguerre_complex_mem_l2 (n : ℕ) :
    Memℒp (fun t : ℝ => (opLaguerre n t : ℂ)) 2 gammaProbability := by
  simpa only [op_laguerre_polynomial_eval] using gamma_complex_polynomial_mem_l2 (opLaguerrePolynomial n)

theorem op_laguerre_expression_complex_mem_l2 (n : ℕ) :
    Memℒp (fun t : ℝ => (opExpression id (fun x => 2-x) (opLaguerre n) t : ℂ)) 2 gammaProbability := by
  have h := (op_laguerre_complex_mem_l2 n).const_smul (n : ℂ)
  simpa only [op_laguerre_expression_eigenvalue,Complex.ofReal_mul,Complex.ofReal_natCast,
    Pi.smul_apply,smul_eq_mul] using h

/-- Actual gamma-weighted complex `L²`, not the independent marked sequence model. -/
abbrev LaguerreWeightedHilbert := Lp ℂ 2 gammaProbability

def laguerreL2Vector (n : ℕ) : LaguerreWeightedHilbert :=
  (op_laguerre_complex_mem_l2 n).toLp (fun t : ℝ => (opLaguerre n t : ℂ))

def laguerreL2DifferentialImage (n : ℕ) : LaguerreWeightedHilbert :=
  (op_laguerre_expression_complex_mem_l2 n).toLp
    (fun t : ℝ => (opExpression id (fun x => 2-x) (opLaguerre n) t : ℂ))

theorem gamma_polynomial_nonzero_ae (P : Polynomial ℝ) (hP : P ≠ 0) :
    ∀ᵐ t ∂gammaProbability, P.eval t ≠ 0 := by
  letI : NoAtoms gammaProbability := ⟨gamma_probability_no_atom⟩
  rw [ae_iff]
  simpa only [not_not,Polynomial.IsRoot] using
    (Polynomial.finite_setOf_isRoot hP).measure_zero gammaProbability

theorem laguerre_l2_vector_ne_zero (n : ℕ) : laguerreL2Vector n ≠ 0 := by
  have hP : opLaguerrePolynomial n ≠ 0 := by
    intro hP
    apply opLaguerre_leading_coefficient_ne_zero n
    rw [←op_laguerre_polynomial_coeff,hP,Polynomial.coeff_zero]
  have hn := gamma_polynomial_nonzero_ae (opLaguerrePolynomial n) hP
  simp only [op_laguerre_polynomial_eval] at hn
  intro hz
  have hzero : (fun t : ℝ => (opLaguerre n t : ℂ)) =ᵐ[gammaProbability] 0 :=
    (op_laguerre_complex_mem_l2 n).coeFn_toLp.symm.trans ((Lp.eq_zero_iff_ae_eq_zero).mp hz)
  have hf : ∀ᵐ t ∂gammaProbability, False := by
    filter_upwards [hn,hzero] with t ht hz
    exact ht (Complex.ofReal_eq_zero.mp hz)
  obtain ⟨t,ht⟩ := hf.exists
  exact ht

/-- Equality of actual weighted `L²` classes of the differential image and the
eigenvalue multiple. This does not assume or declare a self-adjoint operator domain. -/
theorem laguerre_l2_differential_eigenvalue (n : ℕ) :
    laguerreL2DifferentialImage n=(n : ℂ) • laguerreL2Vector n := by
  unfold laguerreL2DifferentialImage laguerreL2Vector
  rw [←Memℒp.toLp_const_smul]
  apply Memℒp.toLp_congr
  exact Filter.Eventually.of_forall fun t => by
    simp [op_laguerre_expression_eigenvalue]

def normalizedLaguerreL2Vector (n : ℕ) : LaguerreWeightedHilbert :=
  ((Real.sqrt (n+1) : ℂ)⁻¹) • laguerreL2Vector n

theorem normalized_laguerre_l2_differential_eigenvalue (n : ℕ) :
    ((Real.sqrt (n+1) : ℂ)⁻¹) • laguerreL2DifferentialImage n=
      (n : ℂ) • normalizedLaguerreL2Vector n := by
  rw [laguerre_l2_differential_eigenvalue,normalizedLaguerreL2Vector]
  exact smul_comm _ _ _

def opComplexLaguerreExpression (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  -(t : ℂ)*deriv (deriv f) t-(2-(t : ℂ))*deriv f t

theorem complex_polynomial_derivative (P : Polynomial ℝ) :
    deriv (fun t : ℝ => Complex.ofReal (P.eval t))=
      fun t => Complex.ofReal (P.derivative.eval t) := by
  funext t
  exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (P.hasDerivAt t)).deriv

theorem op_laguerre_complex_derivative (n : ℕ) :
    deriv (fun t : ℝ => (opLaguerre n t : ℂ))=
      fun t => Complex.ofReal ((opLaguerrePolynomial n).derivative.eval t) := by
  have h := complex_polynomial_derivative (opLaguerrePolynomial n)
  simpa only [op_laguerre_polynomial_eval] using h

theorem op_laguerre_complex_expression (n : ℕ) (t : ℝ) :
    opComplexLaguerreExpression (fun x => (opLaguerre n x : ℂ)) t=
      (opExpression id (fun x => 2-x) (opLaguerre n) t : ℂ) := by
  unfold opComplexLaguerreExpression
  rw [op_laguerre_complex_derivative,complex_polynomial_derivative]
  simp only [opExpression,SigmaPresentations.differentialExpression,
    SigmaPresentations.localExpression,id_eq]
  rw [op_laguerre_second_derivative,op_laguerre_derivative]
  push_cast
  rfl

theorem op_laguerre_native_complex_eigenvalue (n : ℕ) (t : ℝ) :
    opComplexLaguerreExpression (fun x => (opLaguerre n x : ℂ)) t=
      (n : ℂ)*(opLaguerre n t : ℂ) := by
  rw [op_laguerre_complex_expression,op_laguerre_expression_eigenvalue]
  push_cast
  rfl

theorem op_laguerre_native_complex_image_mem_l2 (n : ℕ) :
    Memℒp (opComplexLaguerreExpression (fun t => (opLaguerre n t : ℂ))) 2 gammaProbability := by
  have he : opComplexLaguerreExpression (fun t => (opLaguerre n t : ℂ))=
      fun t => (opExpression id (fun x => 2-x) (opLaguerre n) t : ℂ) :=
    funext (op_laguerre_complex_expression n)
  rw [he]
  exact op_laguerre_expression_complex_mem_l2 n

theorem laguerre_l2_native_complex_eigenvalue (n : ℕ) :
    (op_laguerre_native_complex_image_mem_l2 n).toLp
      (opComplexLaguerreExpression (fun t => (opLaguerre n t : ℂ)))=
      (n : ℂ) • laguerreL2Vector n := by
  rw [←laguerre_l2_differential_eigenvalue]
  apply Memℒp.toLp_congr
  exact Filter.Eventually.of_forall (op_laguerre_complex_expression n)

theorem op_complex_laguerre_expression_const_mul (c : ℂ) (f : ℝ → ℂ) (t : ℝ) :
    opComplexLaguerreExpression (fun x => c*f x) t=c*opComplexLaguerreExpression f t := by
  unfold opComplexLaguerreExpression
  rw [deriv_const_mul_field',deriv_const_mul_field']
  ring

/-- The paper's exact normalized representative, with its marked positive square root. -/
def normalizedOpLaguerre (n : ℕ) (t : ℝ) : ℂ :=
  (opLaguerre n t : ℂ)/(Real.sqrt (n+1) : ℂ)

theorem normalized_op_laguerre_scalar (n : ℕ) :
    normalizedOpLaguerre n=fun t => (Real.sqrt (n+1) : ℂ)⁻¹*(opLaguerre n t : ℂ) := by
  funext t
  unfold normalizedOpLaguerre
  rw [div_eq_mul_inv,mul_comm]

theorem normalized_op_laguerre_native_eigenvalue (n : ℕ) (t : ℝ) :
    opComplexLaguerreExpression (normalizedOpLaguerre n) t=(n : ℂ)*normalizedOpLaguerre n t := by
  rw [normalized_op_laguerre_scalar,op_complex_laguerre_expression_const_mul,
    op_laguerre_native_complex_eigenvalue]
  ring

theorem normalized_op_laguerre_mem_l2 (n : ℕ) :
    Memℒp (normalizedOpLaguerre n) 2 gammaProbability := by
  rw [normalized_op_laguerre_scalar]
  exact (op_laguerre_complex_mem_l2 n).const_smul (Real.sqrt (n+1) : ℂ)⁻¹

theorem normalized_op_laguerre_to_l2 (n : ℕ) :
    (normalized_op_laguerre_mem_l2 n).toLp (normalizedOpLaguerre n)=normalizedLaguerreL2Vector n := by
  unfold normalizedLaguerreL2Vector laguerreL2Vector
  rw [←Memℒp.toLp_const_smul]
  apply Memℒp.toLp_congr
  exact Filter.Eventually.of_forall fun t => congrFun (normalized_op_laguerre_scalar n) t

theorem normalized_laguerre_l2_vector_ne_zero (n : ℕ) : normalizedLaguerreL2Vector n ≠ 0 := by
  have hn : (Real.sqrt (n+1) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by positivity : (0 : ℝ)<n+1))
  unfold normalizedLaguerreL2Vector
  exact smul_ne_zero (inv_ne_zero hn) (laguerre_l2_vector_ne_zero n)

end
end Sigma
