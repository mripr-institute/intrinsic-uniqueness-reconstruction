import SigmaOpLaguerre
import SigmaOperators
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Module.LinearMap.End

namespace Sigma
noncomputable section
open Polynomial
open scoped BigOperators

def opLaguerrePolynomial (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n+1), Polynomial.monomial k (opLaguerreCoefficient n k)

theorem op_laguerre_coefficient_above (n k : ℕ) (h : n<k) :
    opLaguerreCoefficient n k=0 := by
  simp [opLaguerreCoefficient,Nat.choose_eq_zero_of_lt (by omega : n+1<k+1)]

theorem op_laguerre_polynomial_coeff (n k : ℕ) :
    (opLaguerrePolynomial n).coeff k=opLaguerreCoefficient n k := by
  classical
  simp only [opLaguerrePolynomial,finset_sum_coeff,coeff_monomial]
  by_cases hk : k<n+1
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b hb hbk
      simp [hbk]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr hk))
  · rw [op_laguerre_coefficient_above n k (by omega)]
    apply Finset.sum_eq_zero
    intro b hb
    have hbk : b ≠ k := by intro he; subst b; exact hk (Finset.mem_range.mp hb)
    simp [hbk]

theorem op_laguerre_polynomial_eval (n : ℕ) (t : ℝ) :
    (opLaguerrePolynomial n).eval t=opLaguerre n t := by
  simp [opLaguerrePolynomial,opLaguerre,eval_finset_sum]

theorem op_laguerre_coefficient_recurrence (n k : ℕ) :
    (k+1 : ℝ)*(k+2)*opLaguerreCoefficient n (k+1)+
      ((n : ℝ)-k)*opLaguerreCoefficient n k=0 := by
  by_cases hkn : k≤n
  · have hc : ((n+1).choose (k+2) : ℝ)*(k+2)=
        ((n+1).choose (k+1) : ℝ)*((n : ℝ)-k) := by
      have h := Nat.choose_succ_right_eq (n+1) (k+1)
      rw [show n+1-(k+1)=n-k by omega] at h
      exact_mod_cast h
    have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hk : (k+1 : ℝ) ≠ 0 := by positivity
    simp only [opLaguerreCoefficient,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    rw [show k+1+1=k+2 by omega]
    field_simp [hf,hk]
    linear_combination -(-1 : ℝ)^k*(k+1)*(k.factorial : ℝ)*hc
  · rw [op_laguerre_coefficient_above n k (by omega),
      op_laguerre_coefficient_above n (k+1) (by omega)]
    ring

theorem op_laguerre_polynomial_ode (n : ℕ) :
    X*(opLaguerrePolynomial n).derivative.derivative+
      (C 2-X)*(opLaguerrePolynomial n).derivative+C (n : ℝ)*opLaguerrePolynomial n=0 := by
  ext k
  cases k with
  | zero =>
    simp only [coeff_add,coeff_X_mul_zero,sub_mul,coeff_sub,coeff_C_mul,
      coeff_derivative,op_laguerre_polynomial_coeff,coeff_zero]
    have h := op_laguerre_coefficient_recurrence n 0
    norm_num at h ⊢
    linarith
  | succ k =>
    simp only [coeff_add,coeff_X_mul,sub_mul,coeff_sub,coeff_C_mul,
      coeff_derivative,op_laguerre_polynomial_coeff,coeff_zero]
    have h := op_laguerre_coefficient_recurrence n (k+1)
    push_cast at h ⊢
    linear_combination h

theorem op_laguerre_derivative (n : ℕ) :
    deriv (opLaguerre n)=fun t => (opLaguerrePolynomial n).derivative.eval t := by
  rw [←show (fun t => (opLaguerrePolynomial n).eval t)=opLaguerre n from funext (op_laguerre_polynomial_eval n)]
  funext t
  exact (opLaguerrePolynomial n).deriv

theorem op_laguerre_second_derivative (n : ℕ) :
    deriv (deriv (opLaguerre n))=fun t => (opLaguerrePolynomial n).derivative.derivative.eval t := by
  rw [op_laguerre_derivative]
  funext t
  exact (opLaguerrePolynomial n).derivative.deriv

/-- The actual two ordinary derivatives satisfy the Laguerre equation, for
every mode including zero, with no positivity restriction on the evaluation point. -/
theorem op_laguerre_differential_equation (n : ℕ) (t : ℝ) :
    t*deriv (deriv (opLaguerre n)) t+(2-t)*deriv (opLaguerre n) t+
      n*opLaguerre n t=0 := by
  have h := congrArg (Polynomial.eval t) (op_laguerre_polynomial_ode n)
  rw [op_laguerre_second_derivative,op_laguerre_derivative]
  simpa only [eval_add,eval_mul,eval_sub,eval_C,eval_X,eval_zero,
    op_laguerre_polynomial_eval] using h

theorem op_laguerre_expression_eigenvalue (n : ℕ) (t : ℝ) :
    opExpression id (fun x => 2-x) (opLaguerre n) t=n*opLaguerre n t := by
  have h := op_laguerre_differential_equation n t
  simp only [opExpression,SigmaPresentations.differentialExpression,
    SigmaPresentations.localExpression,id_eq]
  linarith

def laguerreWeightedDerivative : Module.End ℝ (Polynomial ℝ) := Polynomial.derivative-1

theorem exp_neg_polynomial_derivative (P : Polynomial ℝ) (t : ℝ) :
    HasDerivAt (fun x => Real.exp (-x)*P.eval x)
      (Real.exp (-t)*(laguerreWeightedDerivative P).eval t) t := by
  convert ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).mul (P.hasDerivAt t) using 1
  simp only [laguerreWeightedDerivative,LinearMap.sub_apply,LinearMap.one_apply,eval_sub,Function.comp_apply]
  ring

theorem exp_neg_polynomial_iterated_derivative (P : Polynomial ℝ) (n : ℕ) :
    iteratedDeriv n (fun t => Real.exp (-t)*P.eval t)=
      fun t => Real.exp (-t)*((laguerreWeightedDerivative^n) P).eval t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    rw [pow_succ',LinearMap.mul_apply]
    exact (exp_neg_polynomial_derivative _ t).deriv

theorem laguerre_weighted_derivative_binomial (n : ℕ) (P : Polynomial ℝ) :
    (laguerreWeightedDerivative^n) P=
      ∑ j ∈ Finset.range (n+1),
        ((-1 : ℝ)^j*(n.choose j : ℝ)) • (Polynomial.derivative^[n-j] P) := by
  have h := (Commute.neg_left (Commute.one_left (Polynomial.derivative : Module.End ℝ (Polynomial ℝ)))).add_pow n
  have hh := congrArg (fun F : Module.End ℝ (Polynomial ℝ) => F P) h
  change ((-1+Polynomial.derivative : Module.End ℝ (Polynomial ℝ))^n) P=_ at hh
  rw [show (-1+Polynomial.derivative : Module.End ℝ (Polynomial ℝ))=laguerreWeightedDerivative by
    unfold laguerreWeightedDerivative; abel] at hh
  dsimp only at hh
  rw [hh,LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [LinearMap.mul_apply,Module.End.natCast_apply,map_nsmul]
  have he : (-1 : Module.End ℝ (Polynomial ℝ))^j=(-1 : ℝ)^j • (1 : Module.End ℝ (Polynomial ℝ)) := by
    rw [show (-1 : Module.End ℝ (Polynomial ℝ))=(-1 : ℝ) • (1 : Module.End ℝ (Polynomial ℝ)) by
      ext Q
      simp]
    rw [smul_pow,one_pow]
  rw [he,LinearMap.smul_apply,LinearMap.one_apply,LinearMap.pow_apply]
  simp only [nsmul_eq_mul,smul_eq_C_mul,map_mul,map_pow,map_natCast]
  ring

theorem laguerre_rodrigues_factorial_identity (n j : ℕ) (hj : j≤n) :
    (n.choose j : ℝ)*(Nat.descFactorial (n+1) (n-j) : ℝ)=
      (n.factorial : ℝ)*((n+1).choose (j+1) : ℝ)/(j.factorial : ℝ) := by
  have hf : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  apply (eq_div_iff hf).mpr
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  have hc : (n+1).choose (n-j)=(n+1).choose (j+1) :=
    Nat.choose_symm_of_eq_add (by omega)
  rw [hc,Nat.cast_mul]
  have h : (n.choose j : ℝ)*(j.factorial : ℝ)*((n-j).factorial : ℝ)=(n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  linear_combination ((n+1).choose (j+1) : ℝ)*h

theorem laguerre_rodrigues_coefficient (n j : ℕ) (hj : j≤n) :
    ((-1 : ℝ)^j*(n.choose j : ℝ))*(Nat.descFactorial (n+1) (n-j) : ℝ)=
      (n.factorial : ℝ)*opLaguerreCoefficient n j := by
  rw [mul_assoc,laguerre_rodrigues_factorial_identity n j hj]
  unfold opLaguerreCoefficient
  ring

theorem laguerre_rodrigues_polynomial (n : ℕ) :
    (laguerreWeightedDerivative^n) (X^(n+1))=
      C (n.factorial : ℝ)*X*opLaguerrePolynomial n := by
  classical
  rw [laguerre_weighted_derivative_binomial,opLaguerrePolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j≤n := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj
  rw [Polynomial.iterate_derivative_X_pow_eq_C_mul,
    show n+1-(n-j)=j+1 by omega,smul_eq_C_mul,←mul_assoc,←map_mul,
    laguerre_rodrigues_coefficient n j hjn,map_mul]
  rw [←C_mul_X_pow_eq_monomial,pow_succ]
  ring

/-- The full Rodrigues numerator identity is valid even at zero. -/
theorem op_laguerre_rodrigues_numerator (n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun x : ℝ => Real.exp (-x)*x^(n+1)) t=
      Real.exp (-t)*(n.factorial : ℝ)*t*opLaguerre n t := by
  have h := congrFun (exp_neg_polynomial_iterated_derivative (X^(n+1)) n) t
  simp only [eval_pow,eval_X,laguerre_rodrigues_polynomial,eval_mul,eval_C,
    op_laguerre_polynomial_eval] at h
  exact h.trans (by ring)

/-- Exact marked Rodrigues formula on the paper's positive ray (indeed at
every nonzero real point). The excluded point is only the displayed division by `t`. -/
theorem op_laguerre_rodrigues (n : ℕ) (t : ℝ) (ht : t ≠ 0) :
    Real.exp t/((n.factorial : ℝ)*t)*
      iteratedDeriv n (fun x : ℝ => Real.exp (-x)*x^(n+1)) t=opLaguerre n t := by
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [op_laguerre_rodrigues_numerator]
  have he : Real.exp t*Real.exp (-t)=1 := by rw [←Real.exp_add]; simp
  field_simp
  linear_combination ((n.factorial : ℝ)*t*opLaguerre n t)*he

end
end Sigma
