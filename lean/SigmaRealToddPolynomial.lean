import SigmaRealToddTower
import Mathlib.Algebra.Polynomial.Roots

namespace Sigma
noncomputable section
open PowerSeries
open scoped BigOperators

/-- The coefficient of X^n in exp(kX) T^(n+1), as an actual polynomial in k. -/
def toddTwistPolynomial (n : ℕ) : Polynomial ℚ :=
  ∑ p ∈ Finset.antidiagonal n,
    Polynomial.C (coeff ℚ p.2 (formalTodd ℚ ^ (n + 1)) / (p.1.factorial : ℚ)) *
      Polynomial.X ^ p.1

/-- The generalized binomial polynomial (k+1)...(k+n)/n!, including n=0. -/
def toddBinomialPolynomial (n : ℕ) : Polynomial ℚ :=
  Polynomial.C ((n.factorial : ℚ)⁻¹) *
    ∏ j ∈ Finset.range n, (Polynomial.X + Polynomial.C ((j : ℚ) + 1))

theorem todd_twist_polynomial_eval (n : ℕ) (k : ℚ) :
    (toddTwistPolynomial n).eval k =
      coeff ℚ n (formalExponential ℚ k * formalTodd ℚ ^ (n + 1)) := by
  rw [coeff_mul]
  simp only [toddTwistPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    formalExponential, coeff_rescale, coeff_exp]
  apply Finset.sum_congr rfl
  intro p hp
  change _ = k ^ p.1 * (1 / (p.1.factorial : ℚ)) *
    coeff ℚ p.2 (formalTodd ℚ ^ (n + 1))
  ring

theorem todd_binomial_polynomial_eval (n : ℕ) (k : ℚ) :
    (toddBinomialPolynomial n).eval k =
      (∏ j ∈ Finset.range n, (k + (j : ℚ) + 1)) / (n.factorial : ℚ) := by
  simp only [toddBinomialPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X]
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  ring

/-- The twist formula is an equality in Q[k], not merely a list of integer checks. -/
theorem todd_twist_polynomial_identity (n : ℕ) :
    toddTwistPolynomial n = toddBinomialPolynomial n := by
  apply Polynomial.funext
  intro k
  rw [todd_twist_polynomial_eval, todd_binomial_polynomial_eval]
  exact formal_twisted_todd_coeff ℚ k n

end
end Sigma
