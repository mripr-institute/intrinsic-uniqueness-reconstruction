import SigmaOpDeterminantZeta

namespace Sigma
noncomputable section
open scoped Topology BigOperators

/-- The zero eigenvalue is omitted, rather than raised to a complex power. -/
def laguerrePrimeZetaMultiplier (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else 1 / (n : ℂ)^s

theorem laguerre_prime_zeta_multiplier_zero (s : ℂ) :
    laguerrePrimeZetaMultiplier s 0 = 0 := by simp [laguerrePrimeZetaMultiplier]

theorem laguerre_prime_zeta_multiplier_succ (s : ℂ) (n : ℕ) :
    laguerrePrimeZetaMultiplier s (n+1) = integerZetaMultiplier s n := by
  simp [laguerrePrimeZetaMultiplier, integerZetaMultiplier]

theorem laguerre_prime_zeta_multiplier_summable_iff (s : ℂ) :
    Summable (fun n => ‖laguerrePrimeZetaMultiplier s n‖) ↔ 1 < s.re := by
  rw [← summable_nat_add_iff 1]
  simp only [laguerre_prime_zeta_multiplier_succ]
  exact integer_zeta_multiplier_norm_summable_iff s

theorem laguerre_prime_zeta_multiplier_hasSum (s : ℂ) (hs : 1 < s.re) :
    HasSum (laguerrePrimeZetaMultiplier s) (riemannZeta s) := by
  apply (hasSum_nat_add_iff' 1).mp
  simpa only [laguerre_prime_zeta_multiplier_succ, Finset.sum_range_one,
    laguerre_prime_zeta_multiplier_zero, sub_zero] using integer_zeta_multiplier_hasSum s hs

/-- The maximal complex power on the positive spectral subspace, extended by zero
on the omitted kernel of the native Laguerre generator. -/
def laguerrePrimeZetaOperator (s : ℂ) :
    LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert :=
  integerBasisMultiplier laguerreHilbertBasis (laguerrePrimeZetaMultiplier s)

private theorem prime_zeta_multiplier_bound (s : ℂ) (hs : 1 < s.re) (n : ℕ) :
    ‖laguerrePrimeZetaMultiplier s n‖ ≤ ∑' k, ‖laguerrePrimeZetaMultiplier s k‖ :=
  le_tsum ((laguerre_prime_zeta_multiplier_summable_iff s).mpr hs) n
    (fun _ _ => norm_nonneg _)

def laguerrePrimeZetaBoundedOperator (s : ℂ) (hs : 1 < s.re) :
    LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert :=
  integerBasisBoundedMultiplier laguerreHilbertBasis (laguerrePrimeZetaMultiplier s)
    (∑' k, ‖laguerrePrimeZetaMultiplier s k‖) (tsum_nonneg (fun _ => norm_nonneg _))
    (prime_zeta_multiplier_bound s hs)

theorem laguerre_prime_zeta_bounded_basis_action (s : ℂ) (hs : 1 < s.re) (n : ℕ) :
    laguerrePrimeZetaBoundedOperator s hs (laguerreHilbertBasis n) =
      laguerrePrimeZetaMultiplier s n • laguerreHilbertBasis n :=
  integer_basis_bounded_multiplier_basis_action _ _ _ _ _ _

theorem laguerre_prime_zeta_bounded_nuclear (s : ℂ) (hs : 1 < s.re) :
    IsNuclearOperator (laguerrePrimeZetaBoundedOperator s hs) :=
  diagonal_operator_nuclear_of_summable laguerreHilbertBasis _ _
    (laguerre_prime_zeta_bounded_basis_action s hs)
    ((laguerre_prime_zeta_multiplier_summable_iff s).mpr hs)

theorem laguerre_prime_zeta_bounded_eq (s : ℂ) (hs : 1 < s.re) :
    laguerrePrimeZetaOperator s =
      (laguerrePrimeZetaBoundedOperator s hs).toLinearMap.toPMap ⊤ :=
  integer_basis_bounded_multiplier_eq _ _ _ _ _

/-- Omitting the genuine zero eigenspace leaves exactly the Riemann spectral trace. -/
theorem laguerre_prime_zeta_trace (s : ℂ) (hs : 1 < s.re) :
    nuclearTrace (laguerrePrimeZetaBoundedOperator s hs)
      (laguerre_prime_zeta_bounded_nuclear s hs) = riemannZeta s := by
  rw [diagonal_operator_nuclear_trace laguerreHilbertBasis _ _
    (laguerre_prime_zeta_bounded_basis_action s hs)]
  exact (laguerre_prime_zeta_multiplier_hasSum s hs).tsum_eq

theorem laguerre_prime_zeta_omits_zero (s : ℂ) (hs : 1 < s.re) :
    laguerrePrimeZetaBoundedOperator s hs (laguerreHilbertBasis 0) = 0 := by
  rw [laguerre_prime_zeta_bounded_basis_action, laguerre_prime_zeta_multiplier_zero, zero_smul]

theorem laguerre_prime_zeta_positive_basis_action (s : ℂ) (hs : 1 < s.re) (n : ℕ) :
    laguerrePrimeZetaBoundedOperator s hs (laguerreHilbertBasis (n+1)) =
      (1 / ((n : ℂ)+1)^s) • laguerreHilbertBasis (n+1) := by
  rw [laguerre_prime_zeta_bounded_basis_action, laguerre_prime_zeta_multiplier_succ]
  rfl

/-- The continued trace of the operator with its zero mode omitted. -/
def laguerrePrimeZetaDeterminant : ℂ := Complex.exp (-deriv riemannZeta 0)

theorem laguerre_prime_zeta_determinant_eq_shift_one :
    laguerrePrimeZetaDeterminant = laguerreZetaDeterminant 1 :=
  laguerre_zeta_determinant_one.symm

end
end Sigma
