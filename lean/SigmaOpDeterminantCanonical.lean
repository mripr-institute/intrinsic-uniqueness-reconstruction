import SigmaOpDeterminantNative
import SigmaOpDeterminantRegularized
import SigmaOpCanonicalInverse

namespace Sigma
noncomputable section
open Filter
open scoped Topology

/-- Summability comes from the actual canonical resolvent, in either category. -/
theorem laguerre_shifted_determinant_summable (reg : Bool) :
    Summable (fun n : ℕ => ‖shiftedDeterminantCoefficient reg n‖^
      determinantSummabilityPower reg) := by
  apply native_shifted_determinant_summable reg laguerreHilbertBasis (fun n : ℕ => (n : ℝ))
    (fun n => Nat.cast_nonneg n) laguerreCanonicalOperator (laguerreResolvent 1 (by norm_num))
    (laguerre_canonical_positive_shift_resolvent 1 (by norm_num))
    laguerre_basis_mem_canonical_domain laguerre_canonical_basis_action
  simpa only [pow_two, ContinuousLinearMap.mul_def, laguerreSquaredResolvent] using
    laguerre_squared_resolvent_nuclear 1 (by norm_num)

/-- The basis-independent ordinary product agrees with the native finite-compression limit. -/
theorem laguerre_spectral_fredholm_determinant (z : ℂ) :
    shiftedSpectralDeterminant false (fun n : ℕ => (n : ℝ)) z =
      laguerreFredholmDeterminant z := by
  have h := (determinant_factors_multipliable false
    (fun n : ℕ => shiftedDeterminantCoefficient false n)
    (laguerre_shifted_determinant_summable false) z).hasProd.tendsto_prod_nat
  have he : (fun N => ∏ n ∈ Finset.range N,
      determinantFactor false (z * shiftedDeterminantCoefficient false n)) =
      laguerreFredholmApprox z := by
    funext N
    rw [laguerre_fredholm_approx_product]
    apply Finset.prod_congr rfl
    intro n hn
    simp [determinantFactor, shiftedDeterminantCoefficient, div_eq_mul_inv, inv_pow, add_comm]
  rw [he] at h
  exact h.limUnder_eq.symm

/-- The regularized unordered product agrees with the actual det-times-exponential
finite-compression convention used for the Hilbert--Schmidt determinant. -/
theorem laguerre_spectral_regularized_determinant (z : ℂ) :
    shiftedSpectralDeterminant true (fun n : ℕ => (n : ℝ)) z =
      laguerreRegularizedDeterminant z := by
  have h := (determinant_factors_multipliable true
    (fun n : ℕ => shiftedDeterminantCoefficient true n)
    (laguerre_shifted_determinant_summable true) z).hasProd.tendsto_prod_nat
  have he : (fun N => ∏ n ∈ Finset.range N,
      determinantFactor true (z * shiftedDeterminantCoefficient true n)) =
      laguerreRegularizedApprox z := by
    funext N
    rw [laguerre_regularized_approx_product]
    apply Finset.prod_congr rfl
    intro n hn
    simp [determinantFactor, shiftedDeterminantCoefficient, div_eq_mul_inv, add_comm]
  rw [he] at h
  exact h.limUnder_eq.symm

end
end Sigma
