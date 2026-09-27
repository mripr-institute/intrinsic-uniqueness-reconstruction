import SigmaOpCanonicalInverse
import SigmaOpIntegerEigenbasis
import SigmaOpLaguerreResolventTrace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

namespace Sigma
noncomputable section
open scoped ENNReal

/-! The inverse logarithm of the actual squared canonical resolvent.  All
unbounded operators below use the existing maximal complex multiplier; no
finite-span domain is substituted for the native operator domain. -/

/-- The scalar spectral coordinate of `(1+A)⁻²`. -/
def canonicalJCoordinate (n : ℕ) : ℝ := ((1 + (n : ℝ))⁻¹)^2

theorem canonical_negative_log_borel : Measurable (fun t : ℝ => -Real.log t) :=
  Real.measurable_log.neg

theorem canonical_j_coordinate_pos (n : ℕ) : 0 < canonicalJCoordinate n := by
  unfold canonicalJCoordinate
  positivity

theorem canonical_j_negative_log (n : ℕ) :
    -Real.log (canonicalJCoordinate n) = gammaLaplaceExponent n := by
  simp only [canonicalJCoordinate, Real.log_pow, Real.log_inv, Nat.cast_ofNat,
    gammaLaplaceExponent]
  ring

theorem canonical_j_exp_negative_exponent (n : ℕ) :
    Real.exp (-gammaLaplaceExponent n) = canonicalJCoordinate n := by
  rw [← canonical_j_negative_log, neg_neg, Real.exp_log (canonical_j_coordinate_pos n)]

/-- This coordinate formula concerns the square of the genuine bounded
two-sided inverse of `1+A` on the original weighted Hilbert space. -/
theorem laguerre_canonical_j_coordinate (x : LaguerreWeightedHilbert) (n : ℕ) :
    laguerreHilbertBasis.repr (laguerreSquaredResolvent 1 zero_lt_one x) n =
      (canonicalJCoordinate n : ℂ) * laguerreHilbertBasis.repr x n := by
  simp only [laguerreSquaredResolvent, ContinuousLinearMap.comp_apply,
    laguerre_resolvent_coordinate, Complex.ofReal_one]
  unfold canonicalJCoordinate
  push_cast
  ring

theorem laguerre_canonical_j_basis_action (n : ℕ) :
    laguerreSquaredResolvent 1 zero_lt_one (laguerreHilbertBasis n) =
      (canonicalJCoordinate n : ℂ) • laguerreHilbertBasis n := by
  rw [laguerre_squared_resolvent_basis_action]
  congr 1
  unfold canonicalJCoordinate
  push_cast
  ring

/-- The scalar supplied to the logarithm is extracted from the full actual
squared resolvent, in its proved complete spectral basis. -/
theorem laguerre_canonical_j_spectral_value (n : ℕ) :
    (@inner ℂ LaguerreWeightedHilbert _ (laguerreHilbertBasis n)
      (laguerreSquaredResolvent 1 zero_lt_one (laguerreHilbertBasis n))).re =
      canonicalJCoordinate n := by
  rw [laguerre_canonical_j_basis_action, inner_smul_right,
    ← laguerreHilbertBasis.repr_apply_apply, laguerreHilbertBasis.repr_self,
    lp.single_apply_self, mul_one, Complex.ofReal_re]

/-- The limiting endpoint zero is not an eigenspace of the complete native
bounded operator, even though its positive eigenvalues converge to zero. -/
theorem laguerre_canonical_j_kernel_zero (x : LaguerreWeightedHilbert)
    (hx : laguerreSquaredResolvent 1 zero_lt_one x = 0) : x = 0 := by
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext n
  have hc := congrArg (fun y : LaguerreWeightedHilbert => laguerreHilbertBasis.repr y n) hx
  change laguerreHilbertBasis.repr (laguerreSquaredResolvent 1 zero_lt_one x) n =
    laguerreHilbertBasis.repr 0 n at hc
  rw [laguerre_canonical_j_coordinate] at hc
  simp only [map_zero, lp.coeFn_zero, Pi.zero_apply] at hc ⊢
  exact (mul_eq_zero.mp hc).resolve_left (by
    exact_mod_cast (canonical_j_coordinate_pos n).ne')

/-- Applying the Borel function `-log` to the complete positive spectral
resolution of the actual squared resolvent produces exactly the actual
canonical `2 log(1+A)` operator, including its maximal domain. -/
theorem laguerre_canonical_negative_log_j :
    integerBasisMultiplier laguerreHilbertBasis
        (fun n : ℕ => ((-Real.log (canonicalJCoordinate n) : ℝ) : ℂ)) =
      laguerreSpectralOperator gammaLaplaceExponent := by
  apply LinearPMap.ext
  · ext x
    change Memℓp (fun n : ℕ => ((-Real.log (canonicalJCoordinate n) : ℝ) : ℂ) *
        laguerreHilbertBasis.repr x n) 2 ↔
      Memℓp (fun n : ℕ => (gammaLaplaceExponent n : ℂ) * laguerreHilbertBasis.repr x n) 2
    simp only [canonical_j_negative_log]
  · intro x y hxy
    apply laguerreHilbertBasis.repr.injective
    apply lp.ext
    funext n
    rw [integer_basis_multiplier_coordinate, laguerre_spectral_coordinate,
      canonical_j_negative_log, hxy]

theorem laguerre_canonical_negative_log_j_selfAdjoint :
    IsSelfAdjoint (integerBasisMultiplier laguerreHilbertBasis
      (fun n : ℕ => ((-Real.log (canonicalJCoordinate n) : ℝ) : ℂ))) := by
  rw [laguerre_canonical_negative_log_j]
  exact laguerre_spectral_selfAdjoint _

/-- The exact logarithmic domain; in particular no inverse image domain of
an algebraic composition of partially defined operators is used. -/
theorem laguerre_canonical_negative_log_j_domain (x : LaguerreWeightedHilbert) :
    x ∈ (integerBasisMultiplier laguerreHilbertBasis
      (fun n : ℕ => ((-Real.log (canonicalJCoordinate n) : ℝ) : ℂ))).domain ↔
      Summable (fun n : ℕ => (2 * Real.log (1 + (n : ℝ)))^2 *
        ‖laguerreHilbertBasis.repr x n‖^2) := by
  rw [integer_basis_multiplier_domain_iff]
  simp only [canonical_j_negative_log, gammaLaplaceExponent, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

theorem laguerre_canonical_negative_log_j_action
    (x : (integerBasisMultiplier laguerreHilbertBasis
      (fun n : ℕ => ((-Real.log (canonicalJCoordinate n) : ℝ) : ℂ))).domain) (n : ℕ) :
    laguerreHilbertBasis.repr
      (integerBasisMultiplier laguerreHilbertBasis
        (fun n : ℕ => ((-Real.log (canonicalJCoordinate n) : ℝ) : ℂ)) x) n =
      ((2 * Real.log (1 + (n : ℝ)) : ℝ) : ℂ) * laguerreHilbertBasis.repr x.val n := by
  rw [integer_basis_multiplier_coordinate, canonical_j_negative_log]
  rfl

/-- Any native self-adjoint realization of `-log J(A)` in the proved
complete spectral resolution of the actual bounded `J(A)` is the entire
canonical exponent operator, not merely its finite-span restriction. -/
theorem laguerre_canonical_exponent_determined_by_j
    (C : LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert)
    (hC : IsSelfAdjoint C)
    (hdom : ∀ n : ℕ, laguerreHilbertBasis n ∈ C.domain)
    (hact : ∀ n : ℕ, C ⟨laguerreHilbertBasis n, hdom n⟩ =
      ((-Real.log ((@inner ℂ LaguerreWeightedHilbert _ (laguerreHilbertBasis n)
        (laguerreSquaredResolvent 1 zero_lt_one (laguerreHilbertBasis n))).re) : ℝ) : ℂ) •
          laguerreHilbertBasis n) :
    C = laguerreSpectralOperator gammaLaplaceExponent := by
  apply laguerre_selfAdjoint_eq_spectral_of_basis _ C hC hdom
  intro n
  rw [hact, laguerre_canonical_j_spectral_value, canonical_j_negative_log]

/-- Changing the arbitrary value assigned to `-log` at the unattained
endpoint zero does not alter the native operator or its full domain. -/
theorem laguerre_canonical_j_log_endpoint_independent (g h : ℝ → ℝ)
    (hgh : ∀ t : ℝ, 0 < t → g t = h t) :
    integerBasisMultiplier laguerreHilbertBasis (fun n => (g (canonicalJCoordinate n) : ℂ)) =
      integerBasisMultiplier laguerreHilbertBasis (fun n => (h (canonicalJCoordinate n) : ℂ)) := by
  have he : (fun n => (g (canonicalJCoordinate n) : ℂ)) =
      fun n => (h (canonicalJCoordinate n) : ℂ) := by
    funext n
    rw [hgh _ (canonical_j_coordinate_pos n)]
  rw [he]

/-- Exponentiating the negative complete canonical exponent gives back the
actual bounded squared resolvent on every vector. -/
theorem laguerre_canonical_exp_negative_log :
    laguerreSpectralOperator (fun t => Real.exp (-gammaLaplaceExponent t)) =
      (laguerreSquaredResolvent 1 zero_lt_one).toLinearMap.toPMap ⊤ := by
  apply LinearPMap.ext
  · apply top_unique
    intro x _
    change Memℓp (fun n : ℕ => (Real.exp (-gammaLaplaceExponent n) : ℂ) *
      laguerreHilbertBasis.repr x n) 2
    have he : (fun n : ℕ => (Real.exp (-gammaLaplaceExponent n) : ℂ) *
        laguerreHilbertBasis.repr x n) =
        fun n => laguerreHilbertBasis.repr (laguerreSquaredResolvent 1 zero_lt_one x) n := by
      funext n
      rw [laguerre_canonical_j_coordinate, canonical_j_exp_negative_exponent]
    rw [he]
    exact (laguerreHilbertBasis.repr _).property
  · intro x y hxy
    apply laguerreHilbertBasis.repr.injective
    apply lp.ext
    funext n
    change laguerreHilbertBasis.repr
        (laguerreSpectralOperator (fun t => Real.exp (-gammaLaplaceExponent t)) x) n =
      laguerreHilbertBasis.repr (laguerreSquaredResolvent 1 zero_lt_one y.val) n
    rw [laguerre_spectral_coordinate, laguerre_canonical_j_coordinate,
      canonical_j_exp_negative_exponent, hxy]

/-- Conversely, the full native exponent determines the actual bounded
squared resolvent by the known Borel function `exp(-t)`. The scalar in the
premise is read from the actual unbounded exponent's basis action. -/
theorem laguerre_canonical_j_determined_by_exponent
    (J : LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert)
    (hact : ∀ n : ℕ, J (laguerreHilbertBasis n) =
      (Real.exp (-(@inner ℂ LaguerreWeightedHilbert _ (laguerreHilbertBasis n)
        (laguerreSpectralOperator gammaLaplaceExponent
          ⟨laguerreHilbertBasis n,
            laguerre_basis_mem_spectral_domain gammaLaplaceExponent n⟩)).re) : ℂ) •
          laguerreHilbertBasis n) :
    J = laguerreSquaredResolvent 1 zero_lt_one := by
  have he (n : ℕ) : J (laguerreHilbertBasis n) =
      laguerreSquaredResolvent 1 zero_lt_one (laguerreHilbertBasis n) := by
    rw [hact, laguerre_spectral_basis_action, inner_smul_right,
      ← laguerreHilbertBasis.repr_apply_apply, laguerreHilbertBasis.repr_self,
      lp.single_apply_self, mul_one, Complex.ofReal_re,
      canonical_j_exp_negative_exponent, laguerre_canonical_j_basis_action]
  apply ContinuousLinearMap.ext
  intro x
  have hleft := J.hasSum (laguerreHilbertBasis.hasSum_repr x)
  have hright := (laguerreSquaredResolvent 1 zero_lt_one).hasSum
    (laguerreHilbertBasis.hasSum_repr x)
  simp only [map_smul, he] at hleft hright
  exact hleft.unique hright

end
end Sigma
