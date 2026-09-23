import SigmaOpZetaTrace

namespace Sigma
noncomputable section

def integerHeatMultiplier (τ : ℂ) (n : ℕ) : ℂ := Complex.exp (-τ * n)

theorem integer_heat_multiplier_norm_summable_iff (τ : ℂ) :
    Summable (fun n => ‖integerHeatMultiplier τ n‖) ↔ 0 < τ.re := by
  rw [summable_norm_iff]
  exact operator_complex_heat_eigenvalue_summable_iff τ

theorem integer_heat_multiplier_bounded (τ : ℂ) (hτ : 0 ≤ τ.re) (n : ℕ) :
    ‖integerHeatMultiplier τ n‖ ≤ 1 := by
  rw [integerHeatMultiplier, Complex.norm_eq_abs, Complex.abs_exp, Real.exp_le_one_iff]
  simp only [Complex.mul_re, Complex.neg_re, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hτ) (Nat.cast_nonneg n)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The maximal complex heat multiplier, with its full weighted square-summable domain. -/
def integerHeatOperator (b : HilbertBasis ℕ ℂ H) (τ : ℂ) : H →ₗ.[ℂ] H :=
  integerBasisMultiplier b (integerHeatMultiplier τ)

def integerHeatBoundedOperator (b : HilbertBasis ℕ ℂ H) (τ : ℂ) (hτ : 0 ≤ τ.re) :
    H →L[ℂ] H := integerBasisBoundedMultiplier b (integerHeatMultiplier τ) 1
      (by norm_num) (integer_heat_multiplier_bounded τ hτ)

omit [CompleteSpace H] in
theorem integer_heat_bounded_eq (b : HilbertBasis ℕ ℂ H) (τ : ℂ) (hτ : 0 ≤ τ.re) :
    integerHeatOperator b τ = (integerHeatBoundedOperator b τ hτ).toLinearMap.toPMap ⊤ :=
  integer_basis_bounded_multiplier_eq _ _ _ _ _

omit [CompleteSpace H] in
theorem integer_heat_bounded_basis_action (b : HilbertBasis ℕ ℂ H) (τ : ℂ)
    (hτ : 0 ≤ τ.re) (n : ℕ) :
    integerHeatBoundedOperator b τ hτ (b n) = integerHeatMultiplier τ n • b n :=
  integer_basis_bounded_multiplier_basis_action _ _ _ _ _ _

theorem integer_heat_bounded_nuclear (b : HilbertBasis ℕ ℂ H) (τ : ℂ) (hτ : 0 < τ.re) :
    IsNuclearOperator (integerHeatBoundedOperator b τ hτ.le) := by
  exact diagonal_operator_nuclear_of_summable b _ _
    (integer_heat_bounded_basis_action b τ _) ((integer_heat_multiplier_norm_summable_iff τ).mpr hτ)

/-- Exact trace-class range, without any boundedness assumption on the complex time. -/
theorem integer_heat_operator_nuclear_iff (b : HilbertBasis ℕ ℂ H) (τ : ℂ) :
    IsNuclearPartialOperator (integerHeatOperator b τ) ↔ 0 < τ.re := by
  constructor
  · rintro ⟨T, hT, he⟩
    have hact (n : ℕ) : T (b n) = integerHeatMultiplier τ n • b n := by
      have hv := he.le.2
        (x := ⟨b n, integer_basis_mem_multiplier_domain b _ n⟩)
        (y := ⟨b n, Submodule.mem_top⟩) rfl
      change integerBasisMultiplier b (integerHeatMultiplier τ)
        ⟨b n, integer_basis_mem_multiplier_domain b _ n⟩ = T (b n) at hv
      exact hv.symm.trans (integer_basis_multiplier_basis_action b _ n)
    exact (integer_heat_multiplier_norm_summable_iff τ).mp
      ((diagonal_operator_nuclear_iff b T _ hact).mp hT)
  · intro hτ
    exact ⟨integerHeatBoundedOperator b τ hτ.le,
      integer_heat_bounded_nuclear b τ hτ, integer_heat_bounded_eq b τ _⟩

theorem integer_heat_operator_trace (b : HilbertBasis ℕ ℂ H) (τ : ℂ) (hτ : 0 < τ.re) :
    nuclearTrace (integerHeatBoundedOperator b τ hτ.le)
      (integer_heat_bounded_nuclear b τ hτ) = (1 - Complex.exp (-τ))⁻¹ := by
  rw [diagonal_operator_nuclear_trace b _ _ (integer_heat_bounded_basis_action b τ _)]
  exact (operator_complex_heat_eigenvalue_hasSum hτ).tsum_eq

theorem integer_heat_trace_any_basis (b c : HilbertBasis ℕ ℂ H) (τ : ℂ)
    (hτ : 0 < τ.re) :
    hilbertBasisTrace c (integerHeatBoundedOperator b τ hτ.le) =
      (1 - Complex.exp (-τ))⁻¹ := by
  rw [← nuclear_trace_basis_independent b c (integer_heat_bounded_nuclear b τ hτ)]
  rw [diagonal_operator_trace b _ _ (integer_heat_bounded_basis_action b τ _)]
  exact (operator_complex_heat_eigenvalue_hasSum hτ).tsum_eq

/-- Supplied native self-adjoint operators with the complete integer eigenbasis
have the same maximal generator and the genuine complex heat traces. -/
theorem integer_eigenbasis_heat_trace (b : HilbertBasis ℕ ℂ H)
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hdom : ∀ n : ℕ, b n ∈ A.domain)
    (ha : ∀ n : ℕ, A ⟨b n, hdom n⟩ = (n : ℂ) • b n) :
    A = integerBasisMultiplier b (fun n => (n : ℂ)) ∧
    (∀ τ : ℂ, IsNuclearPartialOperator (integerHeatOperator b τ) ↔ 0 < τ.re) ∧
    (∀ (τ : ℂ) (hτ : 0 < τ.re),
      nuclearTrace (integerHeatBoundedOperator b τ hτ.le)
        (integer_heat_bounded_nuclear b τ hτ) = (1 - Complex.exp (-τ))⁻¹) :=
  ⟨integer_eigenbasis_operator_eq b A hA hdom ha,
    integer_heat_operator_nuclear_iff b, integer_heat_operator_trace b⟩

/-- O4's actual Gamma-weighted Laguerre realization, including its exact domain. -/
theorem laguerre_complex_heat_trace :
    laguerreSpectralOperator id =
      integerBasisMultiplier laguerreHilbertBasis (fun n => (n : ℂ)) ∧
    (∀ τ : ℂ, IsNuclearPartialOperator (integerHeatOperator laguerreHilbertBasis τ) ↔
      0 < τ.re) ∧
    (∀ (τ : ℂ) (hτ : 0 < τ.re),
      nuclearTrace (integerHeatBoundedOperator laguerreHilbertBasis τ hτ.le)
        (integer_heat_bounded_nuclear laguerreHilbertBasis τ hτ) =
          (1 - Complex.exp (-τ))⁻¹) := by
  apply integer_eigenbasis_heat_trace laguerreHilbertBasis (laguerreSpectralOperator id)
    (laguerre_spectral_selfAdjoint id) (laguerre_basis_mem_spectral_domain id)
  intro n
  simpa using laguerre_spectral_basis_action id n

end
end Sigma
