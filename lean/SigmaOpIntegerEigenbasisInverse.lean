import SigmaOpIntegerEigenbasis
import SigmaOpResolvent

namespace Sigma
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem integer_shift_reciprocal_bound (n : ℕ) : ‖((n : ℂ)+1)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  apply inv_le_one_of_one_le₀
  have hn : ((n : ℂ)+1) = ((n+1 : ℕ) : ℂ) := by push_cast; rfl
  rw [hn, Complex.norm_natCast]
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

def integerBasisShiftInverse (b : HilbertBasis ℕ ℂ H) : H →L[ℂ] H :=
  integerBasisBoundedMultiplier b (fun n => ((n : ℂ)+1)⁻¹) 1 zero_le_one
    integer_shift_reciprocal_bound

theorem integer_basis_shift_inverse_coordinate (b : HilbertBasis ℕ ℂ H) (x : H) (n : ℕ) :
    b.repr (integerBasisShiftInverse b x) n = ((n : ℂ)+1)⁻¹*b.repr x n :=
  integer_basis_bounded_multiplier_coordinate _ _ _ _ _ _ _

theorem integer_basis_shift_inverse_mem (b : HilbertBasis ℕ ℂ H) (x : H) :
    integerBasisShiftInverse b x ∈ (integerBasisMultiplier b (fun n => (n : ℂ))).domain := by
  change Memℓp (fun n : ℕ => (n : ℂ)*b.repr (integerBasisShiftInverse b x) n) 2
  have he : (fun n : ℕ => (n : ℂ)*b.repr (integerBasisShiftInverse b x) n) =
      fun n => b.repr (x-integerBasisShiftInverse b x) n := by
    funext n
    simp only [map_sub, lp.coeFn_sub, Pi.sub_apply, integer_basis_shift_inverse_coordinate]
    have hn : (n : ℂ)+1 ≠ 0 := by
      have : (0 : ℝ) < (n : ℝ)+1 := by positivity
      exact_mod_cast this.ne'
    field_simp
    ring
  rw [he]
  exact (b.repr (x-integerBasisShiftInverse b x)).property

theorem integer_basis_shift_inverse_resolvent (b : HilbertBasis ℕ ℂ H) :
    OpIsResolvent (integerBasisMultiplier b (fun n => (n : ℂ))) 1 (integerBasisShiftInverse b) := by
  refine ⟨integer_basis_shift_inverse_mem b, ?_, ?_⟩
  · intro x
    apply b.repr.injective
    apply lp.ext
    funext n
    simp only [map_add, one_smul, lp.coeFn_add, Pi.add_apply,
      integer_basis_multiplier_coordinate, integer_basis_shift_inverse_coordinate]
    have hn : (n : ℂ)+1 ≠ 0 := by
      have : (0 : ℝ) < (n : ℝ)+1 := by positivity
      exact_mod_cast this.ne'
    field_simp
    ring
  · intro x
    apply b.repr.injective
    apply lp.ext
    funext n
    simp only [integer_basis_shift_inverse_coordinate, map_add, one_smul,
      lp.coeFn_add, Pi.add_apply, integer_basis_multiplier_coordinate]
    have hn : (n : ℂ)+1 ≠ 0 := by
      have : (0 : ℝ) < (n : ℝ)+1 := by positivity
      exact_mod_cast this.ne'
    field_simp
    ring

/-- The reciprocal spectral multiplier is the genuine two-sided bounded
inverse of `1+A` for the supplied operator, not a separately chosen recipe. -/
theorem integer_eigenbasis_shift_inverse [CompleteSpace H] (b : HilbertBasis ℕ ℂ H)
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hdom : ∀ n : ℕ, b n ∈ A.domain)
    (ha : ∀ n : ℕ, A ⟨b n, hdom n⟩ = (n : ℂ) • b n) :
    OpIsResolvent A 1 (integerBasisShiftInverse b) := by
  rw [integer_eigenbasis_operator_eq b A hA hdom ha]
  exact integer_basis_shift_inverse_resolvent b

end
end Sigma
