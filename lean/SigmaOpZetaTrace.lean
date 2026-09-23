import SigmaOpSpectral
import SigmaOpDiagonalNuclear
import SigmaOpIntegerEigenbasisInverse

namespace Sigma
noncomputable section
open scoped Topology

def integerZetaMultiplier (s : ℂ) (n : ℕ) : ℂ := 1 / (n+1 : ℂ)^s

theorem integer_zeta_multiplier_norm (s : ℂ) (n : ℕ) :
    ‖integerZetaMultiplier s n‖ = 1 / (n+1 : ℝ)^s.re := by
  have hp : (0 : ℝ) < n+1 := by positivity
  rw [integerZetaMultiplier, norm_div, norm_one, Complex.norm_eq_abs]
  have he : (n+1 : ℂ) = ((n+1 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.abs_cpow_eq_rpow_re_of_pos hp]

theorem integer_zeta_multiplier_norm_summable_iff (s : ℂ) :
    Summable (fun n => ‖integerZetaMultiplier s n‖) ↔ 1 < s.re := by
  simp_rw [integer_zeta_multiplier_norm]
  exact operator_shifted_real_eigenvalue_summable_iff 1 s.re (by norm_num)

theorem integer_zeta_multiplier_bounded (s : ℂ) (hs : 0 ≤ s.re) (n : ℕ) :
    ‖integerZetaMultiplier s n‖ ≤ 1 := by
  rw [integer_zeta_multiplier_norm]
  have hp : (0 : ℝ) < n+1 := by positivity
  apply (div_le_one (Real.rpow_pos_of_pos hp _)).mpr
  exact Real.one_le_rpow (by have := Nat.cast_nonneg (α := ℝ) n; linarith) hs

theorem integer_zeta_multiplier_hasSum (s : ℂ) (hs : 1 < s.re) :
    HasSum (integerZetaMultiplier s) (riemannZeta s) :=
  operator_zeta_eigenvalue_hasSum hs

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Trace-class for an actual partial operator requires equality, including its
entire domain, to a nuclear bounded operator. An unbounded multiplier cannot
satisfy this condition merely by having selected summable coefficients. -/
def IsNuclearPartialOperator (A : H →ₗ.[ℂ] H) : Prop :=
  ∃ T : H →L[ℂ] H, IsNuclearOperator T ∧ A = T.toLinearMap.toPMap ⊤

/-- Pure-point spectral `(1+A)^(-s)`, on its exact maximal domain in the
supplied complete integer eigenbasis. -/
def integerZetaOperator (b : HilbertBasis ℕ ℂ H) (s : ℂ) : H →ₗ.[ℂ] H :=
  integerBasisMultiplier b (integerZetaMultiplier s)

def integerZetaBoundedOperator (b : HilbertBasis ℕ ℂ H) (s : ℂ) (hs : 0 ≤ s.re) :
    H →L[ℂ] H := integerBasisBoundedMultiplier b (integerZetaMultiplier s) 1
      (by norm_num) (integer_zeta_multiplier_bounded s hs)

omit [CompleteSpace H] in
theorem integer_zeta_bounded_eq (b : HilbertBasis ℕ ℂ H) (s : ℂ) (hs : 0 ≤ s.re) :
    integerZetaOperator b s = (integerZetaBoundedOperator b s hs).toLinearMap.toPMap ⊤ :=
  integer_basis_bounded_multiplier_eq _ _ _ _ _

omit [CompleteSpace H] in
theorem integer_zeta_bounded_basis_action (b : HilbertBasis ℕ ℂ H) (s : ℂ)
    (hs : 0 ≤ s.re) (n : ℕ) :
    integerZetaBoundedOperator b s hs (b n) = integerZetaMultiplier s n • b n :=
  integer_basis_bounded_multiplier_basis_action _ _ _ _ _ _

theorem integer_zeta_bounded_nuclear (b : HilbertBasis ℕ ℂ H) (s : ℂ) (hs : 1 < s.re) :
    IsNuclearOperator (integerZetaBoundedOperator b s (le_trans zero_le_one hs.le)) := by
  exact diagonal_operator_nuclear_of_summable b _ _
    (integer_zeta_bounded_basis_action b s _) ((integer_zeta_multiplier_norm_summable_iff s).mpr hs)

/-- Exact trace-class domain, including exclusion of all parameters where the
maximal complex power is unbounded. No boundedness premise is imposed on s. -/
theorem integer_zeta_operator_nuclear_iff (b : HilbertBasis ℕ ℂ H) (s : ℂ) :
    IsNuclearPartialOperator (integerZetaOperator b s) ↔ 1 < s.re := by
  constructor
  · rintro ⟨T, hT, he⟩
    have hact (n : ℕ) : T (b n) = integerZetaMultiplier s n • b n := by
      have hv := he.le.2
        (x := ⟨b n, integer_basis_mem_multiplier_domain b _ n⟩)
        (y := ⟨b n, Submodule.mem_top⟩) rfl
      change integerBasisMultiplier b (integerZetaMultiplier s)
        ⟨b n, integer_basis_mem_multiplier_domain b _ n⟩ = T (b n) at hv
      calc
        _ = integerBasisMultiplier b (integerZetaMultiplier s)
            ⟨b n, integer_basis_mem_multiplier_domain b _ n⟩ := hv.symm
        _ = _ := integer_basis_multiplier_basis_action b _ n
    exact (integer_zeta_multiplier_norm_summable_iff s).mp
      ((diagonal_operator_nuclear_iff b T _ hact).mp hT)
  · intro hs
    exact ⟨integerZetaBoundedOperator b s (le_trans zero_le_one hs.le),
      integer_zeta_bounded_nuclear b s hs, integer_zeta_bounded_eq b s _⟩

theorem integer_zeta_operator_trace (b : HilbertBasis ℕ ℂ H) (s : ℂ) (hs : 1 < s.re) :
    nuclearTrace (integerZetaBoundedOperator b s (le_trans zero_le_one hs.le))
      (integer_zeta_bounded_nuclear b s hs) = riemannZeta s := by
  rw [diagonal_operator_nuclear_trace b _ _ (integer_zeta_bounded_basis_action b s _)]
  exact (integer_zeta_multiplier_hasSum s hs).tsum_eq

omit [CompleteSpace H] in
theorem integer_zeta_one_eq_shift_inverse (b : HilbertBasis ℕ ℂ H) :
    integerZetaBoundedOperator b 1 (by norm_num) = integerBasisShiftInverse b := by
  ext x
  apply b.repr.injective
  apply lp.ext
  funext n
  rw [integer_basis_shift_inverse_coordinate]
  change b.repr (integerBasisBoundedMultiplier b (integerZetaMultiplier 1) 1 _ _ x) n = _
  rw [integer_basis_bounded_multiplier_coordinate]
  simp [integerZetaMultiplier]

theorem integer_zeta_trace_any_basis (b c : HilbertBasis ℕ ℂ H) (s : ℂ)
    (hs : 1 < s.re) :
    hilbertBasisTrace c (integerZetaBoundedOperator b s (le_trans zero_le_one hs.le)) =
      riemannZeta s := by
  rw [← nuclear_trace_basis_independent b c (integer_zeta_bounded_nuclear b s hs)]
  rw [diagonal_operator_trace b _ _ (integer_zeta_bounded_basis_action b s _)]
  exact (integer_zeta_multiplier_hasSum s hs).tsum_eq

/-- B4's actual supplied-operator clause. Native self-adjointness and the complete
simple eigenbasis derive the exact diagonal realization and its inverse anchor;
the resulting maximal complex powers have the stated exact trace-class range
and genuine, basis-independent operator trace. -/
theorem integer_eigenbasis_zeta_trace (b : HilbertBasis ℕ ℂ H)
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hdom : ∀ n : ℕ, b n ∈ A.domain)
    (ha : ∀ n : ℕ, A ⟨b n, hdom n⟩ = (n : ℂ) • b n) :
    A = integerBasisMultiplier b (fun n => (n : ℂ)) ∧
    OpIsResolvent A 1 (integerZetaBoundedOperator b 1 (by norm_num)) ∧
    (∀ s : ℂ, IsNuclearPartialOperator (integerZetaOperator b s) ↔ 1 < s.re) ∧
    (∀ (s : ℂ) (hs : 1 < s.re),
      nuclearTrace (integerZetaBoundedOperator b s (le_trans zero_le_one hs.le))
        (integer_zeta_bounded_nuclear b s hs) = riemannZeta s) := by
  refine ⟨integer_eigenbasis_operator_eq b A hA hdom ha, ?_,
    integer_zeta_operator_nuclear_iff b, integer_zeta_operator_trace b⟩
  rw [integer_zeta_one_eq_shift_inverse]
  exact integer_eigenbasis_shift_inverse b A hA hdom ha

end
end Sigma
