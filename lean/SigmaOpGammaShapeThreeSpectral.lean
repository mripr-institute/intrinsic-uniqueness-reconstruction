import SigmaOpGammaShapeThreeComplete
import SigmaOpIntegerBasisEquivalence
import SigmaOpCanonicalClosure

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

/-- Maximal spectral operator on the actual Gamma-three weighted L².
Its identification with the compact-test differential closure is separate. -/
def gammaShapeThreeSpectralOperator :
    GammaShapeThreeWeightedHilbert →ₗ.[ℂ] GammaShapeThreeWeightedHilbert :=
  integerBasisMultiplier gammaShapeThreeHilbertBasis (fun n => (n : ℂ))

theorem gamma_shape_three_spectral_coordinate
    (x : gammaShapeThreeSpectralOperator.domain) (n : ℕ) :
    gammaShapeThreeHilbertBasis.repr (gammaShapeThreeSpectralOperator x) n =
      (n : ℂ) * gammaShapeThreeHilbertBasis.repr x.val n :=
  integer_basis_multiplier_coordinate _ _ x n

theorem gamma_shape_three_spectral_domain_iff (x : GammaShapeThreeWeightedHilbert) :
    x ∈ gammaShapeThreeSpectralOperator.domain ↔
      Summable (fun n : ℕ => (n : ℝ)^2 * ‖gammaShapeThreeHilbertBasis.repr x n‖^2) := by
  rw [gammaShapeThreeSpectralOperator, integer_basis_multiplier_domain_iff]
  simp only [Complex.norm_natCast]

theorem gamma_shape_three_spectral_selfAdjoint :
    IsSelfAdjoint gammaShapeThreeSpectralOperator :=
  integer_basis_real_multiplier_selfAdjoint gammaShapeThreeHilbertBasis
    (fun n => (n : ℝ))

theorem gamma_shape_three_spectral_closed : gammaShapeThreeSpectralOperator.IsClosed :=
  integer_basis_multiplier_closed _ _

theorem gamma_shape_three_spectral_nonnegative : OpNonnegative gammaShapeThreeSpectralOperator :=
  integer_basis_real_multiplier_nonnegative gammaShapeThreeHilbertBasis
    (fun n => (n : ℝ)) (fun n => Nat.cast_nonneg n)

theorem gamma_shape_three_basis_mem_spectral_domain (n : ℕ) :
    gammaShapeThreeHilbertBasis n ∈ gammaShapeThreeSpectralOperator.domain :=
  integer_basis_mem_multiplier_domain _ _ n

theorem gamma_shape_three_spectral_basis_action (n : ℕ) :
    gammaShapeThreeSpectralOperator
      ⟨gammaShapeThreeHilbertBasis n, gamma_shape_three_basis_mem_spectral_domain n⟩ =
      (n : ℂ) • gammaShapeThreeHilbertBasis n :=
  integer_basis_multiplier_basis_action _ _ n

theorem gamma_shape_three_spectral_domain_dense :
    Dense (gammaShapeThreeSpectralOperator.domain : Set GammaShapeThreeWeightedHilbert) :=
  integer_basis_multiplier_domain_dense _ _

theorem gamma_shape_three_spectral_action_hasSum (x : gammaShapeThreeSpectralOperator.domain) :
    HasSum (fun n : ℕ => ((n : ℂ) * gammaShapeThreeHilbertBasis.repr x.val n) •
      gammaShapeThreeHilbertBasis n) (gammaShapeThreeSpectralOperator x) := by
  have h := gammaShapeThreeHilbertBasis.hasSum_repr (gammaShapeThreeSpectralOperator x)
  simpa only [gamma_shape_three_spectral_coordinate] using h

theorem gamma_shape_three_integer_eigenvector_line (n : ℕ)
    (x : gammaShapeThreeSpectralOperator.domain)
    (hx : gammaShapeThreeSpectralOperator x = (n : ℂ) • x.val) :
    x.val = gammaShapeThreeHilbertBasis.repr x.val n • gammaShapeThreeHilbertBasis n := by
  apply gammaShapeThreeHilbertBasis.repr.injective
  apply lp.ext
  funext k
  rw [_root_.map_smul, gammaShapeThreeHilbertBasis.repr_self]
  change gammaShapeThreeHilbertBasis.repr x.val k =
    gammaShapeThreeHilbertBasis.repr x.val n *
      (lp.single (E := fun _ : ℕ => ℂ) 2 n (1 : ℂ)) k
  by_cases hk : k = n
  · subst k
    simp only [lp.single_apply_self, mul_one]
  · rw [lp.single_apply_ne _ _ _ hk, mul_zero]
    have hc := congrArg (fun y => gammaShapeThreeHilbertBasis.repr y k) hx
    dsimp only at hc
    rw [gamma_shape_three_spectral_coordinate, _root_.map_smul] at hc
    have hkn : (k : ℂ) ≠ (n : ℂ) := by exact_mod_cast hk
    exact (mul_eq_mul_right_iff.mp hc).resolve_left hkn

theorem laguerre_spectral_eq_integer_basis :
    laguerreSpectralOperator id =
      integerBasisMultiplier laguerreHilbertBasis (fun n => (n : ℂ)) :=
  integer_eigenbasis_operator_eq laguerreHilbertBasis _ (laguerre_spectral_selfAdjoint id)
    (laguerre_basis_mem_spectral_domain id) (laguerre_spectral_basis_action id)

/-- Matches the normalized modes and thus the actual constant vectors. -/
def gammaShapeUnitary : LaguerreWeightedHilbert ≃ₗᵢ[ℂ] GammaShapeThreeWeightedHilbert :=
  integerBasisUnitary laguerreHilbertBasis gammaShapeThreeHilbertBasis

theorem gamma_shape_unitary_basis (n : ℕ) :
    gammaShapeUnitary (laguerreHilbertBasis n) = gammaShapeThreeHilbertBasis n :=
  integer_basis_unitary_basis _ _ n

theorem gamma_shape_unitary_spectral_domain_iff (x : LaguerreWeightedHilbert) :
    gammaShapeUnitary x ∈ gammaShapeThreeSpectralOperator.domain ↔
      x ∈ laguerreCanonicalOperator.domain := by
  rw [laguerre_canonical_eq_spectral, laguerre_spectral_eq_integer_basis]
  exact integer_basis_unitary_domain_iff _ _ _ x

theorem gamma_shape_unitary_spectral_action (x : laguerreCanonicalOperator.domain) :
    gammaShapeUnitary (laguerreCanonicalOperator x) =
      gammaShapeThreeSpectralOperator ⟨gammaShapeUnitary x.val,
        (gamma_shape_unitary_spectral_domain_iff x.val).mpr x.property⟩ := by
  have he : laguerreCanonicalOperator =
      integerBasisMultiplier laguerreHilbertBasis (fun n => (n : ℂ)) :=
    laguerre_canonical_eq_spectral.trans laguerre_spectral_eq_integer_basis
  have ha : laguerreCanonicalOperator x =
      integerBasisMultiplier laguerreHilbertBasis (fun n => (n : ℂ))
        ⟨x.val, he.le.1 x.property⟩ := he.le.2 rfl
  rw [ha]
  exact integer_basis_unitary_multiplier_action _ _ _ ⟨x.val, he.le.1 x.property⟩

end
end Sigma
