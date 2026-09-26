import SigmaOpDeterminantCategory
import SigmaOpDeterminantLerch

namespace Sigma
noncomputable section

/-- The canonical maximal Laguerre operator belongs to both shifted determinant classes. -/
def laguerreNativeDeterminantClass : NativeShiftedDeterminantClass laguerreCanonicalOperator where
  selfadjoint := laguerre_canonical_selfAdjoint
  nonnegative := by
    intro x
    have hx := laguerre_canonical_eq_spectral.le.1 x.property
    have he := laguerre_canonical_eq_spectral.le.2 (show x.val = (⟨x.val, hx⟩ :
      (laguerreSpectralOperator id).domain).val from rfl)
    rw [he]
    exact laguerre_spectral_nonnegative id (fun n => Nat.cast_nonneg n) ⟨x.val, hx⟩
  resolvent := laguerreResolvent 1 (by norm_num)
  inverse := laguerre_canonical_positive_shift_resolvent 1 (by norm_num)
  nuclear_square := by
    simpa only [pow_two, ContinuousLinearMap.mul_def, laguerreSquaredResolvent] using
      laguerre_squared_resolvent_nuclear 1 (by norm_num)

theorem laguerre_native_determinant_spectral (reg : Bool) :
    nativeShiftedDeterminant laguerreNativeDeterminantClass reg =
      shiftedSpectralDeterminant reg (fun n : ℕ => (n : ℝ)) := by
  exact native_shifted_determinant_eq_spectral _ reg laguerreHilbertBasis _
    (fun n => Nat.cast_nonneg n) laguerre_basis_mem_canonical_domain laguerre_canonical_basis_action

theorem laguerre_native_fredholm_determinant :
    nativeShiftedDeterminant laguerreNativeDeterminantClass false = laguerreFredholmDeterminant := by
  rw [laguerre_native_determinant_spectral]
  exact funext laguerre_spectral_fredholm_determinant

theorem laguerre_native_regularized_determinant :
    nativeShiftedDeterminant laguerreNativeDeterminantClass true = laguerreRegularizedDeterminant := by
  rw [laguerre_native_determinant_spectral]
  exact funext laguerre_spectral_regularized_determinant

/-- The ordinary determinant of the native squared resolvent is the entire sinh
power series; in particular it has value one at zero and is branch independent. -/
theorem laguerre_native_fredholm_series (z : ℂ) :
    nativeShiftedDeterminant laguerreNativeDeterminantClass false z = laguerreFredholmSeries z := by
  rw [laguerre_native_fredholm_determinant, laguerre_fredholm_determinant_series]

theorem laguerre_native_fredholm_sqrt (w : ℂ) (hw : w ≠ 0) :
    nativeShiftedDeterminant laguerreNativeDeterminantClass false (w^2) =
      Complex.sinh ((Real.pi : ℂ)*w) / ((Real.pi : ℂ)*w) := by
  rw [laguerre_native_fredholm_determinant]
  exact laguerre_fredholm_determinant_sqrt w hw

/-- The regularized native first resolvent determinant with its exact exponential
normalization, valid also at the zeros of reciprocal Gamma. -/
theorem laguerre_native_regularized_gamma (z : ℂ) :
    nativeShiftedDeterminant laguerreNativeDeterminantClass true z =
      Complex.exp (-(Real.eulerMascheroniConstant : ℂ)*z) / Complex.Gamma (1+z) := by
  rw [laguerre_native_regularized_determinant, laguerre_regularized_determinant_gamma]

/-- Either native determinant zero multiset recovers the full canonical generator,
including its operator domain, against every competitor in the shifted category. -/
theorem laguerre_native_determinant_reconstruction
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {B : H →ₗ.[ℂ] H} (hB : NativeShiftedDeterminantClass B) (reg : Bool)
    (hzeros : ∀ z : ℂ,
      (native_shifted_determinant_entire laguerreNativeDeterminantClass reg z).order =
      (native_shifted_determinant_entire hB reg z).order) :
    ∃ U : LaguerreWeightedHilbert ≃ₗᵢ[ℂ] H,
      (∀ x, U x ∈ B.domain ↔ x ∈ laguerreCanonicalOperator.domain) ∧
      (∀ (x : laguerreCanonicalOperator.domain) (y : B.domain),
        U x.val = y.val → U (laguerreCanonicalOperator x) = B y) :=
  native_shifted_determinant_zero_multiset_unique laguerreNativeDeterminantClass hB reg hzeros

end
end Sigma
