import SigmaOpDeterminantRecovery
import SigmaOpTraceInverse
import SigmaOpCompactResolventBasis

namespace Sigma
noncomputable section
open scoped Topology

def shiftedDeterminantCoefficient (regularized : Bool) (t : ℝ) : ℂ :=
  if regularized then (((1+t)⁻¹ : ℝ) : ℂ) else ((((1+t)⁻¹)^2 : ℝ) : ℂ)

theorem shifted_determinant_coefficient_ne_zero (regularized : Bool) (t : ℝ) (ht : 0 ≤ t) :
    shiftedDeterminantCoefficient regularized t ≠ 0 := by
  have hp : (1+t)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  cases regularized
  · exact Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 hp)
  · exact Complex.ofReal_ne_zero.mpr hp

theorem shifted_determinant_coefficient_injective (regularized : Bool) (t u : ℝ)
    (ht : 0 ≤ t) (hu : 0 ≤ u)
    (he : shiftedDeterminantCoefficient regularized t = shiftedDeterminantCoefficient regularized u) :
    t = u := by
  have ht0 : 0 < (1+t)⁻¹ := inv_pos.mpr (by linarith)
  have hu0 : 0 < (1+u)⁻¹ := inv_pos.mpr (by linarith)
  cases regularized
  · simp only [shiftedDeterminantCoefficient, Bool.false_eq_true, if_false] at he
    have hh : ((1+t)⁻¹)^2 = ((1+u)⁻¹)^2 := by exact_mod_cast he
    have hh' : (1+t)⁻¹ = (1+u)⁻¹ := (sq_eq_sq₀ ht0.le hu0.le).mp hh
    exact add_left_cancel (inv_injective hh')
  · simp only [shiftedDeterminantCoefficient, if_true] at he
    have hh : (1+t)⁻¹ = (1+u)⁻¹ := by exact_mod_cast he
    exact add_left_cancel (inv_injective hh)

def shiftedSpectralDeterminant {ι : Type*} (regularized : Bool) (lam : ι → ℝ) : ℂ → ℂ :=
  spectralDeterminant regularized (fun i => shiftedDeterminantCoefficient regularized (lam i))

variable {ι κ H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Both determinant classes derive their product summability from the same native
trace-class squared shifted resolvent. -/
theorem native_shifted_determinant_summable (regularized : Bool)
    (b : HilbertBasis ι ℂ H) (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (hR : OpIsResolvent A 1 R)
    (hdom : ∀ i, b i ∈ A.domain)
    (ha : ∀ i, A ⟨b i, hdom i⟩ = (lam i : ℂ) • b i)
    (hR2 : IsNuclearOperator (R^2)) :
    Summable (fun i => ‖shiftedDeterminantCoefficient regularized (lam i)‖^
      determinantSummabilityPower regularized) := by
  have hs := nuclear_spectral_power_summable b
    (fun i => reciprocalSpectralCoordinate (lam i) (hlam i)) 2 (R^2)
    (fun i => positive_shift_resolvent_power_eigenvector A R hR ⟨b i, hdom i⟩ _ (hlam i) (ha i) 2) hR2
  have hp (i : ι) : 0 ≤ (1+lam i)⁻¹ := inv_nonneg.mpr (by linarith [hlam i])
  have hs' : Summable (fun i => ((1+lam i)⁻¹)^2) := hs
  cases regularized
  · simpa only [shiftedDeterminantCoefficient, determinantSummabilityPower, Bool.false_eq_true,
      if_false, Complex.norm_real, Real.norm_eq_abs, abs_pow, sq_abs, pow_one] using hs'
  · simpa only [shiftedDeterminantCoefficient, determinantSummabilityPower, if_true,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp _)] using hs'


/-- The spectral determinant of a genuine shifted operator does not depend on its
complete orthonormal eigenbasis, including bases with repeated eigenvalues. -/
theorem native_shifted_determinant_basis_independent (regularized : Bool)
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H)
    (lam : ι → ℝ) (mu : κ → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hmu : ∀ j, 0 ≤ mu j)
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (R : H →L[ℂ] H) (hR : OpIsResolvent A 1 R)
    (hdomA : ∀ i, b i ∈ A.domain) (hdomB : ∀ j, c j ∈ A.domain)
    (ha : ∀ i, A ⟨b i, hdomA i⟩ = (lam i : ℂ) • b i)
    (hb : ∀ j, A ⟨c j, hdomB j⟩ = (mu j : ℂ) • c j)
    (hR2 : IsNuclearOperator (R^2)) :
    shiftedSpectralDeterminant regularized lam = shiftedSpectralDeterminant regularized mu := by
  obtain ⟨e, he, _⟩ := integer_operator_traces_unitary_equivalence b c lam mu hlam hmu
    A A hA hA R R hR hR hdomA hdomB ha hb hR2 hR2 (fun _ => rfl)
  funext z
  have hh := spectral_determinant_reindex regularized
    (fun j => shiftedDeterminantCoefficient regularized (mu j)) e z
  simpa only [Function.comp_def, he, shiftedSpectralDeterminant] using hh

/-- Equality of full analytic zero multisets recovers eigenvalues with multiplicity
and a unitary carrying the entire native generator domains. -/
theorem native_shifted_determinant_zeros_recover_operator (regularized : Bool)
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (lam : ι → ℝ) (mu : κ → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hmu : ∀ j, 0 ≤ mu j)
    (A : H →ₗ.[ℂ] H) (B : K →ₗ.[ℂ] K) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (R : H →L[ℂ] H) (S : K →L[ℂ] K) (hR : OpIsResolvent A 1 R) (hS : OpIsResolvent B 1 S)
    (hdomA : ∀ i, b i ∈ A.domain) (hdomB : ∀ j, c j ∈ B.domain)
    (ha : ∀ i, A ⟨b i, hdomA i⟩ = (lam i : ℂ) • b i)
    (hb : ∀ j, B ⟨c j, hdomB j⟩ = (mu j : ℂ) • c j)
    (hR2 : IsNuclearOperator (R^2)) (hS2 : IsNuclearOperator (S^2))
    (hzeros : ∀ z : ℂ,
      (spectral_determinant_entire regularized _
        (native_shifted_determinant_summable regularized b lam hlam A R hR hdomA ha hR2) z).order =
      (spectral_determinant_entire regularized _
        (native_shifted_determinant_summable regularized c mu hmu B S hS hdomB hb hS2) z).order) :
    ∃ e : ι ≃ κ, (∀ i, mu (e i) = lam i) ∧
      ∃ U : H ≃ₗᵢ[ℂ] K,
        (∀ i, U (b i) = c (e i)) ∧
        (∀ x : H, U x ∈ B.domain ↔ x ∈ A.domain) ∧
        (∀ (x : A.domain) (y : B.domain), U x.val = y.val → U (A x) = B y) := by
  obtain ⟨e, he⟩ := spectral_determinant_zero_multisets_recover regularized
    (fun i => shiftedDeterminantCoefficient regularized (lam i))
    (fun j => shiftedDeterminantCoefficient regularized (mu j))
    (native_shifted_determinant_summable regularized b lam hlam A R hR hdomA ha hR2)
    (native_shifted_determinant_summable regularized c mu hmu B S hS hdomB hb hS2)
    (fun i => shifted_determinant_coefficient_ne_zero regularized _ (hlam i))
    (fun j => shifted_determinant_coefficient_ne_zero regularized _ (hmu j)) hzeros
  have he' : ∀ i, mu (e i) = lam i := fun i =>
    shifted_determinant_coefficient_injective regularized _ _ (hmu (e i)) (hlam i) (he i)
  exact ⟨e, he', real_eigenbasis_unitary_equivalence b c lam mu e he' A B hA hB
    hdomA hdomB ha hb⟩

end
end Sigma
