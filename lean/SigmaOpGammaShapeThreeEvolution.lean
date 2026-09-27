import SigmaOpGammaShapeThreeSpectral
import SigmaOpNonnegativeMixingFinal
import SigmaOpHeatMarkov
import SigmaOpHeatTrace

namespace Sigma
noncomputable section
open MeasureTheory Set
open scoped Topology

def gammaShapeThreeHeat : ℝ →
    GammaShapeThreeWeightedHilbert →L[ℂ] GammaShapeThreeWeightedHilbert :=
  opNonnegativeHeat gammaShapeThreeSpectralOperator
    gamma_shape_three_spectral_selfAdjoint gamma_shape_three_spectral_nonnegative

theorem gamma_shape_three_heat_evolution :
    OpContractionEvolution gammaShapeThreeSpectralOperator gammaShapeThreeHeat :=
  op_nonnegative_heat_evolution _ _ _

theorem gamma_shape_three_heat_semigroup (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    gammaShapeThreeHeat (s+t) = gammaShapeThreeHeat s * gammaShapeThreeHeat t :=
  op_nonnegative_heat_semigroup _ _ _ s t hs ht

theorem gamma_shape_three_heat_basis_action (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    gammaShapeThreeHeat t (gammaShapeThreeHilbertBasis n) =
      (Real.exp (-t * (n : ℝ)) : ℂ) • gammaShapeThreeHilbertBasis n := by
  have h := op_nonnegative_heat_integer_eigenvector gammaShapeThreeSpectralOperator
    gamma_shape_three_spectral_selfAdjoint gamma_shape_three_spectral_nonnegative n
    ⟨gammaShapeThreeHilbertBasis n, gamma_shape_three_basis_mem_spectral_domain n⟩
    (gamma_shape_three_spectral_basis_action n) t ht
  rw [show -(n : ℝ) * t = -t * (n : ℝ) by ring] at h
  exact h.trans (algebraMap_smul ℂ (Real.exp (-t * (n : ℝ))) _).symm

theorem gamma_shape_heat_multiplier_real (t : ℝ) (n : ℕ) :
    integerHeatMultiplier (t : ℂ) n = (Real.exp (-t * (n : ℝ)) : ℂ) := by
  have he : -(t : ℂ) * (n : ℂ) = ((-t * (n : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [integerHeatMultiplier, he, ← Complex.ofReal_exp]

/-- Identifies the exponential constructed from the actual native generator
with the spectral heat multiplier on the complete weighted L² basis. -/
theorem gamma_shape_three_heat_eq_spectral (t : ℝ) (ht : 0 ≤ t) :
    gammaShapeThreeHeat t = integerHeatBoundedOperator gammaShapeThreeHilbertBasis
      (t : ℂ) ht := by
  apply hilbert_basis_operator_ext gammaShapeThreeHilbertBasis
  intro n
  rw [gamma_shape_three_heat_basis_action t ht, integer_heat_bounded_basis_action]
  rw [gamma_shape_heat_multiplier_real]

theorem gamma_shape_three_heat_coordinate (t : ℝ) (ht : 0 ≤ t)
    (f : GammaShapeThreeWeightedHilbert) (n : ℕ) :
    gammaShapeThreeHilbertBasis.repr (gammaShapeThreeHeat t f) n =
      (Real.exp (-t * (n : ℝ)) : ℂ) * gammaShapeThreeHilbertBasis.repr f n := by
  rw [gamma_shape_three_heat_eq_spectral t ht]
  unfold integerHeatBoundedOperator
  rw [integer_basis_bounded_multiplier_coordinate]
  rw [gamma_shape_heat_multiplier_real]

theorem gamma_shape_three_coefficient_zero_integral (f : GammaShapeThreeWeightedHilbert) :
    gammaShapeThreeHilbertBasis.repr f 0 = ∫ t : ℝ, f t ∂gammaShapeThreeProbability := by
  rw [HilbertBasis.repr_apply_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gamma_shape_three_basis_zero_coe] with t ht
  simp [ht, RCLike.inner_apply]

theorem gamma_shape_three_l2_integrable (f : GammaShapeThreeWeightedHilbert) :
    Integrable (fun t : ℝ => f t) gammaShapeThreeProbability :=
  (Lp.memℒp f).integrable (by norm_num)

theorem gamma_shape_three_heat_preserves_one (t : ℝ) (ht : 0 ≤ t) :
    gammaShapeThreeHeat t (gammaShapeThreeHilbertBasis 0) = gammaShapeThreeHilbertBasis 0 := by
  simpa using gamma_shape_three_heat_basis_action t ht 0

/-- Invariance concerns the actual coordinate probability and every weighted
L² input, not just polynomial moments or scalar spectral data. -/
theorem gamma_shape_three_heat_preserves_integral (t : ℝ) (ht : 0 ≤ t)
    (f : GammaShapeThreeWeightedHilbert) :
    (∫ x : ℝ, (gammaShapeThreeHeat t f : ℝ → ℂ) x ∂gammaShapeThreeProbability) =
      ∫ x : ℝ, f x ∂gammaShapeThreeProbability := by
  rw [← gamma_shape_three_coefficient_zero_integral, gamma_shape_three_heat_coordinate t ht]
  simp [gamma_shape_three_coefficient_zero_integral]

theorem gamma_shape_unitary_fixes_one :
    (gammaShapeUnitary (laguerreHilbertBasis 0) : ℝ → ℂ) =ᵐ[gammaShapeThreeProbability]
      fun _ => 1 := by
  rw [gamma_shape_unitary_basis]
  exact gamma_shape_three_basis_zero_coe

theorem gamma_shape_unitary_heat (t : ℝ) (ht : 0 ≤ t) (x : LaguerreWeightedHilbert) :
    gammaShapeUnitary (laguerreHeatOperator t ht x) =
      gammaShapeThreeHeat t (gammaShapeUnitary x) := by
  let S := gammaShapeUnitary.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (laguerreHeatOperator t ht)
  let T := (gammaShapeThreeHeat t).comp
    gammaShapeUnitary.toContinuousLinearEquiv.toContinuousLinearMap
  have he : S = T := by
    apply ContinuousLinearMap.ext
    intro y
    have hs := S.hasSum (laguerreHilbertBasis.hasSum_repr y)
    have ht' := T.hasSum (laguerreHilbertBasis.hasSum_repr y)
    have hm (n : ℕ) : S (laguerreHilbertBasis n) = T (laguerreHilbertBasis n) := by
      dsimp [S, T]
      rw [laguerre_heat_basis_action, _root_.map_smul, gamma_shape_unitary_basis,
        gamma_shape_three_heat_basis_action t ht]
    simp only [_root_.map_smul, hm] at hs ht'
    exact hs.unique ht'
  exact congrArg (fun U => U x) he

def gammaShapeThreeResolventOne :
    GammaShapeThreeWeightedHilbert →L[ℂ] GammaShapeThreeWeightedHilbert :=
  opNonnegativeResolvent gammaShapeThreeSpectralOperator
    gamma_shape_three_spectral_selfAdjoint gamma_shape_three_spectral_nonnegative

theorem gamma_shape_three_gamma_mixing (x : GammaShapeThreeWeightedHilbert) :
    (∫ t : ℝ, gammaShapeThreeHeat t x ∂gammaProbability) =
      gammaShapeThreeResolventOne (gammaShapeThreeResolventOne x) :=
  op_nonnegative_gamma_probability_mixing _ _ _ x

theorem gamma_shape_three_operator_gamma_mixing :
    (∫ t : ℝ in Ioi 0, (t * Real.exp (-t)) • gammaShapeThreeHeat t) =
      gammaShapeThreeResolventOne ^ 2 :=
  op_nonnegative_operator_gamma_mixing _ _ _

theorem gamma_shape_three_complex_mixing_iff (μ : ComplexMeasure OpNonnegativeRay) :
    (∀ x : GammaShapeThreeWeightedHilbert,
      complexStrongIntegral μ (fun s => gammaShapeThreeHeat s.val x) =
        gammaShapeThreeResolventOne (gammaShapeThreeResolventOne x)) ↔
      μ = nonnegativeGammaComplexMeasure := by
  apply op_nonnegative_complex_mixing_iff _ _ _
  intro n
  exact ⟨⟨gammaShapeThreeHilbertBasis n, gamma_shape_three_basis_mem_spectral_domain n⟩,
    gammaShapeThreeHilbertBasis.orthonormal.ne_zero n,
    gamma_shape_three_spectral_basis_action n⟩

theorem laguerre_canonical_nonnegative : OpNonnegative laguerreCanonicalOperator := by
  rw [laguerre_canonical_eq_spectral]
  exact laguerre_spectral_nonnegative id (fun n => Nat.cast_nonneg n)

theorem laguerre_canonical_heat_eq (t : ℝ) (ht : 0 ≤ t) :
    opNonnegativeHeat laguerreCanonicalOperator laguerre_canonical_selfAdjoint
      laguerre_canonical_nonnegative t = laguerreHeatOperator t ht := by
  apply hilbert_basis_operator_ext laguerreHilbertBasis
  intro n
  have h := op_nonnegative_heat_integer_eigenvector laguerreCanonicalOperator
    laguerre_canonical_selfAdjoint laguerre_canonical_nonnegative n
    ⟨laguerreHilbertBasis n, laguerre_basis_mem_canonical_domain n⟩
    (laguerre_canonical_basis_action n) t ht
  rw [laguerre_heat_basis_action]
  rw [show -(n : ℝ) * t = -t * (n : ℝ) by ring] at h
  exact h.trans (algebraMap_smul ℂ (Real.exp (-t * (n : ℝ))) _).symm

theorem gamma_shape_two_complex_mixing_iff (μ : ComplexMeasure OpNonnegativeRay) :
    (∀ x : LaguerreWeightedHilbert,
      complexStrongIntegral μ (fun s => opNonnegativeHeat laguerreCanonicalOperator
        laguerre_canonical_selfAdjoint laguerre_canonical_nonnegative s.val x) =
        opNonnegativeResolvent laguerreCanonicalOperator laguerre_canonical_selfAdjoint
          laguerre_canonical_nonnegative
          (opNonnegativeResolvent laguerreCanonicalOperator laguerre_canonical_selfAdjoint
            laguerre_canonical_nonnegative x)) ↔
      μ = nonnegativeGammaComplexMeasure := by
  apply op_nonnegative_complex_mixing_iff _ _ _
  intro n
  exact ⟨⟨laguerreHilbertBasis n, laguerre_basis_mem_canonical_domain n⟩,
    laguerreHilbertBasis.orthonormal.ne_zero n, laguerre_canonical_basis_action n⟩

end
end Sigma
