import SigmaOpGammaShapeThreeSpectral

namespace Sigma
noncomputable section
open Set

theorem gamma_shape_unitary_coordinate (x : LaguerreWeightedHilbert) :
    gammaShapeThreeHilbertBasis.repr (gammaShapeUnitary x) = laguerreHilbertBasis.repr x :=
  integer_basis_unitary_coordinate _ _ x

theorem gamma_shape_unitary_symm_coordinate (x : GammaShapeThreeWeightedHilbert) :
    laguerreHilbertBasis.repr (gammaShapeUnitary.symm x) =
      gammaShapeThreeHilbertBasis.repr x := by
  calc
    _ = gammaShapeThreeHilbertBasis.repr
        (gammaShapeUnitary (gammaShapeUnitary.symm x)) :=
      (integer_basis_unitary_coordinate _ _ _).symm
    _ = _ := by rw [gammaShapeUnitary.apply_symm_apply]

def gammaShapeThreeComplexResolvent (z : ℂ) :
    GammaShapeThreeWeightedHilbert →L[ℂ] GammaShapeThreeWeightedHilbert :=
  gammaShapeUnitary.toLinearIsometry.toContinuousLinearMap.comp
    ((laguerreComplexResolvent z).comp
      gammaShapeUnitary.symm.toLinearIsometry.toContinuousLinearMap)

theorem gamma_shape_three_complex_resolvent_coordinate (z : ℂ)
    (x : GammaShapeThreeWeightedHilbert) (n : ℕ) :
    gammaShapeThreeHilbertBasis.repr (gammaShapeThreeComplexResolvent z x) n =
      ((n : ℂ)-z)⁻¹ * gammaShapeThreeHilbertBasis.repr x n := by
  change gammaShapeThreeHilbertBasis.repr
    (gammaShapeUnitary (laguerreComplexResolvent z (gammaShapeUnitary.symm x))) n = _
  rw [gamma_shape_unitary_coordinate, laguerre_complex_resolvent_coordinate,
    gamma_shape_unitary_symm_coordinate]

theorem gamma_shape_three_complex_resolvent_mem_domain (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ (n : ℂ)) (x : GammaShapeThreeWeightedHilbert) :
    gammaShapeThreeComplexResolvent z x ∈ gammaShapeThreeSpectralOperator.domain := by
  change gammaShapeUnitary (laguerreComplexResolvent z (gammaShapeUnitary.symm x)) ∈ _
  apply (gamma_shape_unitary_spectral_domain_iff _).mpr
  rw [laguerre_canonical_eq_spectral]
  exact laguerre_complex_resolvent_mem_domain z hz _

theorem gamma_shape_three_has_complex_resolvent (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ (n : ℂ)) :
    HasBoundedUnboundedResolvent gammaShapeThreeSpectralOperator z := by
  refine ⟨gammaShapeThreeComplexResolvent z,
    gamma_shape_three_complex_resolvent_mem_domain z hz, ?_, ?_⟩
  · intro x
    apply gammaShapeThreeHilbertBasis.repr.injective
    apply lp.ext
    funext n
    rw [map_sub, map_smul]
    simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      gamma_shape_three_spectral_coordinate, gamma_shape_three_complex_resolvent_coordinate]
    field_simp [sub_ne_zero.mpr (hz n).symm]
    ring
  · intro x
    apply gammaShapeThreeHilbertBasis.repr.injective
    apply lp.ext
    funext n
    rw [gamma_shape_three_complex_resolvent_coordinate, map_sub, map_smul]
    simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      gamma_shape_three_spectral_coordinate]
    field_simp [sub_ne_zero.mpr (hz n).symm]
    ring

theorem gamma_shape_three_full_resolvent_set (z : ℂ) :
    HasBoundedUnboundedResolvent gammaShapeThreeSpectralOperator z ↔
      ∀ n : ℕ, z ≠ (n : ℂ) := by
  constructor
  · intro h n hz
    subst z
    exact (gammaShapeThreeHilbertBasis.orthonormal.ne_zero n)
      (bounded_unbounded_resolvent_excludes_eigenvalue _ _ h
        ⟨gammaShapeThreeHilbertBasis n, gamma_shape_three_basis_mem_spectral_domain n⟩
        (gamma_shape_three_spectral_basis_action n))
  · exact gamma_shape_three_has_complex_resolvent z

theorem gamma_shape_three_full_spectrum_exact :
    unboundedOperatorSpectrum gammaShapeThreeSpectralOperator =
      Set.range (fun n : ℕ => (n : ℂ)) := by
  ext z
  simp only [unboundedOperatorSpectrum, mem_setOf_eq, gamma_shape_three_full_resolvent_set,
    Set.mem_range]
  push_neg
  exact exists_congr fun n => eq_comm

def gammaShapeThreeIntegerEigenspace (n : ℕ) : Submodule ℂ GammaShapeThreeWeightedHilbert where
  carrier := {x | ∃ hx : x ∈ gammaShapeThreeSpectralOperator.domain,
    gammaShapeThreeSpectralOperator ⟨x, hx⟩ = (n : ℂ) • x}
  zero_mem' := ⟨Submodule.zero_mem _, by
    change gammaShapeThreeSpectralOperator.toFun 0 = _
    simp⟩
  add_mem' := by
    rintro x y ⟨hx, hAx⟩ ⟨hy, hAy⟩
    refine ⟨Submodule.add_mem _ hx hy, ?_⟩
    change gammaShapeThreeSpectralOperator (⟨x, hx⟩ + ⟨y, hy⟩) = _
    rw [LinearPMap.map_add, hAx, hAy, smul_add]
  smul_mem' := by
    rintro c x ⟨hx, hAx⟩
    refine ⟨Submodule.smul_mem _ c hx, ?_⟩
    change gammaShapeThreeSpectralOperator (c • ⟨x, hx⟩) = _
    rw [LinearPMap.map_smul, hAx, smul_comm]

theorem gamma_shape_three_integer_eigenspace_eq_span (n : ℕ) :
    gammaShapeThreeIntegerEigenspace n =
      Submodule.span ℂ {gammaShapeThreeHilbertBasis n} := by
  apply le_antisymm
  · rintro x ⟨hx, hAx⟩
    have he : x = gammaShapeThreeHilbertBasis.repr x n • gammaShapeThreeHilbertBasis n :=
      gamma_shape_three_integer_eigenvector_line n ⟨x, hx⟩ hAx
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    intro x hx
    have he : x = gammaShapeThreeHilbertBasis n := by simpa using hx
    subst x
    exact ⟨gamma_shape_three_basis_mem_spectral_domain n,
      gamma_shape_three_spectral_basis_action n⟩

theorem gamma_shape_three_integer_eigenvalue_simple (n : ℕ) :
    Module.finrank ℂ (gammaShapeThreeIntegerEigenspace n) = 1 := by
  rw [gamma_shape_three_integer_eigenspace_eq_span]
  exact finrank_span_singleton (gammaShapeThreeHilbertBasis.orthonormal.ne_zero n)

end
end Sigma
