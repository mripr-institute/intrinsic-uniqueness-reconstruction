import SigmaOpMarkedSelfAdjoint
import SigmaOpLaguerreComplete

namespace Sigma
noncomputable section
open scoped ComplexConjugate

/-! Actual self-adjoint diagonal operators in the weighted Laguerre Hilbert
space. Identification of the identity multiplier with the closure of the
compactly supported differential operator is a separate theorem. -/

def laguerreSpectralDomain (f : ℝ → ℝ) : Submodule ℂ LaguerreWeightedHilbert :=
  (markedFunctionalCalculus f).domain.comap laguerreHilbertBasis.repr.toLinearMap

def laguerreSpectralOperator (f : ℝ → ℝ) :
    LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert where
  domain := laguerreSpectralDomain f
  toFun :=
    { toFun := fun x => laguerreHilbertBasis.repr.symm
        (markedFunctionalCalculus f ⟨laguerreHilbertBasis.repr x.val, x.property⟩)
      map_add' := by
        intro x y
        apply laguerreHilbertBasis.repr.injective
        simp only [map_add, LinearIsometryEquiv.apply_symm_apply]
        apply lp.ext
        funext n
        change (f n : ℂ) * (laguerreHilbertBasis.repr (x.val + y.val) n) =
          (f n : ℂ) * laguerreHilbertBasis.repr x.val n +
          (f n : ℂ) * laguerreHilbertBasis.repr y.val n
        rw [map_add]
        exact mul_add _ _ _
      map_smul' := by
        intro c x
        apply laguerreHilbertBasis.repr.injective
        simp only [map_smul, LinearIsometryEquiv.apply_symm_apply]
        apply lp.ext
        funext n
        change (f n : ℂ) * (laguerreHilbertBasis.repr (c • x.val) n) =
          c * ((f n : ℂ) * laguerreHilbertBasis.repr x.val n)
        rw [map_smul]
        change (f n : ℂ) * (c * laguerreHilbertBasis.repr x.val n) = _
        ring }

theorem laguerre_spectral_repr (f : ℝ → ℝ)
    (x : (laguerreSpectralOperator f).domain) :
    laguerreHilbertBasis.repr (laguerreSpectralOperator f x) =
      markedFunctionalCalculus f ⟨laguerreHilbertBasis.repr x.val, x.property⟩ := by
  change laguerreHilbertBasis.repr (laguerreHilbertBasis.repr.symm _) = _
  exact LinearIsometryEquiv.apply_symm_apply _ _

theorem laguerre_spectral_coordinate (f : ℝ → ℝ)
    (x : (laguerreSpectralOperator f).domain) (n : ℕ) :
    laguerreHilbertBasis.repr (laguerreSpectralOperator f x) n =
      (f n : ℂ) * laguerreHilbertBasis.repr x.val n := by
  change laguerreHilbertBasis.repr (laguerreHilbertBasis.repr.symm _) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem laguerre_basis_mem_spectral_domain (f : ℝ → ℝ) (n : ℕ) :
    laguerreHilbertBasis n ∈ (laguerreSpectralOperator f).domain := by
  change laguerreHilbertBasis.repr (laguerreHilbertBasis n) ∈ (markedFunctionalCalculus f).domain
  rw [laguerreHilbertBasis.repr_self]
  exact markedIntegerEigenvector_mem_domain f n

theorem laguerre_spectral_basis_action (f : ℝ → ℝ) (n : ℕ) :
    laguerreSpectralOperator f ⟨laguerreHilbertBasis n, laguerre_basis_mem_spectral_domain f n⟩ =
      (f n : ℂ) • laguerreHilbertBasis n := by
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext k
  rw [laguerre_spectral_coordinate, map_smul, laguerreHilbertBasis.repr_self]
  change (f k : ℂ) * markedIntegerEigenvector n k =
    (f n : ℂ) * markedIntegerEigenvector n k
  by_cases h : k = n
  · subst k; rfl
  · simp [markedIntegerEigenvector, lp.single_apply_ne, h]

theorem laguerre_spectral_domain_dense (f : ℝ → ℝ) :
    Dense ((laguerreSpectralOperator f).domain : Set LaguerreWeightedHilbert) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  rw [← laguerreHilbertBasis.dense_span]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨n,rfl⟩
  exact laguerre_basis_mem_spectral_domain f n

theorem laguerre_spectral_formal_adjoint (f : ℝ → ℝ) :
    (laguerreSpectralOperator f).IsFormalAdjoint (laguerreSpectralOperator f) := by
  intro x y
  rw [← laguerreHilbertBasis.repr.inner_map_map, ← laguerreHilbertBasis.repr.inner_map_map]
  rw [laguerre_spectral_repr, laguerre_spectral_repr]
  exact marked_functional_formal_adjoint f
    ⟨laguerreHilbertBasis.repr x.val,x.property⟩
    ⟨laguerreHilbertBasis.repr y.val,y.property⟩

theorem laguerre_spectral_adjoint_coordinate (f : ℝ → ℝ)
    (y : (laguerreSpectralOperator f).adjoint.domain) (n : ℕ) :
    laguerreHilbertBasis.repr ((laguerreSpectralOperator f).adjoint y) n =
      (f n : ℂ) * laguerreHilbertBasis.repr y.val n := by
  have hi := ((laguerreSpectralOperator f).adjoint_isFormalAdjoint
    (laguerre_spectral_domain_dense f)).symm
      ⟨laguerreHilbertBasis n, laguerre_basis_mem_spectral_domain f n⟩ y
  rw [laguerre_spectral_basis_action, inner_smul_left] at hi
  simpa [laguerreHilbertBasis.repr_apply_apply] using hi.symm

theorem laguerre_spectral_selfAdjoint (f : ℝ → ℝ) :
    IsSelfAdjoint (laguerreSpectralOperator f) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro y hy
      change Memℓp (fun n : ℕ => (f n : ℂ) * laguerreHilbertBasis.repr y n) 2
      have he : (fun n : ℕ => (f n : ℂ) * laguerreHilbertBasis.repr y n) =
          fun n => laguerreHilbertBasis.repr ((laguerreSpectralOperator f).adjoint ⟨y,hy⟩) n := by
        funext n
        exact (laguerre_spectral_adjoint_coordinate f ⟨y,hy⟩ n).symm
      rw [he]
      exact (laguerreHilbertBasis.repr ((laguerreSpectralOperator f).adjoint ⟨y,hy⟩)).property
    · intro x y hxy
      apply laguerreHilbertBasis.repr.injective
      apply lp.ext
      funext n
      rw [laguerre_spectral_adjoint_coordinate, laguerre_spectral_coordinate]
      exact congrArg (fun z : LaguerreWeightedHilbert => (f n : ℂ) * laguerreHilbertBasis.repr z n) hxy
  · exact (laguerre_spectral_formal_adjoint f).le_adjoint (laguerre_spectral_domain_dense f)

theorem laguerre_raw_eq_sqrt_smul_basis (n : ℕ) :
    laguerreL2Vector n = (Real.sqrt (n+1 : ℝ) : ℂ) • laguerreHilbertBasis n := by
  rw [laguerre_hilbert_basis_apply, normalizedLaguerreL2Vector, smul_smul]
  have hn : (Real.sqrt (n+1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < n+1)).ne'
  rw [mul_inv_cancel₀ hn, one_smul]

theorem laguerre_raw_mem_spectral_domain (f : ℝ → ℝ) (n : ℕ) :
    laguerreL2Vector n ∈ (laguerreSpectralOperator f).domain := by
  rw [laguerre_raw_eq_sqrt_smul_basis]
  exact Submodule.smul_mem _ _ (laguerre_basis_mem_spectral_domain f n)

theorem laguerre_spectral_raw_action (f : ℝ → ℝ) (n : ℕ) :
    laguerreSpectralOperator f ⟨laguerreL2Vector n, laguerre_raw_mem_spectral_domain f n⟩ =
      (f n : ℂ) • laguerreL2Vector n := by
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext k
  rw [laguerre_spectral_coordinate, map_smul]
  change (f k : ℂ) * laguerreHilbertBasis.repr (laguerreL2Vector n) k =
    (f n : ℂ) * laguerreHilbertBasis.repr (laguerreL2Vector n) k
  rw [laguerre_raw_eq_sqrt_smul_basis, map_smul, laguerreHilbertBasis.repr_self]
  change (f k : ℂ) * ((Real.sqrt (n+1 : ℝ) : ℂ) * markedIntegerEigenvector n k) =
    (f n : ℂ) * ((Real.sqrt (n+1 : ℝ) : ℂ) * markedIntegerEigenvector n k)
  by_cases hk : k=n
  · subst k; rfl
  · simp [markedIntegerEigenvector, lp.single_apply_ne, hk]

theorem laguerre_spectral_raw_representative (f : ℝ → ℝ) (n : ℕ) :
    (fun t : ℝ => (laguerreSpectralOperator f
      ⟨laguerreL2Vector n, laguerre_raw_mem_spectral_domain f n⟩) t) =ᵐ[gammaProbability]
      (fun t => ((f n * opLaguerre n t : ℝ) : ℂ)) := by
  rw [laguerre_spectral_raw_action]
  filter_upwards [MeasureTheory.Lp.coeFn_smul (f n : ℂ) (laguerreL2Vector n),
    (op_laguerre_complex_mem_l2 n).coeFn_toLp] with t ht hu
  change laguerreL2Vector n t = _ at hu
  rw [ht]
  change (f n : ℂ) * laguerreL2Vector n t = _
  rw [hu]
  simp

end
end Sigma
