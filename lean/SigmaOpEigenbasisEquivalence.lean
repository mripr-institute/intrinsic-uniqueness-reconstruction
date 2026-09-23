import SigmaOpIntegerEigenbasis

namespace Sigma
noncomputable section
open scoped ComplexConjugate ENNReal NNReal

variable {ι H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The coordinates of a self-adjoint operator in any complete eigenbasis. -/
theorem real_eigenbasis_coordinate [CompleteSpace H] (b : HilbertBasis ι ℂ H) (eigenvalue : ι → ℝ)
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hdom : ∀ i, b i ∈ A.domain)
    (ha : ∀ i, A ⟨b i, hdom i⟩ = (eigenvalue i : ℂ) • b i)
    (x : A.domain) (i : ι) : b.repr (A x) i = (eigenvalue i : ℂ) * b.repr x.val i := by
  have hsymm : A.IsFormalAdjoint A := by
    have h := A.adjoint_isFormalAdjoint hA.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hA] at h
  have h := hsymm ⟨b i, hdom i⟩ x
  rw [ha, inner_smul_left] at h
  simpa [b.repr_apply_apply] using h.symm

/-- Self-adjointness derives the full weighted coefficient domain. The index
type may be finite, empty, or infinite. -/
theorem real_eigenbasis_mem_domain_iff [CompleteSpace H] (b : HilbertBasis ι ℂ H) (eigenvalue : ι → ℝ)
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hdom : ∀ i, b i ∈ A.domain)
    (ha : ∀ i, A ⟨b i, hdom i⟩ = (eigenvalue i : ℂ) • b i) (x : H) :
    x ∈ A.domain ↔ Memℓp (fun i => (eigenvalue i : ℂ) * b.repr x i) 2 := by
  constructor
  · intro hx
    have he : (fun i => (eigenvalue i : ℂ) * b.repr x i) = b.repr (A ⟨x, hx⟩) := by
      funext i
      exact (real_eigenbasis_coordinate b eigenvalue A hA hdom ha ⟨x, hx⟩ i).symm
    rw [he]
    exact (b.repr (A ⟨x, hx⟩)).property
  · intro hx
    let w : H := b.repr.symm ⟨fun i => (eigenvalue i : ℂ) * b.repr x i, hx⟩
    have hw (y : A.domain) : @inner ℂ H _ w y.val = @inner ℂ H _ x (A y) := by
      rw [← b.repr.inner_map_map, ← b.repr.inner_map_map,
        lp.inner_eq_tsum, lp.inner_eq_tsum]
      apply tsum_congr
      intro i
      have hwc : b.repr w i = (eigenvalue i : ℂ) * b.repr x i := by
        simp only [w, LinearIsometryEquiv.apply_symm_apply]
      rw [hwc, real_eigenbasis_coordinate b eigenvalue A hA hdom ha]
      simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
      ring
    have hx' := A.mem_adjoint_domain_of_exists x ⟨w, hw⟩
    rwa [LinearPMap.isSelfAdjoint_def.mp hA] at hx'

theorem real_eigenbasis_domain_iff [CompleteSpace H] (b : HilbertBasis ι ℂ H) (eigenvalue : ι → ℝ)
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hdom : ∀ i, b i ∈ A.domain)
    (ha : ∀ i, A ⟨b i, hdom i⟩ = (eigenvalue i : ℂ) • b i) (x : H) :
    x ∈ A.domain ↔ Summable (fun i => (eigenvalue i)^2 * ‖b.repr x i‖^2) := by
  rw [real_eigenbasis_mem_domain_iff b eigenvalue A hA hdom ha,
    memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The existing maximal multiplier realizes arbitrary real eigenvalues. -/
theorem real_eigenbasis_operator_eq [CompleteSpace H] (b : HilbertBasis ℕ ℂ H) (eigenvalue : ℕ → ℝ)
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hdom : ∀ i, b i ∈ A.domain)
    (ha : ∀ i, A ⟨b i, hdom i⟩ = (eigenvalue i : ℂ) • b i) :
    A = integerBasisMultiplier b (fun i => (eigenvalue i : ℂ)) := by
  apply LinearPMap.ext
  · ext x
    exact real_eigenbasis_mem_domain_iff b eigenvalue A hA hdom ha x
  · intro x y hxy
    apply b.repr.injective
    apply lp.ext
    funext i
    rw [real_eigenbasis_coordinate b eigenvalue A hA hdom ha,
      integer_basis_multiplier_coordinate, hxy]

/-- Matching complete orthonormal eigenbases supply an actual unitary. -/
def eigenbasisUnitary (b : HilbertBasis ι ℂ H) (c : HilbertBasis ι ℂ K) : H ≃ₗᵢ[ℂ] K :=
  b.repr.trans c.repr.symm

theorem eigenbasis_unitary_coordinate (b : HilbertBasis ι ℂ H)
    (c : HilbertBasis ι ℂ K) (x : H) :
    c.repr (eigenbasisUnitary b c x) = b.repr x := by
  simp [eigenbasisUnitary]

theorem eigenbasis_unitary_basis (b : HilbertBasis ι ℂ H)
    (c : HilbertBasis ι ℂ K) (i : ι) : eigenbasisUnitary b c (b i) = c i := by
  classical
  apply c.repr.injective
  rw [eigenbasis_unitary_coordinate, b.repr_self, c.repr_self]

/-- The unitary carries the entire domains, not just the eigenvector spans. -/
theorem real_eigenbasis_unitary_domain [CompleteSpace H] [CompleteSpace K] (b : HilbertBasis ι ℂ H)
    (c : HilbertBasis ι ℂ K) (eigenvalue : ι → ℝ)
    (A : H →ₗ.[ℂ] H) (B : K →ₗ.[ℂ] K) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hdomA : ∀ i, b i ∈ A.domain) (hdomB : ∀ i, c i ∈ B.domain)
    (ha : ∀ i, A ⟨b i, hdomA i⟩ = (eigenvalue i : ℂ) • b i)
    (hb : ∀ i, B ⟨c i, hdomB i⟩ = (eigenvalue i : ℂ) • c i) (x : H) :
    eigenbasisUnitary b c x ∈ B.domain ↔ x ∈ A.domain := by
  rw [real_eigenbasis_mem_domain_iff c eigenvalue B hB hdomB hb,
    real_eigenbasis_mem_domain_iff b eigenvalue A hA hdomA ha, eigenbasis_unitary_coordinate]

theorem real_eigenbasis_unitary_intertwines [CompleteSpace H] [CompleteSpace K] (b : HilbertBasis ι ℂ H)
    (c : HilbertBasis ι ℂ K) (eigenvalue : ι → ℝ)
    (A : H →ₗ.[ℂ] H) (B : K →ₗ.[ℂ] K) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hdomA : ∀ i, b i ∈ A.domain) (hdomB : ∀ i, c i ∈ B.domain)
    (ha : ∀ i, A ⟨b i, hdomA i⟩ = (eigenvalue i : ℂ) • b i)
    (hb : ∀ i, B ⟨c i, hdomB i⟩ = (eigenvalue i : ℂ) • c i) (x : A.domain) :
    eigenbasisUnitary b c (A x) =
      B ⟨eigenbasisUnitary b c x.val,
        (real_eigenbasis_unitary_domain b c eigenvalue A B hA hB hdomA hdomB ha hb x.val).2
          x.property⟩ := by
  apply c.repr.injective
  apply lp.ext
  funext i
  rw [eigenbasis_unitary_coordinate, real_eigenbasis_coordinate b eigenvalue A hA hdomA ha,
    real_eigenbasis_coordinate c eigenvalue B hB hdomB hb]
  rw [eigenbasis_unitary_coordinate]

/-- Reindexing a complete Hilbert basis along a bijection preserves completeness. -/
def reindexEigenbasis {κ : Type*} [CompleteSpace K]
    (c : HilbertBasis κ ℂ K) (e : ι ≃ κ) : HilbertBasis ι ℂ K :=
  HilbertBasis.mk (c.orthonormal.comp e e.injective) (by
    have hr : Set.range (c ∘ e) = Set.range c := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, by simp⟩
    rw [hr, c.dense_span])

theorem reindex_eigenbasis_apply {κ : Type*} [CompleteSpace K]
    (c : HilbertBasis κ ℂ K) (e : ι ≃ κ) (i : ι) :
    reindexEigenbasis c e i = c (e i) := by
  exact congrFun (HilbertBasis.coe_mk _ _) i

/-- An eigenvalue-preserving bijection of complete eigenbases gives unitary
equivalence of the actual self-adjoint operators, with their full domains.
No infinitude or nonemptiness assumption is made on either index type. -/
theorem real_eigenbasis_unitary_equivalence {κ : Type*} [CompleteSpace H] [CompleteSpace K]
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (eigenvalue : ι → ℝ) (otherEigenvalue : κ → ℝ) (e : ι ≃ κ)
    (he : ∀ i, otherEigenvalue (e i) = eigenvalue i)
    (A : H →ₗ.[ℂ] H) (B : K →ₗ.[ℂ] K) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hdomA : ∀ i, b i ∈ A.domain) (hdomB : ∀ i, c i ∈ B.domain)
    (ha : ∀ i, A ⟨b i, hdomA i⟩ = (eigenvalue i : ℂ) • b i)
    (hb : ∀ i, B ⟨c i, hdomB i⟩ = (otherEigenvalue i : ℂ) • c i) :
    ∃ U : H ≃ₗᵢ[ℂ] K,
      (∀ i, U (b i) = c (e i)) ∧
      (∀ x : H, U x ∈ B.domain ↔ x ∈ A.domain) ∧
      (∀ (x : A.domain) (y : B.domain), U x.val = y.val → U (A x) = B y) := by
  let d := reindexEigenbasis c e
  have hd (i : ι) : d i = c (e i) := reindex_eigenbasis_apply c e i
  have hdomD (i : ι) : d i ∈ B.domain := by rw [hd]; exact hdomB (e i)
  have hbD (i : ι) : B ⟨d i, hdomD i⟩ = (eigenvalue i : ℂ) • d i := by
    have hsub : (⟨d i, hdomD i⟩ : B.domain) = ⟨c (e i), hdomB (e i)⟩ :=
      Subtype.ext (hd i)
    rw [hsub, hb, he, hd]
  refine ⟨eigenbasisUnitary b d, ?_, ?_, ?_⟩
  · intro i
    rw [eigenbasis_unitary_basis, hd]
  · exact real_eigenbasis_unitary_domain b d eigenvalue A B hA hB hdomA hdomD ha hbD
  · intro x y hxy
    rw [real_eigenbasis_unitary_intertwines b d eigenvalue A B hA hB hdomA hdomD ha hbD]
    congr 1
    exact Subtype.ext hxy

end
end Sigma
