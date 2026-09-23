import SigmaOpCanonicalClosure

namespace Sigma
noncomputable section

/-- The marked spectral representation intertwines the closure of the actual
compact-test differential operator, with its full domain, not just its modes. -/
theorem laguerre_canonical_repr (x : laguerreCanonicalOperator.domain) :
    laguerreHilbertBasis.repr (laguerreCanonicalOperator x) =
      markedFunctionalCalculus id
        ⟨laguerreHilbertBasis.repr x.val,
          laguerre_canonical_eq_spectral.le.1 x.property⟩ := by
  have he : laguerreCanonicalOperator x = laguerreSpectralOperator id
      ⟨x.val, laguerre_canonical_eq_spectral.le.1 x.property⟩ :=
    laguerre_canonical_eq_spectral.le.2 rfl
  rw [he]
  exact laguerre_spectral_repr id _

theorem laguerre_canonical_repr_domain (x : LaguerreWeightedHilbert) :
    x ∈ laguerreCanonicalOperator.domain ↔
      laguerreHilbertBasis.repr x ∈ (markedFunctionalCalculus id).domain := by
  rw [laguerre_canonical_eq_spectral]
  rfl

theorem laguerre_canonical_eigenspace_iff (n : ℕ) (x : LaguerreWeightedHilbert) :
    x ∈ laguerreIntegerEigenspace n ↔
      ∃ hx : x ∈ laguerreCanonicalOperator.domain,
        laguerreCanonicalOperator ⟨x,hx⟩ = (n : ℂ) • x := by
  rw [laguerre_canonical_eq_spectral]
  rfl

/-- The spectral multiplier is uniquely determined among self-adjoint
operators by its actions on the proved complete marked basis. Thus it is not
a separately chosen realization of the scalar samples. -/
theorem laguerre_selfAdjoint_eq_spectral_of_basis (f : ℝ → ℝ)
    (T : LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert)
    (hT : IsSelfAdjoint T)
    (hdom : ∀ n : ℕ, laguerreHilbertBasis n ∈ T.domain)
    (ha : ∀ n : ℕ, T ⟨laguerreHilbertBasis n,hdom n⟩ =
      (f n : ℂ) • laguerreHilbertBasis n) :
    T = laguerreSpectralOperator f := by
  have hsymm : T.IsFormalAdjoint T := by
    have h := T.adjoint_isFormalAdjoint hT.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hT] at h
  have hc (x : T.domain) (n : ℕ) :
      laguerreHilbertBasis.repr (T x) n =
        (f n : ℂ) * laguerreHilbertBasis.repr x.val n := by
    have h := hsymm ⟨laguerreHilbertBasis n,hdom n⟩ x
    rw [ha, inner_smul_left] at h
    simpa [laguerreHilbertBasis.repr_apply_apply] using h.symm
  have hle : T ≤ laguerreSpectralOperator f := by
    refine ⟨?_, ?_⟩
    · intro x hx
      change Memℓp (fun n : ℕ => (f n : ℂ) * laguerreHilbertBasis.repr x n) 2
      have he : (fun n : ℕ => (f n : ℂ) * laguerreHilbertBasis.repr x n) =
          fun n => laguerreHilbertBasis.repr (T ⟨x,hx⟩) n := by
        funext n
        exact (hc ⟨x,hx⟩ n).symm
      rw [he]
      exact (laguerreHilbertBasis.repr (T ⟨x,hx⟩)).property
    · intro x y hxy
      apply laguerreHilbertBasis.repr.injective
      apply lp.ext
      funext n
      rw [hc, laguerre_spectral_coordinate, hxy]
  apply le_antisymm hle
  have hST : T.IsFormalAdjoint (laguerreSpectralOperator f) := by
    intro x y
    have h := laguerre_spectral_formal_adjoint f ⟨x.val,hle.1 x.property⟩ y
    rwa [← hle.2 (x := x) rfl] at h
  have h := hST.le_adjoint hT.dense_domain
  rwa [LinearPMap.isSelfAdjoint_def.mp hT] at h

theorem laguerre_spectral_congr (f g : ℝ → ℝ) (h : ∀ n : ℕ, f n = g n) :
    laguerreSpectralOperator f = laguerreSpectralOperator g := by
  apply laguerre_selfAdjoint_eq_spectral_of_basis g _ (laguerre_spectral_selfAdjoint f)
    (laguerre_basis_mem_spectral_domain f)
  intro n
  rw [laguerre_spectral_basis_action, h n]

/-- Sampling is extracted from the actual weighted-L2 operator actions; the
tail index may be zero and no sample at zero is assumed for positive tails. -/
theorem laguerre_samples_of_tail_actions (f g : ℝ → ℝ) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n →
      laguerreSpectralOperator f
          ⟨laguerreHilbertBasis n, laguerre_basis_mem_spectral_domain f n⟩ =
        laguerreSpectralOperator g
          ⟨laguerreHilbertBasis n, laguerre_basis_mem_spectral_domain g n⟩) :
    ∀ n : ℕ, N ≤ n → f n = g n := by
  intro n hn
  have he := h n hn
  rw [laguerre_spectral_basis_action, laguerre_spectral_basis_action] at he
  have hc := congrArg (fun x : LaguerreWeightedHilbert => laguerreHilbertBasis.repr x n) he
  simp only [map_smul, laguerreHilbertBasis.repr_self, lp.coeFn_smul,
    Pi.smul_apply, lp.single_apply_self, smul_eq_mul, mul_one] at hc
  exact Complex.ofReal_injective hc

theorem laguerre_bernstein_tail_actions_unique (f g : ℝ → ℝ)
    (hf : HasBernsteinRepresentation f) (hg : HasBernsteinRepresentation g) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n →
      laguerreSpectralOperator f
          ⟨laguerreHilbertBasis n, laguerre_basis_mem_spectral_domain f n⟩ =
        laguerreSpectralOperator g
          ⟨laguerreHilbertBasis n, laguerre_basis_mem_spectral_domain g n⟩) :
    ∀ l : ℝ, 0 ≤ l → f l = g l :=
  bernstein_function_integer_tail_unique f g hf hg N
    (laguerre_samples_of_tail_actions f g N h)

theorem laguerre_bernstein_tail_actions_data_unique
    (B C : BernsteinRepresentation) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n →
      laguerreSpectralOperator B.exponent
          ⟨laguerreHilbertBasis n, laguerre_basis_mem_spectral_domain B.exponent n⟩ =
        laguerreSpectralOperator C.exponent
          ⟨laguerreHilbertBasis n, laguerre_basis_mem_spectral_domain C.exponent n⟩) :
    B.killing = C.killing ∧ B.drift = C.drift ∧ B.levy = C.levy :=
  B.integer_tail_data_unique C N (laguerre_samples_of_tail_actions _ _ N h)

theorem laguerre_gamma_tail_actions_unique (B : BernsteinRepresentation) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n →
      laguerreSpectralOperator B.exponent
          ⟨laguerreHilbertBasis n, laguerre_basis_mem_spectral_domain B.exponent n⟩ =
        laguerreSpectralOperator gammaLaplaceExponent
          ⟨laguerreHilbertBasis n, laguerre_basis_mem_spectral_domain gammaLaplaceExponent n⟩) :
    (∀ l : ℝ, 0 ≤ l → B.exponent l = 2 * Real.log (1+l)) ∧
      B.killing = 0 ∧ B.drift = 0 ∧ B.levy = gammaCompletionLevyMeasure :=
  gamma_bernstein_integer_tail_unique B N (laguerre_samples_of_tail_actions _ _ N h)

/-- A distinct smooth nonnegative function, outside the Bernstein category,
has exactly the same operator on the actual Gamma-weighted Hilbert space,
including equality of unbounded domains. -/
theorem smooth_integer_invisible_canonical_calculus :
    ContDiffOn ℝ ⊤ smoothIntegerInvisibleExponent (Set.Ici 0) ∧
    (∀ l : ℝ, 0 ≤ l → 0 ≤ smoothIntegerInvisibleExponent l) ∧
    smoothIntegerInvisibleExponent (1/2) ≠ gammaLaplaceExponent (1/2) ∧
    ¬ HasBernsteinRepresentation smoothIntegerInvisibleExponent ∧
    laguerreSpectralOperator smoothIntegerInvisibleExponent =
      laguerreSpectralOperator gammaLaplaceExponent := by
  have h := smooth_integer_invisible_exponent_boundary
  exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2,
    laguerre_spectral_congr _ _ h.2.2.1⟩

end
end Sigma
