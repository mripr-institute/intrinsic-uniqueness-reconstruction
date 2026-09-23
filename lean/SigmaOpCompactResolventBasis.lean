import SigmaOpCompactBasis
import SigmaOpCompactTotal
import SigmaOpResolventEigenbasis

namespace Sigma
noncomputable section
open Module.End
open scoped ComplexConjugate

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A nonnegative self-adjoint operator with a compact genuine positive-shift
resolvent admits a complete Hilbert eigenbasis. Compactness and injectivity of
the resolvent imply completeness; the generator eigenvalues and their domains
are then recovered from both resolvent inverse equations. -/
theorem nonnegative_compact_resolvent_eigenbasis
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ (@inner ℂ H _ x.val (A x)).re)
    (R : H →L[ℂ] H) (hR : OpIsResolvent A 1 R)
    (hcompact : IsCompactOperator R) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℂ H) (lam : ι → ℝ),
      (∀ i, 0 ≤ lam i) ∧
      ∃ hdom : ∀ i, b i ∈ A.domain,
        ∀ i, A ⟨b i, hdom i⟩ = (lam i : ℂ) • b i := by
  have hRself := selfadjoint_positive_shift_resolvent A hA R hR
  obtain ⟨ι, b, μ, hb⟩ := hilbert_eigenbasis_of_total_eigenspaces R hRself
    (compact_injective_selfadjoint_eigenspaces_total R hRself hcompact
      (operator_resolvent_injective A 1 R hR))
  have hreal (i : ι) : conj (μ i) = μ i := by
    have hbi : b i ≠ 0 := by
      intro hz
      have ho := b.orthonormal.1 i
      rw [hz, norm_zero] at ho
      norm_num at ho
    have heig : (b i) ∈ eigenspace R.toLinearMap (μ i) := by
      rw [mem_eigenspace_iff]
      exact hb i
    exact hRself.isSymmetric.conj_eigenvalue_eq_self
      (hasEigenvalue_of_hasEigenvector ⟨heig, hbi⟩)
  let r : ι → ℝ := fun i => (μ i).re
  have hRaction (i : ι) : R (b i) = (r i : ℂ) • b i := by
    rw [← (Complex.conj_eq_iff_re.mp (hreal i)).symm]
    exact hb i
  obtain ⟨hnonneg, hdom, hAaction⟩ :=
    nonnegative_generator_eigenbasis_of_resolvent A hpos R hR b r hRaction
  let lam : ι → ℝ := fun i => (r i)⁻¹ - 1
  exact ⟨ι, b, lam, hnonneg, hdom, hAaction⟩

end
end Sigma
