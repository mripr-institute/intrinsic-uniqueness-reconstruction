import SigmaOpMarkedCalculus
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace Sigma
noncomputable section
open scoped ComplexConjugate

theorem marked_functional_domain_dense (f : ℝ → ℝ) :
    Dense ((markedFunctionalCalculus f).domain : Set MarkedIntegerHilbert) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  apply lp.ext
  funext n
  have hh := (Submodule.mem_orthogonal _ x).mp hx (markedIntegerEigenvector n)
    (markedIntegerEigenvector_mem_domain f n)
  simpa [markedIntegerEigenvector, lp.inner_single_left] using hh

theorem marked_functional_formal_adjoint (f : ℝ → ℝ) :
    (markedFunctionalCalculus f).IsFormalAdjoint (markedFunctionalCalculus f) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  change @inner ℂ ℂ _ ((f n : ℂ) * x.val n) (y.val n) =
    @inner ℂ ℂ _ (x.val n) ((f n : ℂ) * y.val n)
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem marked_functional_adjoint_coordinate (f : ℝ → ℝ)
    (y : (markedFunctionalCalculus f).adjoint.domain) (n : ℕ) :
    (markedFunctionalCalculus f).adjoint y n = (f n : ℂ) * y.val n := by
  have hi := ((markedFunctionalCalculus f).adjoint_isFormalAdjoint
    (marked_functional_domain_dense f)).symm
      ⟨markedIntegerEigenvector n, markedIntegerEigenvector_mem_domain f n⟩ y
  rw [markedFunctionalCalculus_eigenvector_action, inner_smul_left] at hi
  simpa [markedIntegerEigenvector, lp.inner_single_left] using hi.symm

/-- The maximal real diagonal operator is genuinely self-adjoint for the native
unbounded-operator adjoint, not just symmetric on its finite-support core. -/
theorem marked_functional_calculus_selfAdjoint (f : ℝ → ℝ) :
    IsSelfAdjoint (markedFunctionalCalculus f) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro y hy
      change Memℓp (fun n : ℕ => (f n : ℂ) * y n) 2
      have he : (fun n : ℕ => (f n : ℂ) * y n) =
          fun n => (markedFunctionalCalculus f).adjoint ⟨y,hy⟩ n := by
        funext n
        exact (marked_functional_adjoint_coordinate f ⟨y,hy⟩ n).symm
      rw [he]
      exact ((markedFunctionalCalculus f).adjoint ⟨y,hy⟩).property
    · intro x y hxy
      apply lp.ext
      funext n
      change (markedFunctionalCalculus f).adjoint x n = (f n : ℂ) * y.val n
      rw [marked_functional_adjoint_coordinate]
      exact congrArg (fun z : MarkedIntegerHilbert => (f n : ℂ) * z n) hxy
  · exact (marked_functional_formal_adjoint f).le_adjoint (marked_functional_domain_dense f)

end
end Sigma
