import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact

namespace Sigma
noncomputable section
open Module.End Submodule Set
open scoped ComplexConjugate
set_option maxHeartbeats 800000

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem bounded_eigenspace_isClosed (T : H →L[ℂ] H) (μ : ℂ) :
    IsClosed (eigenspace T.toLinearMap μ : Set H) := by
  convert isClosed_eq T.continuous (continuous_const.smul continuous_id :
    Continuous (fun x : H => μ • x)) using 1
  ext x
  exact mem_eigenspace_iff

/-- Assemble the complete orthogonal eigenspaces into one genuine Hilbert
basis. Its index type permits finite and empty spaces without auxiliary assumptions. -/
theorem hilbert_eigenbasis_of_total_eigenspaces (T : H →L[ℂ] H)
    (hT : IsSelfAdjoint T)
    (htotal : (⨆ μ : ℂ, eigenspace T.toLinearMap μ)ᗮ = ⊥) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℂ H) (μ : ι → ℂ),
      ∀ i, T (b i) = μ i • b i := by
  classical
  letI (μ : ℂ) : CompleteSpace (eigenspace T.toLinearMap μ) :=
    (bounded_eigenspace_isClosed T μ).completeSpace_coe
  choose w b hb using fun μ : ℂ => exists_hilbertBasis ℂ (eigenspace T.toLinearMap μ)
  let v : (Σ μ : ℂ, ↥(w μ)) → H := fun i => (b i.1 i.2 : H)
  have hv : Orthonormal ℂ v :=
    hT.isSymmetric.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
      (fun μ => (b μ).orthonormal)
  have hspan : (span ℂ (Set.range v))ᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hall (μ : ℂ) (i : w μ) : @inner ℂ H _ x (b μ i : H) = 0 := by
      rw [inner_eq_zero_symm]
      exact hx (v ⟨μ, i⟩) (subset_span ⟨⟨μ, i⟩, rfl⟩)
    have hper (μ : ℂ) : x ∈ (eigenspace T.toLinearMap μ)ᗮ := by
      intro y hy
      have hs := ((innerSL ℂ x).comp (eigenspace T.toLinearMap μ).subtypeL).hasSum
        ((b μ).hasSum_repr ⟨y, hy⟩)
      have he : @inner ℂ H _ x y = 0 := by
        have hz : HasSum (fun _ : w μ => (0 : ℂ)) (@inner ℂ H _ x y) := by
          simpa only [ContinuousLinearMap.comp_apply, map_smul, Submodule.subtypeL_apply,
            innerSL_apply, hall, smul_zero] using hs
        exact hz.unique hasSum_zero
      exact inner_eq_zero_symm.mp he
    have hm : x ∈ (⨆ μ : ℂ, eigenspace T.toLinearMap μ)ᗮ := by
      rw [← Submodule.iInf_orthogonal]
      exact (Submodule.mem_iInf _).mpr hper
    simpa only [htotal, Submodule.mem_bot] using hm
  refine ⟨Σ μ : ℂ, ↥(w μ), HilbertBasis.mkOfOrthogonalEqBot hv hspan,
    fun i => i.1, ?_⟩
  intro i
  have hbasis : (HilbertBasis.mkOfOrthogonalEqBot hv hspan) i = v i :=
    congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot hv hspan) i
  change T ((HilbertBasis.mkOfOrthogonalEqBot hv hspan) i) =
    i.1 • (HilbertBasis.mkOfOrthogonalEqBot hv hspan) i
  rw [hbasis]
  exact mem_eigenspace_iff.mp (b i.1 i.2).property

end
end Sigma
