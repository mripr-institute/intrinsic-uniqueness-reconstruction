import SigmaOpCompactEigenvector
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace Sigma
noncomputable section
open Module.End

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A compact injective self-adjoint operator has no nonzero vector orthogonal to
all of its eigenspaces. The proof applies compact self-adjoint eigenvector
existence to the invariant orthogonal complement. -/
theorem compact_injective_selfadjoint_eigenspaces_total
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hcompact : IsCompactOperator T)
    (hinjective : Function.Injective T) :
    (⨆ μ : ℂ, eigenspace T.toLinearMap μ)ᗮ = ⊥ := by
  classical
  let V : Submodule ℂ H := (⨆ μ : ℂ, eigenspace T.toLinearMap μ)ᗮ
  have hpres (x : H) (hx : x ∈ V) : T x ∈ V := by
    exact hT.isSymmetric.orthogonalComplement_iSup_eigenspaces_invariant hx
  have hclosed : IsClosed (V : Set H) :=
    (⨆ μ : ℂ, eigenspace T.toLinearMap μ).isClosed_orthogonal
  letI : CompleteSpace V := hclosed.completeSpace_coe
  let S : V →L[ℂ] V := (T.comp V.subtypeL).codRestrict V (fun x => hpres x.val x.property)
  have hScompact : IsCompactOperator S :=
    hcompact.comp_clm V.subtypeL |>.codRestrict (fun x => hpres x.val x.property) hclosed
  have hSself : IsSelfAdjoint S := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    change @inner ℂ H _ (T x.val) y.val = @inner ℂ H _ x.val (T y.val)
    exact hT.isSymmetric x.val y.val
  have hVbot : V = ⊥ := by
    by_contra hv
    have hSne : S ≠ 0 := by
      intro hzero
      apply hv
      apply (Submodule.eq_bot_iff V).mpr
      intro x hx
      have hSx : S ⟨x, hx⟩ = 0 := by rw [hzero]; simp
      have hTx : T x = 0 := congrArg Subtype.val hSx
      exact hinjective (by simpa using hTx)
    obtain ⟨r, x, hr, hxne, hx⟩ := compact_selfadjoint_exists_eigenvector S hSself hScompact hSne
    have hmem : (x : H) ∈ eigenspace T.toLinearMap (r : ℂ) := by
      rw [mem_eigenspace_iff]
      change T x.val = (r : ℂ) • x.val
      exact congrArg Subtype.val hx
    have htop : (x : H) ∈ (⨆ μ : ℂ, eigenspace T.toLinearMap μ) :=
      le_iSup (fun μ : ℂ => eigenspace T.toLinearMap μ) (r : ℂ) hmem
    have hz := x.property (x : H) htop
    have hnorm : ‖(x : H)‖ = 0 := by
      have := inner_self_eq_zero.mp hz
      simpa [norm_eq_zero] using this
    exact hxne (Subtype.ext (norm_eq_zero.mp hnorm))
  change V = ⊥ at hVbot
  exact hVbot

end
end Sigma
