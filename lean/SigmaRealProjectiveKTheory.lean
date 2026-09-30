import SigmaNativeComplexBundleModel
import SigmaRealProjectiveDeterminantCancellation

namespace Sigma
noncomputable section
open Bundle
open FiniteComplexBundle

/-- The actual complexified tautological line, as an object of the native
Whitney-sum monoid on the fixed real projective plane. -/
def realProjectiveKLine : FiniteComplexBundle RealProjectivePlane where
  Model := Fin 1 → ℂ
  Fiber := realProjectiveComplexCore.Fiber

/-- The paper's literal complex K⁰ inequality. Equality in the constructed
Grothendieck group produces an arbitrary native finite-dimensional stabilizer;
changing its model coordinates permits the proved determinant cancellation. -/
theorem real_projective_complex_k0_class_ne_one :
    kClass realProjectiveKLine ≠
      kClass (FiniteComplexBundle.trivial (B := RealProjectivePlane) 1) := by
  intro heq
  obtain ⟨S, ⟨e⟩⟩ := (kClass_eq_iff _ _).mp heq
  let n := Module.finrank ℂ S.Model
  let h : S.Model ≃L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
  let S' := S.withModel (Fin n → ℂ) h
  let es : Iso S' S := S.withModelIso (Fin n → ℂ) h
  let e' : Iso (realProjectiveKLine.sum S')
      ((FiniteComplexBundle.trivial 1).sum S') :=
    (((Iso.refl realProjectiveKLine).sum es).trans e).trans
      ((Iso.refl (FiniteComplexBundle.trivial 1)).sum es.symm)
  letI : TopologicalSpace (TotalSpace (Fin n → ℂ) S.Fiber) := S'.totalTopology
  letI : FiberBundle (Fin n → ℂ) S.Fiber := S'.fiberBundle
  letI : VectorBundle ℂ (Fin n → ℂ) S.Fiber := S'.vectorBundle
  apply real_projective_complex_line_not_stably_trivial n S.Fiber
  exact ⟨{ totalHomeomorph := e'.homeomorph
           fiberEquiv := e'.fiber
           total_apply := fun _ _ => rfl }⟩

end
end Sigma
