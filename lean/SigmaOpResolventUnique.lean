import SigmaOpResolvent

namespace Sigma

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem operator_two_sided_resolvents_unique (A : E →ₗ.[ℂ] E) (a : ℂ)
    (R S : E →L[ℂ] E) (hR : OpIsResolvent A a R) (hS : OpIsResolvent A a S) :
    R = S := by
  apply ContinuousLinearMap.ext
  intro x
  have h := hR.left_inverse ⟨S x, hS.image_mem x⟩
  change R (A ⟨S x, hS.image_mem x⟩ + a • S x) = S x at h
  rw [hS.right_inverse x] at h
  exact h

theorem operator_square_apply_eq (R S : E →L[ℂ] E) (h : R = S) (x : E) :
    R (R x) = (S.comp S) x := by
  rw [h]
  rfl

theorem forall_equations_congr {α β : Type*} (F G P : α → β)
    (h : ∀ x, F x = G x) : (∀ x, P x = F x) ↔ (∀ x, P x = G x) := by
  simp only [h]

theorem common_iff_intersection {P Q R : Prop} (hP : P ↔ R) (hQ : Q ↔ R) :
    (P ∧ Q) ↔ R := by
  exact ⟨fun h => hP.mp h.1, fun h => ⟨hP.mpr h, hQ.mpr h⟩⟩

end Sigma
