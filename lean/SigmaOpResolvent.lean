import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import SigmaOperators

/-! The full-resolvent inverse in final:O4-resolvents, using the native
partially defined operator type.  A resolvent is specified by its actual
two inverse equations, not by the desired domain or uniqueness conclusion.
-/

namespace Sigma
noncomputable section

variable {K E : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]

structure OpIsResolvent (A : E →ₗ.[K] E) (a : K) (R : E →L[K] E) : Prop where
  image_mem : ∀ h : E, R h ∈ A.domain
  right_inverse : ∀ h : E, A ⟨R h, image_mem h⟩ + a • R h = h
  left_inverse : ∀ x : A.domain, R (A x + a • (x : E)) = (x : E)

/-- A full resolvent recovers the actual domain, not just eigenvalues. -/
theorem operator_resolvent_domain (A : E →ₗ.[K] E) (a : K) (R : E →L[K] E)
    (hR : OpIsResolvent A a R) : (A.domain : Set E) = Set.range R := by
  ext x
  constructor
  · intro hx
    exact ⟨A ⟨x, hx⟩ + a • x, hR.left_inverse ⟨x, hx⟩⟩
  · rintro ⟨h, rfl⟩
    exact hR.image_mem h

theorem operator_resolvent_action (A : E →ₗ.[K] E) (a : K) (R : E →L[K] E)
    (hR : OpIsResolvent A a R) (h : E) :
    A ⟨R h, hR.image_mem h⟩ = h - a • R h := by
  exact eq_sub_iff_add_eq.mpr (hR.right_inverse h)

theorem operator_resolvent_injective (A : E →ₗ.[K] E) (a : K) (R : E →L[K] E)
    (hR : OpIsResolvent A a R) : Function.Injective R := by
  intro x y hxy
  have hp : (⟨R x, hR.image_mem x⟩ : A.domain) = ⟨R y, hR.image_mem y⟩ :=
    Subtype.ext hxy
  calc
    x = A ⟨R x, hR.image_mem x⟩ + a • R x := (hR.right_inverse x).symm
    _ = A ⟨R y, hR.image_mem y⟩ + a • R y := by rw [hp, hxy]
    _ = y := hR.right_inverse y

/-- Equality of the complete resolvent at one retained shift determines the
native partially defined operator, including its domain. -/
theorem operator_full_resolvent_unique (A B : E →ₗ.[K] E) (a : K) (R : E →L[K] E)
    (hA : OpIsResolvent A a R) (hB : OpIsResolvent B a R) : A = B := by
  apply LinearPMap.ext
  · apply SetLike.coe_injective
    exact (operator_resolvent_domain A a R hA).trans
      (operator_resolvent_domain B a R hB).symm
  · intro x y hxy
    have he : R (A x + a • (x : E)) = R (B y + a • (y : E)) := by
      rw [hA.left_inverse, hB.left_inverse, hxy]
    have h := operator_resolvent_injective A a R hA he
    rw [hxy] at h
    exact add_right_cancel h

end
end Sigma
