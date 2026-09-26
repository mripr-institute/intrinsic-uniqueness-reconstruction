import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.LinearPMap

namespace Sigma
noncomputable section

/-- The supplied Thom and Chern-character data for one complex-oriented bundle.
The relative groups are modules over the base rings. No correction class or
comparison formula is assumed: it is constructed by the inverse cohomological
Thom isomorphism below. -/
structure NativeThomContext (K H KR HR : Type*) [CommRing K] [CommRing H]
    [AddCommGroup KR] [AddCommGroup HR] [Module K KR] [Module H HR] where
  chBase : K →+* H
  chRelative : KR →+ HR
  ch_smul : ∀ (a : K) (u : KR), chRelative (a • u) = chBase a • chRelative u
  kThom : K ≃ₗ[K] KR
  hThom : H ≃ₗ[H] HR

namespace NativeThomContext
variable {K H KR HR : Type*} [CommRing K] [CommRing H]
  [AddCommGroup KR] [AddCommGroup HR] [Module K KR] [Module H HR]
variable (T : NativeThomContext K H KR HR)

def kClass : KR := T.kThom 1
def hClass : HR := T.hThom 1

def correction : H := T.hThom.symm (T.chRelative T.kClass)

/-- Multiplication by the supplied cohomological Thom class is the actual
supplied Thom isomorphism. -/
theorem hThom_eq_smul (a : H) : T.hThom a = a • T.hClass := by
  simpa [hClass] using T.hThom.map_smul a (1 : H)

theorem kThom_eq_smul (a : K) : T.kThom a = a • T.kClass := by
  simpa [kClass] using T.kThom.map_smul a (1 : K)

/-- Existence of the comparison is a consequence of Thom surjectivity. -/
theorem correction_comparison : T.chRelative T.kClass = T.correction • T.hClass := by
  rw [← T.hThom_eq_smul, correction, T.hThom.apply_symm_apply]

/-- Uniqueness uses the injective Thom map, rather than cancellation of an
Euler class, which could be a zero divisor on a finite base. -/
theorem correction_unique (c : H) (hc : T.chRelative T.kClass = c • T.hClass) :
    c = T.correction := by
  apply T.hThom.injective
  rw [T.hThom_eq_smul, ← hc, correction, T.hThom.apply_symm_apply]

theorem correction_exists_unique :
    ∃! c : H, T.chRelative T.kClass = c • T.hClass :=
  ⟨T.correction, T.correction_comparison, fun c hc => T.correction_unique c hc⟩

/-- Chern character on the entire Thom image, not only on its unit class. -/
theorem ch_thom (a : K) :
    T.chRelative (T.kThom a) = T.hThom (T.chBase a * T.correction) := by
  rw [T.kThom_eq_smul, T.ch_smul, T.correction_comparison, T.hThom_eq_smul, mul_smul]

end NativeThomContext
end
end Sigma
