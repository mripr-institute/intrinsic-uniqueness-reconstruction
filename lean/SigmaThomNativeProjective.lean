import SigmaThomNativeBundles
import Mathlib.LinearAlgebra.Projectivization.Basic

namespace Sigma
noncomputable section
open scoped LinearAlgebra.Projectivization

abbrev NativeProjectiveSpace (n : ℕ) := ℙ ℂ (Fin (n+1) → ℂ)

/-- The standard quotient topology from nonzero complex coordinate vectors. -/
instance native_projective_topology (n : ℕ) : TopologicalSpace (NativeProjectiveSpace n) :=
  TopologicalSpace.coinduced (Projectivization.mk' ℂ) inferInstance

def nativeProjectiveBase (n : ℕ) : TopCat := TopCat.of (NativeProjectiveSpace n)

/-- The actual incidence-space model of the tautological complex line. -/
def NativeTautologicalTotal (n : ℕ) :=
  {p : NativeProjectiveSpace n × (Fin (n+1) → ℂ) // p.2 ∈ p.1.submodule}
instance native_tautological_total_topology (n : ℕ) : TopologicalSpace (NativeTautologicalTotal n) :=
  inferInstanceAs (TopologicalSpace {p : NativeProjectiveSpace n × (Fin (n+1) → ℂ) // p.2 ∈ p.1.submodule})

/-- A supplied locally trivial model is identified with the actual universal
line, both fibrewise and as a total topological space. This is not an arbitrary
bundle carrying a projective label. -/
structure NativeTautologicalIdentification (n : ℕ) (V : NativeComplexBundle) where
  rank : V.rank = 1
  base : V.base ≃ₜ NativeProjectiveSpace n
  fiber : ∀ b, V.Fiber b ≃ₗ[ℂ] (base b).submodule
  total : V.total ≃ₜ NativeTautologicalTotal n
  total_apply : ∀ x : V.total, (total x).val = (base x.proj, (fiber x.proj x.snd).val)

/-- The standard coordinate inclusion, with zero as the new first coordinate. -/
def nativeProjectiveLinearInclusion (n : ℕ) :
    (Fin (n+1) → ℂ) →ₗ[ℂ] (Fin (n+2) → ℂ) where
  toFun x := Fin.cons 0 x
  map_add' x y := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem native_projective_linear_inclusion_injective (n : ℕ) :
    Function.Injective (nativeProjectiveLinearInclusion n) := by
  intro x y h
  funext i
  exact congrFun h i.succ

def nativeProjectiveInclusion (n : ℕ) : NativeProjectiveSpace n → NativeProjectiveSpace (n+1) :=
  Projectivization.map (nativeProjectiveLinearInclusion n) (native_projective_linear_inclusion_injective n)

end
end Sigma
