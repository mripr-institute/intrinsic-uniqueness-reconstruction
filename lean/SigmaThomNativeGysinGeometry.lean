import SigmaThomNativeGysinQuotient
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Maps.Proper.Basic

namespace Sigma
noncomputable section
open Topology
open scoped Manifold

/-- The actual rank-k trivial complex vector bundle used for stabilization. -/
def nativeGysinTrivialBundle (B : TopCat) (k : ℕ) : NativeComplexBundle where
  base := B
  rank := k
  Fiber := Bundle.Trivial B (Fin k → ℂ)

/-- A native direct-sum witness: continuously identified total spaces and
fiberwise complex-linear equivalences over the common base. The image of the
displayed embedding is the fiber product, by the fiber equivalences. -/
structure NativeGysinBundleSum (W W₁ W₂ : NativeComplexBundle)
    (h₁ : W₁.base = W.base) (h₂ : W₂.base = W.base) where
  fiber : ∀ x : W.base, W.Fiber x ≃ₗ[ℂ]
    (W₁.Fiber (h₁.symm ▸ x) × W₂.Fiber (h₂.symm ▸ x))
  totalEmbedding : IsEmbedding (fun p : W.total =>
    ((⟨h₁.symm ▸ p.proj, (fiber p.proj p.snd).1⟩ : W₁.total),
      (⟨h₂.symm ▸ p.proj, (fiber p.proj p.snd).2⟩ : W₂.total)))

/-- Geometric marks of the supplied stable embedding factorization. The
factorization retains the actual proper smooth map, its ambient real dimension,
and the actual embedding whose projection is that map. -/
structure NativeSmoothGysinGeometry (V : NativeComplexBundle) (Y : TopCat)
    (m n : ℕ) [ChartedSpace (EuclideanSpace ℝ (Fin m)) V.base]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y] where
  sourceManifold : SmoothManifoldWithCorners 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) V.base
  targetManifold : SmoothManifoldWithCorners 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Y
  map : C(V.base,Y)
  proper : IsProperMap map
  smooth : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ⊤ map
  stabilization : ℕ
  embedding : C(V.base, Y × EuclideanSpace ℝ (Fin (2*stabilization)))
  closedEmbedding : IsClosedEmbedding embedding
  embeddingSmooth : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
    (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin (2*stabilization)))) ⊤ embedding
  projection : ∀ x, (embedding x).1 = map x
  tubular : C(V.total, Y × EuclideanSpace ℝ (Fin (2*stabilization)))
  tubularEmbedding : IsOpenEmbedding tubular
  tubularZero : ∀ x, tubular (V.zeroSection x) = embedding x

/-- The primitive virtual-bundle data attached to the supplied complex
orientation. Actual bundles label their classes, including the actual trivial
stabilizing bundle. The designated tangent assignment is indexed by the actual
map. Its stable-normal equation is geometric input, not an RR identity. -/
structure NativeGysinVirtualData (T : SuppliedComplexThomTheory)
    (V : NativeComplexBundle) (Y : TopCat)
    (m n : ℕ) [ChartedSpace (EuclideanSpace ℝ (Fin m)) V.base]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y]
    (F : NativeSmoothGysinGeometry V Y m n) where
  Virtual : Type
  [virtualGroup : AddCommGroup Virtual]
  bundleClass : (W : NativeComplexBundle) → W.base = V.base → Virtual
  sumClass : ∀ (W W₁ W₂ : NativeComplexBundle)
    (h : W.base = V.base) (h₁ : W₁.base = V.base) (h₂ : W₂.base = V.base),
    NativeGysinBundleSum W W₁ W₂ (h₁.trans h.symm) (h₂.trans h.symm) →
      bundleClass W h = bundleClass W₁ h₁ + bundleClass W₂ h₂
  relativeTangent : C(V.base,Y) → Virtual
  todd : Multiplicative Virtual →* (T.HBase V.base)ˣ
  trivialTodd : ∀ k, todd (Multiplicative.ofAdd
    (bundleClass (nativeGysinTrivialBundle V.base k) rfl)) = 1
  tangentNormal : relativeTangent F.map =
    bundleClass (nativeGysinTrivialBundle V.base F.stabilization) rfl - bundleClass V rfl

attribute [instance] NativeGysinVirtualData.virtualGroup

end
end Sigma
