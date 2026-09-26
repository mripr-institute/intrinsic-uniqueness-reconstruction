import SigmaThomNativeBundles

namespace Sigma
noncomputable section

/-- Native complex bundles over a fixed supplied base, so their cohomology
rings and cup-product modules agree definitionally in splitting formulas. -/
structure NativeBundleOver (B : TopCat) where
  rank : ℕ
  Fiber : B → Type
  [fiberTopology : ∀ b, TopologicalSpace (Fiber b)]
  [fiberAdd : ∀ b, AddCommGroup (Fiber b)]
  [fiberModule : ∀ b, Module ℂ (Fiber b)]
  [totalTopology : TopologicalSpace (Bundle.TotalSpace (Fin rank → ℂ) Fiber)]
  [fiberBundle : FiberBundle (Fin rank → ℂ) Fiber]
  [vectorBundle : VectorBundle ℂ (Fin rank → ℂ) Fiber]

attribute [instance] NativeBundleOver.fiberTopology NativeBundleOver.fiberAdd
  NativeBundleOver.fiberModule NativeBundleOver.totalTopology
  NativeBundleOver.fiberBundle NativeBundleOver.vectorBundle

abbrev NativeBundleOver.bundle {B : TopCat} (V : NativeBundleOver B) : NativeComplexBundle where
  base := B
  rank := V.rank
  Fiber := V.Fiber

end
end Sigma
