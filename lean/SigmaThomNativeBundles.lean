import SigmaThomNativeContext
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Analysis.Complex.Basic

namespace Sigma
noncomputable section

/-- An actual finite-rank complex topological vector bundle. The topology,
local triviality, and complex linearity are native Mathlib structures. -/
structure NativeComplexBundle where
  base : TopCat
  rank : ℕ
  Fiber : base → Type
  [fiberTopology : ∀ b, TopologicalSpace (Fiber b)]
  [fiberAdd : ∀ b, AddCommGroup (Fiber b)]
  [fiberModule : ∀ b, Module ℂ (Fiber b)]
  [totalTopology : TopologicalSpace (Bundle.TotalSpace (Fin rank → ℂ) Fiber)]
  [fiberBundle : FiberBundle (Fin rank → ℂ) Fiber]
  [vectorBundle : VectorBundle ℂ (Fin rank → ℂ) Fiber]

attribute [instance] NativeComplexBundle.fiberTopology NativeComplexBundle.fiberAdd
  NativeComplexBundle.fiberModule NativeComplexBundle.totalTopology
  NativeComplexBundle.fiberBundle NativeComplexBundle.vectorBundle

namespace NativeComplexBundle

def total (V : NativeComplexBundle) : TopCat :=
  TopCat.of (Bundle.TotalSpace (Fin V.rank → ℂ) V.Fiber)

/-- The actual zero section, retained when supplying cohomological pullbacks. -/
def zeroSection (V : NativeComplexBundle) : V.base → V.total :=
  Bundle.zeroSection (Fin V.rank → ℂ) V.Fiber

/-- The actual bundle projection. -/
def projection (V : NativeComplexBundle) : V.total → V.base :=
  Bundle.TotalSpace.proj

theorem projection_zeroSection (V : NativeComplexBundle) (b : V.base) :
    V.projection (V.zeroSection b) = b := rfl

theorem projection_continuous (V : NativeComplexBundle) : Continuous V.projection :=
  FiberBundle.continuous_proj _ _

theorem zeroSection_continuous (V : NativeComplexBundle) : Continuous V.zeroSection := by
  apply continuous_iff_continuousAt.mpr
  intro b
  let e := trivializationAt (Fin V.rank → ℂ) V.Fiber b
  have hb : b ∈ e.baseSet := mem_baseSet_trivializationAt _ _ b
  have hmem : V.zeroSection ⁻¹' e.source ∈ nhds b := by
    simpa only [e.source_eq, Set.preimage_preimage, Function.comp_def,
      zeroSection, Bundle.zeroSection_proj, Set.preimage_id_eq] using e.open_baseSet.mem_nhds hb
  apply (e.toPartialHomeomorph.continuousAt_iff_continuousAt_comp_left hmem).mpr
  apply (continuousAt_id.prod continuousAt_const).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hb] with x hx
  exact e.zeroSection ℂ hx

end NativeComplexBundle
end
end Sigma
