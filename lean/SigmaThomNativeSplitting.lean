import SigmaThomNativeUniversalBundles
import SigmaThomNativeBundleOver
import SigmaThomNativeMultiplicativity

namespace Sigma
noncomputable section
open scoped BigOperators

instance native_over_k_module (T : SuppliedComplexThomTheory) (B : TopCat)
    (V : NativeBundleOver B) : Module (T.KBase B) (T.K.relative V.bundle) := T.kModule V.bundle
instance native_over_h_module (T : SuppliedComplexThomTheory) (B : TopCat)
    (V : NativeBundleOver B) : Module (T.HBase B) (T.H.relative V.bundle) := T.hModule V.bundle

/-- The actual fibrewise finite direct sum, with its topology induced by the
base and the native total-space coordinate maps. -/
def NativeWhitneyTotal {B : TopCat} {ι : Type*} (L : ι → NativeBundleOver B) :=
  Bundle.TotalSpace (∀ i, Fin (L i).rank → ℂ) (fun b => ∀ i, (L i).Fiber b)

instance native_whitney_total_topology {B : TopCat} {ι : Type*} (L : ι → NativeBundleOver B) :
    TopologicalSpace (NativeWhitneyTotal L) :=
  TopologicalSpace.induced (fun x : NativeWhitneyTotal L =>
    (x.proj, fun i => (⟨x.proj,x.snd i⟩ : (L i).bundle.total))) inferInstance

/-- A genuine direct-sum identification over the same base, continuous on
total spaces and complex-linear on every fibre. -/
structure NativeWhitneyDecomposition {B : TopCat} {ι : Type*}
    (W : NativeBundleOver B) (L : ι → NativeBundleOver B) where
  fiber : ∀ b, W.Fiber b ≃ₗ[ℂ] (∀ i, (L i).Fiber b)
  total : W.bundle.total ≃ₜ NativeWhitneyTotal L
  total_apply : ∀ x : W.bundle.total, total x = ⟨x.proj, fiber x.proj x.snd⟩

/-- Supplied injective splitting-principle data on actual bundles. The cup
products act on the native relative Thom groups for this exact decomposition.
No correction formula is a field. -/
structure NativeThomSplit (T : SuppliedComplexThomTheory) (U : NativeUniversalBundleTower T)
    (V : NativeComplexBundle) (hV : T.admissible V) where
  base : TopCat
  bundle : NativeBundleOver base
  admissible : T.admissible bundle.bundle
  map : NativeBundlePullback bundle.bundle V
  pullback : SuppliedThomPullback T admissible hV map
  injective : Function.Injective pullback.hBase
  rank : ℕ
  lines : Fin rank → NativeBundleOver base
  lines_admissible : ∀ i, T.admissible (lines i).bundle
  classified : ∀ i, NativeClassifiedLine T U (lines i).bundle (lines_admissible i)
  decomposition : NativeWhitneyDecomposition bundle lines
  thomProduct : NativeThomProduct (T.context bundle.bundle admissible)
    (fun i => T.context (lines i).bundle (lines_admissible i))

namespace NativeThomSplit
variable {T : SuppliedComplexThomTheory} {U : NativeUniversalBundleTower T}
variable {V : NativeComplexBundle} {hV : T.admissible V}

/-- The independently specified inverse-Todd Chern-root product. Its line
series evaluations send X to the actual supplied first Chern classes. -/
def inverseToddRootProduct (S : NativeThomSplit T U V hV) : T.HBase S.base :=
  ∏ i, (S.classified i).evaluate (↑(formalToddUnitOver ℚ)⁻¹ : PowerSeries ℚ)

theorem root_evaluation_firstChern (S : NativeThomSplit T U V hV) (i : Fin S.rank) :
    (S.classified i).evaluate PowerSeries.X = T.firstChern (S.lines i).bundle :=
  (S.classified i).evaluate_X

/-- Multiplicativity on the actual split bundle is derived from native cup
products and the line comparison. -/
theorem split_correction (S : NativeThomSplit T U V hV) :
    T.correction S.bundle.bundle S.admissible = S.inverseToddRootProduct := by
  rw [SuppliedComplexThomTheory.correction, S.thomProduct.correction_product]
  apply Finset.prod_congr rfl
  intro i hi
  exact (S.classified i).correction_eq_evaluate_inverseTodd

/-- The original bundle correction pulls back to the independently defined
Chern-root product; this is the genuine splitting-principle identification. -/
theorem correction_root_product (S : NativeThomSplit T U V hV) :
    S.pullback.hBase (T.correction V hV) = S.inverseToddRootProduct := by
  rw [S.pullback.correction_natural, S.split_correction]

/-- Existence and uniqueness of the descended inverse-Todd class is proved.
Existence is not an assumed root-product equation for the unknown correction. -/
theorem inverseTodd_exists_unique (S : NativeThomSplit T U V hV) :
    ∃! c : T.HBase V.base, S.pullback.hBase c = S.inverseToddRootProduct := by
  refine ⟨T.correction V hV, S.correction_root_product, ?_⟩
  intro c hc
  exact S.injective (hc.trans S.correction_root_product.symm)

/-- The inverse-Todd characteristic class defined by descent of its prescribed
universal line series, independently of the Thom-comparison equation. -/
def inverseTodd (S : NativeThomSplit T U V hV) : T.HBase V.base :=
  Classical.choose S.inverseTodd_exists_unique

theorem inverseTodd_spec (S : NativeThomSplit T U V hV) :
    S.pullback.hBase S.inverseTodd = S.inverseToddRootProduct :=
  (Classical.choose_spec S.inverseTodd_exists_unique).1

theorem correction_eq_inverseTodd (S : NativeThomSplit T U V hV) :
    T.correction V hV = S.inverseTodd :=
  S.injective (S.correction_root_product.trans S.inverseTodd_spec.symm)

/-- The descended class does not depend on a chosen splitting/classifying
presentation, because each is identified by the intrinsic Thom comparison. -/
theorem inverseTodd_independent (S R : NativeThomSplit T U V hV) :
    S.inverseTodd = R.inverseTodd :=
  S.correction_eq_inverseTodd.symm.trans R.correction_eq_inverseTodd

end NativeThomSplit

/-- The supplied splitting principle covers every bundle in the declared
admissible category; no favorable splitting datum is left existentially
unproved for an input bundle. -/
structure NativeThomSplittingContext (T : SuppliedComplexThomTheory) where
  universal : NativeUniversalBundleTower T
  split : ∀ V (hV : T.admissible V), NativeThomSplit T universal V hV

namespace NativeThomSplittingContext
variable {T : SuppliedComplexThomTheory} (S : NativeThomSplittingContext T)

def inverseTodd (V : NativeComplexBundle) (hV : T.admissible V) : T.HBase V.base :=
  (S.split V hV).inverseTodd

/-- The exact finite-base Thom correction with all supplied geometric context
retained. The inverse-Todd class is identified by its actual Chern-root product. -/
theorem thom_comparison (V : NativeComplexBundle) (hV : T.admissible V) :
    T.ch V.thomPair ((T.kThom V hV) 1) = S.inverseTodd V hV • ((T.hThom V hV) 1) := by
  rw [T.comparison V hV, (S.split V hV).correction_eq_inverseTodd]
  rfl

theorem correction_exists_unique (V : NativeComplexBundle) (hV : T.admissible V) :
    ∃! c : T.HBase V.base, T.ch V.thomPair ((T.kThom V hV) 1) = c • ((T.hThom V hV) 1) :=
  T.comparison_exists_unique V hV

theorem full_universal_line_inverse (Q : (PowerSeries ℚ)ˣ)
    (hQ : ∀ n, thomStageMap n (↑Q⁻¹ : PowerSeries ℚ) =
      S.universal.coordinate n (T.correction (S.universal.stage n) (S.universal.admissible n))) :
    Q = formalToddUnitOver ℚ := S.universal.universal_unit_identification Q hQ

end NativeThomSplittingContext
end
end Sigma
