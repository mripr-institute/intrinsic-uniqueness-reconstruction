import SigmaThomNativeBundles
import SigmaThomNativeNaturality

namespace Sigma
noncomputable section

/-- An actual topological pair, including the punctured-total-space pairs used
for relative Thom groups. -/
structure NativeTopologicalPair where
  space : TopCat
  subspace : Set space

namespace NativeTopologicalPair

def absolute (B : TopCat) : NativeTopologicalPair := ⟨B, ∅⟩

structure Map (P Q : NativeTopologicalPair) where
  continuousMap : C(P.space, Q.space)
  maps_subspace : Set.MapsTo continuousMap P.subspace Q.subspace

def Map.id (P : NativeTopologicalPair) : Map P P := ⟨ContinuousMap.id _, fun _ h => h⟩
def Map.comp {P Q R : NativeTopologicalPair} (g : Map Q R) (f : Map P Q) : Map P R :=
  ⟨g.continuousMap.comp f.continuousMap, g.maps_subspace.comp f.maps_subspace⟩

def absoluteMap {B C : TopCat} (f : C(B,C)) : Map (absolute B) (absolute C) :=
  ⟨f, Set.mapsTo_empty _ _⟩

end NativeTopologicalPair

namespace NativeComplexBundle

def thomPair (V : NativeComplexBundle) : NativeTopologicalPair :=
  ⟨V.total, (Set.range V.zeroSection)ᶜ⟩

def zeroSectionPairMap (V : NativeComplexBundle) :
    NativeTopologicalPair.Map (NativeTopologicalPair.absolute V.base) V.thomPair :=
  ⟨⟨V.zeroSection, V.zeroSection_continuous⟩, Set.mapsTo_empty _ _⟩

end NativeComplexBundle

/-- A supplied contravariant relative cohomology group functor on actual
continuous maps of topological pairs. The ordinary/K-theoretic foundations are
supplied as in F4; the correction theorem constructs no replacement topology. -/
structure NativeRelativeTheory where
  value : NativeTopologicalPair → Type
  [group : ∀ P, AddCommGroup (value P)]
  pull : {P Q : NativeTopologicalPair} → NativeTopologicalPair.Map P Q → value Q →+ value P
  pull_id : ∀ P x, pull (NativeTopologicalPair.Map.id P) x = x
  pull_comp : ∀ {P Q R} (g : NativeTopologicalPair.Map Q R) (f : NativeTopologicalPair.Map P Q) x,
    pull (g.comp f) x = pull f (pull g x)

attribute [instance] NativeRelativeTheory.group

namespace NativeRelativeTheory
abbrev base (T : NativeRelativeTheory) (B : TopCat) := T.value (NativeTopologicalPair.absolute B)
abbrev relative (T : NativeRelativeTheory) (V : NativeComplexBundle) := T.value V.thomPair
end NativeRelativeTheory

/-- Supplied complex orientations and Chern character on the actual base and
relative-pair groups. Every Thom comparison below is derived from these maps.
The module structures are the usual base pullback/cup-product actions. -/
structure SuppliedComplexThomTheory where
  K : NativeRelativeTheory
  H : NativeRelativeTheory
  KBase : TopCat → Type
  HBase : TopCat → Type
  [kRing : ∀ B, CommRing (KBase B)]
  [hRing : ∀ B, CommRing (HBase B)]
  [hRational : ∀ B, Algebra ℚ (HBase B)]
  bundleClass : ∀ V : NativeComplexBundle, KBase V.base
  firstChern : ∀ V : NativeComplexBundle, HBase V.base
  kAbsolute : ∀ B, K.value (NativeTopologicalPair.absolute B) ≃+ KBase B
  hAbsolute : ∀ B, H.value (NativeTopologicalPair.absolute B) ≃+ HBase B
  [kModule : ∀ V, Module (KBase V.base) (K.relative V)]
  [hModule : ∀ V, Module (HBase V.base) (H.relative V)]
  ch : ∀ P, K.value P →+ H.value P
  chBase : ∀ B, KBase B →+* HBase B
  ch_absolute : ∀ B x, hAbsolute B (ch (NativeTopologicalPair.absolute B) x) =
    chBase B (kAbsolute B x)
  ch_natural : ∀ {P Q} (f : NativeTopologicalPair.Map P Q) x,
    ch P (K.pull f x) = H.pull f (ch Q x)
  ch_smul : ∀ (V : NativeComplexBundle) (a : KBase V.base) (u : K.relative V),
    ch V.thomPair (a • u) = chBase V.base a • ch V.thomPair u
  admissible : NativeComplexBundle → Prop
  kThom : ∀ V, admissible V → KBase V.base ≃ₗ[KBase V.base] K.relative V
  hThom : ∀ V, admissible V → HBase V.base ≃ₗ[HBase V.base] H.relative V
  zero_h_smul : ∀ (V : NativeComplexBundle) (a : HBase V.base) (u : H.relative V),
    hAbsolute V.base (H.pull V.zeroSectionPairMap (a • u)) =
      a * hAbsolute V.base (H.pull V.zeroSectionPairMap u)

attribute [instance] SuppliedComplexThomTheory.kRing SuppliedComplexThomTheory.hRing
  SuppliedComplexThomTheory.hRational SuppliedComplexThomTheory.kModule SuppliedComplexThomTheory.hModule

namespace SuppliedComplexThomTheory
variable (T : SuppliedComplexThomTheory)

def context (V : NativeComplexBundle) (hV : T.admissible V) :
    NativeThomContext (T.KBase V.base) (T.HBase V.base) (T.K.relative V) (T.H.relative V) where
  chBase := T.chBase V.base
  chRelative := T.ch V.thomPair
  ch_smul := T.ch_smul V
  kThom := T.kThom V hV
  hThom := T.hThom V hV

def correction (V : NativeComplexBundle) (hV : T.admissible V) : T.HBase V.base := (T.context V hV).correction

theorem comparison (V : NativeComplexBundle) (hV : T.admissible V) :
    T.ch V.thomPair ((T.kThom V hV) 1) = T.correction V hV • ((T.hThom V hV) 1) :=
  (T.context V hV).correction_comparison

theorem comparison_exists_unique (V : NativeComplexBundle) (hV : T.admissible V) :
    ∃! c : T.HBase V.base, T.ch V.thomPair ((T.kThom V hV) 1) = c • ((T.hThom V hV) 1) :=
  (T.context V hV).correction_exists_unique

def zeroK (V : NativeComplexBundle) : T.K.relative V →+ T.KBase V.base :=
  (T.kAbsolute V.base).toAddMonoidHom.comp (T.K.pull V.zeroSectionPairMap)

def zeroH (V : NativeComplexBundle) : T.H.relative V →ₗ[T.HBase V.base] T.HBase V.base :=
  { (T.hAbsolute V.base).toAddMonoidHom.comp (T.H.pull V.zeroSectionPairMap) with
    map_smul' := by intro a u; exact T.zero_h_smul V a u }

theorem zero_ch (V : NativeComplexBundle) (u : T.K.relative V) :
    T.chBase V.base (T.zeroK V u) = T.zeroH V (T.ch V.thomPair u) := by
  change T.chBase V.base (T.kAbsolute V.base (T.K.pull V.zeroSectionPairMap u)) =
    T.hAbsolute V.base (T.H.pull V.zeroSectionPairMap (T.ch V.thomPair u))
  rw [← T.ch_absolute, T.ch_natural]

/-- The standard line Euler identities and Chern normalization give the
primitive line interface on the actual supplied bundle/cohomology groups. -/
def line (V : NativeComplexBundle) (hV : T.admissible V) (lineClass : (T.KBase V.base)ˣ)
    (u expNeg : T.HBase V.base)
    (hk : T.zeroK V ((T.kThom V hV) 1) = 1-(↑lineClass⁻¹ : T.KBase V.base))
    (hh : T.zeroH V ((T.hThom V hV) 1) = u)
    (hch : T.chBase V.base (↑lineClass⁻¹ : T.KBase V.base) = expNeg) :
    NativeThomLine (T.context V hV) u expNeg where
  line := lineClass
  zeroK := T.zeroK V
  zeroH := T.zeroH V
  zero_ch := T.zero_ch V
  zero_kClass := hk
  zero_hClass := hh
  ch_dual := hch

theorem line_euler (V : NativeComplexBundle) (hV : T.admissible V) (lineClass : (T.KBase V.base)ˣ)
    (u expNeg : T.HBase V.base)
    (hk : T.zeroK V ((T.kThom V hV) 1) = 1-(↑lineClass⁻¹ : T.KBase V.base))
    (hh : T.zeroH V ((T.hThom V hV) 1) = u)
    (hch : T.chBase V.base (↑lineClass⁻¹ : T.KBase V.base) = expNeg) :
    u * T.correction V hV = 1-expNeg :=
  native_thom_line_euler _ (T.line V hV lineClass u expNeg hk hh hch)

end SuppliedComplexThomTheory
end
end Sigma
