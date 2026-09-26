import SigmaThomNativeGysin
import SigmaThomNativeTheory

/-!
The abstract collapse computation instantiated on the actual continuous maps
of pairs and actual complex bundles of the supplied topological theory.
Relative target pairs allow relative or compact-support conventions to be
retained. No new Riemann--Roch compatibility assumption is introduced.
-/

namespace Sigma
noncomputable section
namespace SuppliedComplexThomTheory
variable (T : SuppliedComplexThomTheory)

/-- The native pullback along the supplied topological collapse map. Chern
naturality is inherited from the supplied theory on actual maps of pairs. -/
def nativeCollapse (V : NativeComplexBundle) (hV : T.admissible V) (P : NativeTopologicalPair)
    (c : NativeTopologicalPair.Map P V.thomPair) :
    NativeThomCollapse (KY := T.K.value P) (HY := T.H.value P) (T.context V hV) where
  kCollapse := T.K.pull c
  hCollapse := T.H.pull c
  chTarget := T.ch P
  naturality := T.ch_natural c

/-- The K Gysin map is genuinely Thom followed by the native collapse pullback. -/
def nativeKGysin (V : NativeComplexBundle) (hV : T.admissible V) (P : NativeTopologicalPair)
    (c : NativeTopologicalPair.Map P V.thomPair) : T.KBase V.base →+ T.K.value P :=
  (T.nativeCollapse V hV P c).kGysin

/-- The H Gysin map uses the same map of pairs with the cohomological Thom map. -/
def nativeHGysin (V : NativeComplexBundle) (hV : T.admissible V) (P : NativeTopologicalPair)
    (c : NativeTopologicalPair.Map P V.thomPair) : T.HBase V.base →+ T.H.value P :=
  (T.nativeCollapse V hV P c).hGysin

theorem native_gysin_comparison (V : NativeComplexBundle) (hV : T.admissible V) (P : NativeTopologicalPair)
    (c : NativeTopologicalPair.Map P V.thomPair) (a : T.KBase V.base) :
    T.ch P (T.nativeKGysin V hV P c a) =
      T.nativeHGysin V hV P c (T.chBase V.base a * T.correction V hV) :=
  (T.nativeCollapse V hV P c).comparison a

/-- For an embedding this is the normal-bundle Riemann--Roch identity, on
every input class, obtained from the already proved bundle comparison. -/
theorem native_gysin_normal_rr (V : NativeComplexBundle) (hV : T.admissible V) (P : NativeTopologicalPair)
    (c : NativeTopologicalPair.Map P V.thomPair) (tdNormal : (T.HBase V.base)ˣ)
    (hNormal : T.correction V hV = (↑tdNormal⁻¹ : T.HBase V.base))
    (a : T.KBase V.base) :
    T.ch P (T.nativeKGysin V hV P c a) =
      T.nativeHGysin V hV P c (T.chBase V.base a * (↑tdNormal⁻¹ : T.HBase V.base)) :=
  (T.nativeCollapse V hV P c).normal_riemann_roch tdNormal hNormal a

/-- The stable virtual-tangent form for a supplied collapse factorization.
The virtual class convention and trivial-bundle normalization are retained;
their group laws supply the sign, rather than an assumed RR identity. -/
theorem native_gysin_stable_tangent_rr
    (V : NativeComplexBundle) (hV : T.admissible V) (P : NativeTopologicalPair)
    (c : NativeTopologicalPair.Map P V.thomPair)
    {G : Type*} [AddCommGroup G] (td : Multiplicative G →* (T.HBase V.base)ˣ)
    (normal stable tangent : G) (hTangent : tangent = stable - normal)
    (hStable : td (Multiplicative.ofAdd stable) = 1)
    (hNormal : T.correction V hV =
      (↑(td (Multiplicative.ofAdd normal))⁻¹ : T.HBase V.base))
    (a : T.KBase V.base) :
    T.ch P (T.nativeKGysin V hV P c a) =
      T.nativeHGysin V hV P c
        (T.chBase V.base a * (↑(td (Multiplicative.ofAdd tangent)) : T.HBase V.base)) :=
  (T.nativeCollapse V hV P c).stable_tangent_riemann_roch
    td normal stable tangent hTangent hStable hNormal a

end SuppliedComplexThomTheory
end
end Sigma
