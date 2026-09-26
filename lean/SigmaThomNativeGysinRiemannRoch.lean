import SigmaThomNativeGysinFactorization
import SigmaThomNativeSplitting
import SigmaThomNativeSupports

namespace Sigma
noncomputable section
open scoped BigOperators

namespace NativeThomSplit
variable {T : SuppliedComplexThomTheory} {U : NativeUniversalBundleTower T}
  {V : NativeComplexBundle} {hV : T.admissible V}

/-- The actual Todd root product, evaluated as a product of units. -/
def toddRootUnit (S : NativeThomSplit T U V hV) : (T.HBase S.base)ˣ :=
  ∏ i, Units.map (S.classified i).evaluate.toMonoidHom (formalToddUnitOver ℚ)

theorem toddRootUnit_inverse (S : NativeThomSplit T U V hV) :
    (↑S.toddRootUnit⁻¹ : T.HBase S.base) = S.inverseToddRootProduct := by
  simp [toddRootUnit, inverseToddRootProduct, map_prod, Units.coe_prod,
    ← Finset.prod_inv_distrib, ← map_inv]

/-- Ordinary root normalization of the Todd class identifies the normal Thom
correction. The hypothesis contains the defining Todd root product, and does
not assume a correction or Riemann--Roch equation. -/
theorem correction_inverse_of_todd_roots (S : NativeThomSplit T U V hV)
    (td : (T.HBase V.base)ˣ)
    (hRoots : Units.map S.pullback.hBase.toMonoidHom td = S.toddRootUnit) :
    T.correction V hV = (↑td⁻¹ : T.HBase V.base) := by
  apply S.injective
  rw [S.correction_root_product]
  change S.inverseToddRootProduct = (↑(Units.map S.pullback.hBase.toMonoidHom td)⁻¹ : _)
  rw [hRoots, S.toddRootUnit_inverse]

end NativeThomSplit

namespace NativeProperGysinFactorization
variable {T : SuppliedComplexThomTheory} {V : NativeComplexBundle} {hV : T.admissible V}
  {Y : TopCat} {m n : ℕ}
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) V.base]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y]
  {F : NativeSmoothGysinGeometry V Y m n}
  {pushK : C(V.base,Y) → (T.KBase V.base →+ T.KBase Y)}
  {pushH : C(V.base,Y) → (T.HBase V.base →+ T.HBase Y)}

/-- Riemann--Roch for the actual supplied proper smooth map. Normal correction
is discharged by universal line identification and injective splitting, while
the virtual tangent value follows from its geometric stable-normal equation.
There is no assumed Thom correction or RR equality in this theorem. -/
theorem riemann_roch_of_chern_roots
    (S : NativeProperGysinFactorization T V hV Y m n F pushK pushH)
    {U : NativeUniversalBundleTower T} (N : NativeThomSplit T U V hV)
    (A : NativeGysinVirtualData T V Y m n F)
    (hRoots : Units.map N.pullback.hBase.toMonoidHom
      (A.todd (Multiplicative.ofAdd (A.bundleClass V rfl))) = N.toddRootUnit)
    (a : T.KBase V.base) :
    T.chBase Y (pushK F.map a) = pushH F.map
      (T.chBase V.base a * (↑(A.todd (Multiplicative.ofAdd (A.relativeTangent F.map))) :
        T.HBase V.base)) :=
  S.riemann_roch A (N.correction_inverse_of_todd_roots _ hRoots) a

end NativeProperGysinFactorization
end
end Sigma
