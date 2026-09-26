import SigmaThomNativeGysinGeometry

namespace Sigma
noncomputable section
open scoped Manifold

variable (T : SuppliedComplexThomTheory) (V : NativeComplexBundle) (hV : T.admissible V)
  (Y : TopCat) (m n : ℕ)
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) V.base]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y]

/-- The supplied collapse/excision/desuspension construction for the designated
proper smooth map. The support pair and both endpoint identifications remain
explicit. The factorization identities refer to the supplied pushforwards at
that actual map; no Chern/Todd pushforward equation is a field. -/
structure NativeProperGysinFactorization (F : NativeSmoothGysinGeometry V Y m n)
    (pushK : C(V.base,Y) → (T.KBase V.base →+ T.KBase Y))
    (pushH : C(V.base,Y) → (T.HBase V.base →+ T.HBase Y)) where
  model : NativeThomQuotientModel T V
  supportPair : NativeTopologicalPair
  collapse : NativeTopologicalPair.Map supportPair model.quotientPair
  targetInclusion : C(Y × EuclideanSpace ℝ (Fin (2*F.stabilization)), supportPair.space)
  targetInclusionEmbedding : Topology.IsOpenEmbedding targetInclusion
  collapse_on_disk : ∀ d, collapse.continuousMap
    (targetInclusion (F.tubular (model.inclusion.continuousMap d))) =
      (nativeQuotientProjection model.diskPair).continuousMap d
  collapse_outside_disk : ∀ y, y ∉ Set.range (fun d =>
    targetInclusion (F.tubular (model.inclusion.continuousMap d))) →
      collapse.continuousMap y = nativeQuotientPoint model.diskPair
  kDesuspend : T.K.value supportPair ≃+ T.KBase Y
  hDesuspend : T.H.value supportPair ≃+ T.HBase Y
  ch_desuspend : ∀ u, T.chBase Y (kDesuspend u) = hDesuspend (T.ch supportPair u)
  k_factorization : pushK F.map = kDesuspend.toAddMonoidHom.comp
    (model.collapse hV supportPair collapse).kGysin
  h_factorization : pushH F.map = hDesuspend.toAddMonoidHom.comp
    (model.collapse hV supportPair collapse).hGysin

namespace NativeProperGysinFactorization
variable {T V hV Y m n}
  {F : NativeSmoothGysinGeometry V Y m n}
  {pushK : C(V.base,Y) → (T.KBase V.base →+ T.KBase Y)}
  {pushH : C(V.base,Y) → (T.HBase V.base →+ T.HBase Y)}
variable (S : NativeProperGysinFactorization T V hV Y m n F pushK pushH)

/-- The primitive diagram yields a native collapse interface after the actual
endpoint desuspension identifications. -/
def collapseContext : NativeThomCollapse (KY := T.KBase Y) (HY := T.HBase Y)
    (T.context V hV) where
  kCollapse := S.kDesuspend.toAddMonoidHom.comp
    (S.model.collapse hV S.supportPair S.collapse).kCollapse
  hCollapse := S.hDesuspend.toAddMonoidHom.comp
    (S.model.collapse hV S.supportPair S.collapse).hCollapse
  chTarget := (T.chBase Y).toAddMonoidHom
  naturality := by
    intro u
    change T.chBase Y (S.kDesuspend ((S.model.collapse hV S.supportPair S.collapse).kCollapse u)) = _
    rw [S.ch_desuspend]
    exact congrArg S.hDesuspend ((S.model.collapse hV S.supportPair S.collapse).naturality u)

theorem kGysin_eq : S.collapseContext.kGysin = pushK F.map := by
  rw [S.k_factorization]
  rfl

theorem hGysin_eq : S.collapseContext.hGysin = pushH F.map := by
  rw [S.h_factorization]
  rfl

include S

/-- The comparison for the supplied proper smooth map itself, with its actual
pushforwards and all support/degree transports accounted for. -/
theorem comparison (a : T.KBase V.base) :
    T.chBase Y (pushK F.map a) =
      pushH F.map (T.chBase V.base a * T.correction V hV) := by
  have h := S.collapseContext.comparison a
  rw [S.kGysin_eq, S.hGysin_eq] at h
  exact h

/-- The proper-map Riemann--Roch consequence once the normal-bundle Todd value
has been identified by the independent universal/splitting comparison theorem.
The tangent value here is indexed by the actual map of the factorization. -/
theorem riemann_roch (A : NativeGysinVirtualData T V Y m n F)
    (hNormal : T.correction V hV =
      (↑(A.todd (Multiplicative.ofAdd (A.bundleClass V rfl)))⁻¹ : T.HBase V.base))
    (a : T.KBase V.base) :
    T.chBase Y (pushK F.map a) = pushH F.map
      (T.chBase V.base a * (↑(A.todd (Multiplicative.ofAdd (A.relativeTangent F.map))) :
        T.HBase V.base)) := by
  have h := S.collapseContext.stable_tangent_riemann_roch A.todd
    (A.bundleClass V rfl)
    (A.bundleClass (nativeGysinTrivialBundle V.base F.stabilization) rfl)
    (A.relativeTangent F.map) A.tangentNormal (A.trivialTodd _) hNormal a
  rw [S.kGysin_eq, S.hGysin_eq] at h
  exact h

end NativeProperGysinFactorization
end
end Sigma
