import SigmaThomNativeGysinRiemannRoch

namespace Sigma
noncomputable section

def nativeGysinSourcePair (V : NativeComplexBundle) (K : Set V.base) : NativeTopologicalPair :=
  ⟨V.base, Kᶜ⟩

def nativeGysinRelativePair (V : NativeComplexBundle) (K : Set V.base) : NativeTopologicalPair :=
  ⟨V.total, (V.zeroSection '' K)ᶜ⟩

def nativeGysinTargetPair (Y : TopCat) {X : TopCat} (f : C(X,Y)) (K : Set X) :
    NativeTopologicalPair := ⟨Y, (f '' K)ᶜ⟩

def nativeGysinForgetRelative (V : NativeComplexBundle) (K : Set V.base) :
    NativeTopologicalPair.Map V.thomPair (nativeGysinRelativePair V K) where
  continuousMap := ContinuousMap.id _
  maps_subspace := by
    rintro z hz ⟨x, hx, rfl⟩
    exact hz ⟨x, rfl⟩

def nativeGysinForgetTarget (Y : TopCat) {X : TopCat} (f : C(X,Y)) (K : Set X) :
    NativeTopologicalPair.Map (NativeTopologicalPair.absolute Y) (nativeGysinTargetPair Y f K) :=
  ⟨ContinuousMap.id _, Set.mapsTo_empty _ _⟩

variable (T : SuppliedComplexThomTheory) (V : NativeComplexBundle) (hV : T.admissible V)
  (Y : TopCat) (m n : ℕ)
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) V.base]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y]

/-- Supported source and target endpoints for the same supplied proper smooth
map. Relative groups are the actual cohomology of `(X,X\K)`, of the total space
supported at the zero section over K, and of `(Y,Y\f(K))`. The collapse maps
preserve these supports and commute with forgetting supports to the previously
specified geometric factorization. No supported RR equation is assumed. -/
structure NativeProperSupportedGysin
    (F : NativeSmoothGysinGeometry V Y m n)
    (pushK : C(V.base,Y) → (T.KBase V.base →+ T.KBase Y))
    (pushH : C(V.base,Y) → (T.HBase V.base →+ T.HBase Y))
    (S : NativeProperGysinFactorization T V hV Y m n F pushK pushH)
    (support : Set V.base)
    (pushKS : (f : C(V.base,Y)) → T.K.value (nativeGysinSourcePair V support) →+
      T.K.value (nativeGysinTargetPair Y f support))
    (pushHS : (f : C(V.base,Y)) → T.H.value (nativeGysinSourcePair V support) →+
      T.H.value (nativeGysinTargetPair Y f support)) where
  compact : IsCompact support
  [kSourceModule : Module (T.KBase V.base) (T.K.value (nativeGysinSourcePair V support))]
  [hSourceModule : Module (T.HBase V.base) (T.H.value (nativeGysinSourcePair V support))]
  [kRelativeModule : Module (T.KBase V.base) (T.K.value (nativeGysinRelativePair V support))]
  [hRelativeModule : Module (T.HBase V.base) (T.H.value (nativeGysinRelativePair V support))]
  thom : NativeSupportedThom
    (KS := T.K.value (nativeGysinSourcePair V support))
    (HS := T.H.value (nativeGysinSourcePair V support))
    (KRS := T.K.value (nativeGysinRelativePair V support))
    (HRS := T.H.value (nativeGysinRelativePair V support)) (T.context V hV)
  ch_source : thom.chSource = T.ch (nativeGysinSourcePair V support)
  ch_relative : thom.chRelative = T.ch (nativeGysinRelativePair V support)
  collapse : thom.Collapse
    (KY := T.K.value (nativeGysinTargetPair Y F.map support))
    (HY := T.H.value (nativeGysinTargetPair Y F.map support))
  ch_target : collapse.chTarget = T.ch (nativeGysinTargetPair Y F.map support)
  k_factorization : collapse.kGysin = pushKS F.map
  h_factorization : collapse.hGysin = pushHS F.map
  k_forget : ∀ u, T.kAbsolute Y (T.K.pull (nativeGysinForgetTarget Y F.map support)
    (collapse.kMap u)) = S.collapseContext.kCollapse
      (T.K.pull (nativeGysinForgetRelative V support) u)
  h_forget : ∀ u, T.hAbsolute Y (T.H.pull (nativeGysinForgetTarget Y F.map support)
    (collapse.hMap u)) = S.collapseContext.hCollapse
      (T.H.pull (nativeGysinForgetRelative V support) u)

namespace NativeProperSupportedGysin
variable {T V hV Y m n}
  {F : NativeSmoothGysinGeometry V Y m n}
  {pushK : C(V.base,Y) → (T.KBase V.base →+ T.KBase Y)}
  {pushH : C(V.base,Y) → (T.HBase V.base →+ T.HBase Y)}
  {S : NativeProperGysinFactorization T V hV Y m n F pushK pushH}
  {support : Set V.base}
  {pushKS : (f : C(V.base,Y)) → T.K.value (nativeGysinSourcePair V support) →+
    T.K.value (nativeGysinTargetPair Y f support)}
  {pushHS : (f : C(V.base,Y)) → T.H.value (nativeGysinSourcePair V support) →+
    T.H.value (nativeGysinTargetPair Y f support)}

/-- Riemann--Roch on native supported classes for the same geometric map.
The supported Thom correction is derived from primitive cups; the ordinary
normal Todd identification is discharged by universal line/splitting. -/
theorem riemann_roch_of_chern_roots
    (C : NativeProperSupportedGysin T V hV Y m n F pushK pushH S support pushKS pushHS)
    {U : NativeUniversalBundleTower T} (N : NativeThomSplit T U V hV)
    (A : NativeGysinVirtualData T V Y m n F)
    (hRoots : Units.map N.pullback.hBase.toMonoidHom
      (A.todd (Multiplicative.ofAdd (A.bundleClass V rfl))) = N.toddRootUnit)
    (a : T.K.value (nativeGysinSourcePair V support)) :
    letI := C.hSourceModule
    T.ch (nativeGysinTargetPair Y F.map support) (pushKS F.map a) =
      pushHS F.map ((↑(A.todd (Multiplicative.ofAdd (A.relativeTangent F.map))) :
        T.HBase V.base) • T.ch (nativeGysinSourcePair V support) a) := by
  letI := C.kSourceModule
  letI := C.hSourceModule
  letI := C.kRelativeModule
  letI := C.hRelativeModule
  have h := C.collapse.stable_tangent_riemann_roch A.todd (A.bundleClass V rfl)
    (A.bundleClass (nativeGysinTrivialBundle V.base F.stabilization) rfl)
    (A.relativeTangent F.map) A.tangentNormal (A.trivialTodd _)
    (N.correction_inverse_of_todd_roots _ hRoots) a
  rw [C.ch_target, C.ch_source, C.k_factorization, C.h_factorization] at h
  exact h

end NativeProperSupportedGysin
end
end Sigma
