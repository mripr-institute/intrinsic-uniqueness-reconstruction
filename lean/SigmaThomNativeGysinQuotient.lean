import SigmaThomNativeGysinMaps
import Mathlib.Topology.Constructions

namespace Sigma
noncomputable section

/-- Collapse exactly the specified boundary subspace of a topological pair. -/
def nativeCollapseSetoid (P : NativeTopologicalPair) : Setoid P.space where
  r x y := x = y ∨ x ∈ P.subspace ∧ y ∈ P.subspace
  iseqv := ⟨fun _ => Or.inl rfl, fun h => h.elim (fun h => Or.inl h.symm)
    (fun h => Or.inr h.symm), by
      intro x y z hxy hyz
      rcases hxy with rfl | ⟨hx,hy⟩
      · exact hyz
      · rcases hyz with rfl | ⟨_,hz⟩
        · exact Or.inr ⟨hx,hy⟩
        · exact Or.inr ⟨hx,hz⟩⟩

/-- Adjoin a basepoint before collapsing the boundary; this also handles an
empty boundary (in particular, a rank-zero normal bundle). -/
def nativeBasedPair (P : NativeTopologicalPair) : NativeTopologicalPair :=
  ⟨TopCat.of (P.space ⊕ Unit), {x | match x with
    | Sum.inl p => p ∈ P.subspace
    | Sum.inr _ => True}⟩

def nativeQuotientPair (P : NativeTopologicalPair) : NativeTopologicalPair :=
  ⟨TopCat.of (Quotient (nativeCollapseSetoid (nativeBasedPair P))),
    {Quotient.mk _ (Sum.inr Unit.unit)}⟩

def nativeQuotientPoint (P : NativeTopologicalPair) : (nativeQuotientPair P).space :=
  Quotient.mk _ (Sum.inr Unit.unit)

def nativeQuotientProjection (P : NativeTopologicalPair) :
    NativeTopologicalPair.Map P (nativeQuotientPair P) where
  continuousMap := ⟨fun x => Quotient.mk _ (Sum.inl x),
    continuous_quotient_mk'.comp continuous_inl⟩
  maps_subspace := by
    intro x hx
    exact Quotient.sound (Or.inr ⟨hx, trivial⟩)

/-- Supplied disk/sphere model and the native relative/reduced comparison
isomorphisms. Both isomorphisms are tied to the actual pullback maps, so the
Chern compatibility follows from naturality and is not an extra RR premise. -/
structure NativeThomQuotientModel (T : SuppliedComplexThomTheory) (V : NativeComplexBundle) where
  diskPair : NativeTopologicalPair
  inclusion : NativeTopologicalPair.Map diskPair V.thomPair
  kExcision : T.K.relative V ≃+ T.K.value diskPair
  hExcision : T.H.relative V ≃+ T.H.value diskPair
  kExcision_apply : ∀ u, kExcision u = T.K.pull inclusion u
  hExcision_apply : ∀ u, hExcision u = T.H.pull inclusion u
  kQuotient : T.K.value (nativeQuotientPair diskPair) ≃+ T.K.value diskPair
  hQuotient : T.H.value (nativeQuotientPair diskPair) ≃+ T.H.value diskPair
  kQuotient_apply : ∀ u, kQuotient u = T.K.pull (nativeQuotientProjection diskPair) u
  hQuotient_apply : ∀ u, hQuotient u = T.H.pull (nativeQuotientProjection diskPair) u

namespace NativeThomQuotientModel
variable {T : SuppliedComplexThomTheory} {V : NativeComplexBundle}
variable (Q : NativeThomQuotientModel T V)

def quotientPair : NativeTopologicalPair := nativeQuotientPair Q.diskPair

def kTransport : T.K.relative V ≃+ T.K.value Q.quotientPair := Q.kExcision.trans Q.kQuotient.symm
def hTransport : T.H.relative V ≃+ T.H.value Q.quotientPair := Q.hExcision.trans Q.hQuotient.symm

theorem ch_transport (u : T.K.relative V) :
    T.ch Q.quotientPair (Q.kTransport u) = Q.hTransport (T.ch V.thomPair u) := by
  apply Q.hQuotient.injective
  change Q.hQuotient (T.ch (nativeQuotientPair Q.diskPair) (Q.kQuotient.symm (Q.kExcision u))) =
    Q.hQuotient (Q.hQuotient.symm (Q.hExcision (T.ch V.thomPair u)))
  rw [Q.hQuotient.apply_symm_apply, Q.hQuotient_apply,
    ← T.ch_natural (nativeQuotientProjection Q.diskPair),
    ← Q.kQuotient_apply, Q.kQuotient.apply_symm_apply,
    Q.kExcision_apply, T.ch_natural, ← Q.hExcision_apply]

/-- A genuine collapse into the quotient, composed with the supplied excision
isomorphisms, gives the relative collapse interface used in the Thom proof. -/
def collapse (hV : T.admissible V) (P : NativeTopologicalPair)
    (c : NativeTopologicalPair.Map P Q.quotientPair) :
    NativeThomCollapse (KY := T.K.value P) (HY := T.H.value P) (T.context V hV) where
  kCollapse := (T.K.pull c).comp Q.kTransport.toAddMonoidHom
  hCollapse := (T.H.pull c).comp Q.hTransport.toAddMonoidHom
  chTarget := T.ch P
  naturality := by
    intro u
    change T.ch P (T.K.pull c (Q.kTransport u)) =
      T.H.pull c (Q.hTransport (T.ch V.thomPair u))
    rw [T.ch_natural, Q.ch_transport]

theorem quotient_gysin_comparison (hV : T.admissible V) (P : NativeTopologicalPair)
    (c : NativeTopologicalPair.Map P Q.quotientPair) (a : T.KBase V.base) :
    T.ch P ((Q.collapse hV P c).kGysin a) =
      (Q.collapse hV P c).hGysin (T.chBase V.base a * T.correction V hV) :=
  (Q.collapse hV P c).comparison a

end NativeThomQuotientModel
end
end Sigma
