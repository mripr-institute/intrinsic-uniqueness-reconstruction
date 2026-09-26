import SigmaThomNativeTheory

namespace Sigma
noncomputable section

/-- A genuine pullback identification of complex bundles: a continuous map on
bases, complex-linear fibre equivalences and the continuous induced total map. -/
structure NativeBundlePullback (W V : NativeComplexBundle) where
  base : C(W.base, V.base)
  fiber : ∀ b, W.Fiber b ≃ₗ[ℂ] V.Fiber (base b)
  continuous_total : Continuous (fun x : W.total =>
    (⟨base x.proj, fiber x.proj x.snd⟩ : V.total))

namespace NativeBundlePullback
variable {W V : NativeComplexBundle}

def total (f : NativeBundlePullback W V) : C(W.total, V.total) :=
  ⟨fun x => ⟨f.base x.proj, f.fiber x.proj x.snd⟩, f.continuous_total⟩

theorem total_zero (f : NativeBundlePullback W V) (b : W.base) :
    f.total (W.zeroSection b) = V.zeroSection (f.base b) := by
  change (⟨f.base b, f.fiber b 0⟩ : V.total) = ⟨f.base b,0⟩
  rw [map_zero]

theorem total_mem_zero_iff (f : NativeBundlePullback W V) (x : W.total) :
    f.total x ∈ Set.range V.zeroSection ↔ x ∈ Set.range W.zeroSection := by
  constructor
  · rintro ⟨b,hb⟩
    have hz : (⟨f.base x.proj, f.fiber x.proj x.snd⟩ : V.total) =
        ⟨f.base x.proj,0⟩ := by
      have hbase : b = f.base x.proj := congrArg Bundle.TotalSpace.proj hb
      subst b
      exact hb.symm
    have hf : f.fiber x.proj x.snd = 0 := Bundle.TotalSpace.mk_injective _ hz
    have hx : x.snd = 0 := (f.fiber x.proj).map_eq_zero_iff.mp hf
    refine ⟨x.proj, ?_⟩
    change (⟨x.proj,0⟩ : Bundle.TotalSpace (Fin W.rank → ℂ) W.Fiber) = x
    exact Bundle.TotalSpace.ext rfl (heq_of_eq hx.symm)
  · rintro ⟨b,rfl⟩
    exact ⟨f.base b,(f.total_zero b).symm⟩

def pairMap (f : NativeBundlePullback W V) : NativeTopologicalPair.Map W.thomPair V.thomPair :=
  ⟨f.total, fun x hx => by
    change f.total x ∉ Set.range V.zeroSection
    exact fun h => hx ((f.total_mem_zero_iff x).mp h)⟩

end NativeBundlePullback

/-- The supplied natural Thom classes and cup products along an actual
bundle pullback. Correction naturality is not included among the fields. -/
structure SuppliedThomPullback (T : SuppliedComplexThomTheory) {W V : NativeComplexBundle}
    (hW : T.admissible W) (hV : T.admissible V) (f : NativeBundlePullback W V) where
  kBase : T.KBase V.base →+* T.KBase W.base
  hBase : T.HBase V.base →+* T.HBase W.base
  kBase_pull : ∀ a, kBase a = T.kAbsolute W.base (T.K.pull (NativeTopologicalPair.absoluteMap f.base) ((T.kAbsolute V.base).symm a))
  hBase_pull : ∀ a, hBase a = T.hAbsolute W.base (T.H.pull (NativeTopologicalPair.absoluteMap f.base) ((T.hAbsolute V.base).symm a))
  h_smul : ∀ a u, T.H.pull f.pairMap (a • u) = hBase a • T.H.pull f.pairMap u
  kClass : T.K.pull f.pairMap ((T.kThom V hV) 1) = (T.kThom W hW) 1
  hClass : T.H.pull f.pairMap ((T.hThom V hV) 1) = (T.hThom W hW) 1

namespace SuppliedThomPullback
variable {T : SuppliedComplexThomTheory} {W V : NativeComplexBundle}
variable {hW : T.admissible W} {hV : T.admissible V}
variable {f : NativeBundlePullback W V}

def algebraic (P : SuppliedThomPullback T hW hV f) : NativeThomPullback (T.context V hV) (T.context W hW) where
  kBase := P.kBase
  hBase := P.hBase
  kRelative := T.K.pull f.pairMap
  hRelative := T.H.pull f.pairMap
  h_smul := P.h_smul
  kClass := P.kClass
  hClass := P.hClass
  ch := T.ch_natural f.pairMap

theorem correction_natural (P : SuppliedThomPullback T hW hV f) :
    P.hBase (T.correction V hV) = T.correction W hW := P.algebraic.correction_natural

end SuppliedThomPullback
end
end Sigma
