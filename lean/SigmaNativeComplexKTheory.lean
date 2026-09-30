import SigmaThomNativeBundleOver
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace Sigma
noncomputable section
open Bundle

/-- Finite-dimensional complex vector bundles on a fixed base. Allowing any
finite-dimensional model makes Whitney sums literal native product bundles. -/
structure FiniteComplexBundle (B : Type) [TopologicalSpace B] where
  Model : Type
  [modelNorm : NormedAddCommGroup Model]
  [modelSpace : NormedSpace ℂ Model]
  [modelFinite : FiniteDimensional ℂ Model]
  Fiber : B → Type
  [fiberTopology : ∀ b, TopologicalSpace (Fiber b)]
  [fiberAdd : ∀ b, AddCommGroup (Fiber b)]
  [fiberModule : ∀ b, Module ℂ (Fiber b)]
  [totalTopology : TopologicalSpace (TotalSpace Model Fiber)]
  [fiberBundle : FiberBundle Model Fiber]
  [vectorBundle : VectorBundle ℂ Model Fiber]

attribute [instance] FiniteComplexBundle.modelNorm FiniteComplexBundle.modelSpace
  FiniteComplexBundle.modelFinite FiniteComplexBundle.fiberTopology
  FiniteComplexBundle.fiberAdd FiniteComplexBundle.fiberModule
  FiniteComplexBundle.totalTopology FiniteComplexBundle.fiberBundle
  FiniteComplexBundle.vectorBundle

namespace FiniteComplexBundle
variable {B : Type} [TopologicalSpace B]

abbrev Total (V : FiniteComplexBundle B) := TotalSpace V.Model V.Fiber

def ofNative (V : NativeBundleOver (TopCat.of B)) : FiniteComplexBundle B where
  Model := Fin V.rank → ℂ
  Fiber := V.Fiber
  totalTopology := V.totalTopology
  fiberBundle := V.fiberBundle
  vectorBundle := V.vectorBundle

def trivial (n : ℕ) : FiniteComplexBundle B where
  Model := Fin n → ℂ
  Fiber := Bundle.Trivial B (Fin n → ℂ)

def sum (V W : FiniteComplexBundle B) : FiniteComplexBundle B where
  Model := V.Model × W.Model
  Fiber := V.Fiber ×ᵇ W.Fiber

/-- Isomorphisms retain both continuity on total spaces and complex linearity
on every fiber, over the identity of the fixed base. -/
structure Iso (V W : FiniteComplexBundle B) where
  fiber : ∀ b, V.Fiber b ≃ₗ[ℂ] W.Fiber b
  continuous : Continuous (fun z : V.Total => (⟨z.proj, fiber z.proj z.snd⟩ : W.Total))
  continuous_symm : Continuous (fun z : W.Total =>
    (⟨z.proj, (fiber z.proj).symm z.snd⟩ : V.Total))

namespace Iso
variable {V W U : FiniteComplexBundle B}

def homeomorph (e : Iso V W) : V.Total ≃ₜ W.Total where
  toFun z := ⟨z.proj, e.fiber z.proj z.snd⟩
  invFun z := ⟨z.proj, (e.fiber z.proj).symm z.snd⟩
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := e.continuous
  continuous_invFun := e.continuous_symm

def refl (V : FiniteComplexBundle B) : Iso V V where
  fiber b := LinearEquiv.refl ℂ (V.Fiber b)
  continuous := continuous_id
  continuous_symm := continuous_id

def symm (e : Iso V W) : Iso W V where
  fiber b := (e.fiber b).symm
  continuous := e.continuous_symm
  continuous_symm := e.continuous

def trans (e : Iso V W) (f : Iso W U) : Iso V U where
  fiber b := (e.fiber b).trans (f.fiber b)
  continuous := f.continuous.comp e.continuous
  continuous_symm := e.continuous_symm.comp f.continuous_symm

end Iso

def sumFst (V W : FiniteComplexBundle B) (z : (V.sum W).Total) : V.Total :=
  ⟨z.proj, z.snd.1⟩

def sumSnd (V W : FiniteComplexBundle B) (z : (V.sum W).Total) : W.Total :=
  ⟨z.proj, z.snd.2⟩

theorem continuous_sumFst (V W : FiniteComplexBundle B) : Continuous (sumFst V W) :=
  continuous_fst.comp (FiberBundle.Prod.isInducing_diag V.Model V.Fiber W.Model W.Fiber).continuous

theorem continuous_sumSnd (V W : FiniteComplexBundle B) : Continuous (sumSnd V W) :=
  continuous_snd.comp (FiberBundle.Prod.isInducing_diag V.Model V.Fiber W.Model W.Fiber).continuous

theorem continuous_sum_iff {X : Type*} [TopologicalSpace X]
    (V W : FiniteComplexBundle B) (f : X → (V.sum W).Total) :
    Continuous f ↔ Continuous (sumFst V W ∘ f) ∧ Continuous (sumSnd V W ∘ f) := by
  rw [(FiberBundle.Prod.isInducing_diag V.Model V.Fiber W.Model W.Fiber).continuous_iff]
  constructor
  · intro h
    exact ⟨continuous_fst.comp h, continuous_snd.comp h⟩
  · rintro ⟨h, h'⟩
    exact h.prod_mk h'

def Iso.sum {V W U Z : FiniteComplexBundle B} (e : Iso V W) (f : Iso U Z) :
    Iso (V.sum U) (W.sum Z) where
  fiber b := (e.fiber b).prod (f.fiber b)
  continuous := (continuous_sum_iff _ _ _).2
    ⟨e.continuous.comp (continuous_sumFst V U),
      f.continuous.comp (continuous_sumSnd V U)⟩
  continuous_symm := (continuous_sum_iff _ _ _).2
    ⟨e.continuous_symm.comp (continuous_sumFst W Z),
      f.continuous_symm.comp (continuous_sumSnd W Z)⟩

def sumComm (V W : FiniteComplexBundle B) : Iso (V.sum W) (W.sum V) where
  fiber b := LinearEquiv.prodComm ℂ (V.Fiber b) (W.Fiber b)
  continuous := (continuous_sum_iff _ _ _).2
    ⟨continuous_sumSnd V W, continuous_sumFst V W⟩
  continuous_symm := (continuous_sum_iff _ _ _).2
    ⟨continuous_sumSnd W V, continuous_sumFst W V⟩

def sumAssoc (V W U : FiniteComplexBundle B) :
    Iso ((V.sum W).sum U) (V.sum (W.sum U)) where
  fiber b := LinearEquiv.prodAssoc ℂ (V.Fiber b) (W.Fiber b) (U.Fiber b)
  continuous := (continuous_sum_iff _ _ _).2 ⟨
    (continuous_sumFst V W).comp (continuous_sumFst (V.sum W) U),
    (continuous_sum_iff _ _ _).2 ⟨
      (continuous_sumSnd V W).comp (continuous_sumFst (V.sum W) U),
      continuous_sumSnd (V.sum W) U⟩⟩
  continuous_symm := (continuous_sum_iff _ _ _).2 ⟨
    (continuous_sum_iff _ _ _).2 ⟨continuous_sumFst V (W.sum U),
      (continuous_sumFst W U).comp (continuous_sumSnd V (W.sum U))⟩,
    (continuous_sumSnd W U).comp (continuous_sumSnd V (W.sum U))⟩

def sumZero (V : FiniteComplexBundle B) : Iso (V.sum (trivial 0)) V where
  fiber b :=
    { toFun := Prod.fst
      invFun := fun v => (v, 0)
      left_inv := by intro v; exact Prod.ext rfl (by funext i; exact Fin.elim0 i)
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  continuous := continuous_sumFst V (trivial 0)
  continuous_symm := (continuous_sum_iff _ _ _).2 ⟨continuous_id, by
    exact ((Bundle.Trivial.homeomorphProd B (Fin 0 → ℂ)).symm.continuous.comp
      ((FiberBundle.continuous_proj V.Model V.Fiber).prod_mk continuous_const))⟩

def isoSetoid : Setoid (FiniteComplexBundle B) where
  r V W := Nonempty (Iso V W)
  iseqv := ⟨fun V => ⟨Iso.refl V⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- The Whitney-sum monoid of isomorphism classes of actual native bundles. -/
def Class (B : Type) [TopologicalSpace B] := Quotient (isoSetoid (B := B))

def classOf (V : FiniteComplexBundle B) : Class B := Quotient.mk _ V

instance : Zero (Class B) := ⟨classOf (trivial 0)⟩
instance : Add (Class B) := ⟨Quotient.map₂ sum (by
  intro V W ⟨e⟩ U Z ⟨f⟩
  exact ⟨e.sum f⟩)⟩

theorem class_eq_iff (V W : FiniteComplexBundle B) :
    classOf V = classOf W ↔ Nonempty (Iso V W) := Quotient.eq

instance : AddCommMonoid (Class B) where
  add_assoc := by
    intro a b c
    induction a using Quotient.inductionOn with | h V =>
    induction b using Quotient.inductionOn with | h W =>
    induction c using Quotient.inductionOn with | h U =>
    exact Quotient.sound ⟨sumAssoc V W U⟩
  add_comm := by
    intro a b
    induction a using Quotient.inductionOn with | h V =>
    induction b using Quotient.inductionOn with | h W =>
    exact Quotient.sound ⟨sumComm V W⟩
  zero_add := by
    intro a
    induction a using Quotient.inductionOn with | h V =>
    exact Quotient.sound ⟨(sumComm (trivial 0) V).trans (sumZero V)⟩
  add_zero := by
    intro a
    induction a using Quotient.inductionOn with | h V =>
    exact Quotient.sound ⟨sumZero V⟩
  nsmul := nsmulRec

/-- Complex K⁰ is the Grothendieck group of the native Whitney-sum monoid. -/
def K0 (B : Type) [TopologicalSpace B] := AddLocalization (⊤ : AddSubmonoid (Class B))

instance : AddCommMonoid (K0 B) := inferInstanceAs
  (AddCommMonoid (AddLocalization (⊤ : AddSubmonoid (Class B))))

def kClass (V : FiniteComplexBundle B) : K0 B :=
  AddLocalization.mk (classOf V) 0

theorem kClass_iso {V W : FiniteComplexBundle B} (e : Iso V W) :
    kClass V = kClass W := by
  apply congrArg (fun c : Class B =>
    AddLocalization.mk c (0 : (⊤ : AddSubmonoid (Class B))))
  exact Quotient.sound ⟨e⟩

private theorem k0_exists_neg (x : K0 B) : ∃ y : K0 B, y + x = 0 := by
  induction x using AddLocalization.induction_on with
  | H p =>
    refine ⟨AddLocalization.mk p.2.val ⟨p.1, by trivial⟩, ?_⟩
    rw [AddLocalization.mk_add]
    have h : p.2.val + p.1 = ((⟨p.1, by trivial⟩ :
        (⊤ : AddSubmonoid (Class B))) + p.2).val := add_comm _ _
    rw [h, AddLocalization.mk_self]

instance : Neg (K0 B) := ⟨fun x => (k0_exists_neg x).choose⟩

instance : AddCommGroup (K0 B) where
  neg_add_cancel x := (k0_exists_neg x).choose_spec
  zsmul := zsmulRec
  add_comm := add_comm

/-- Equality in the actual Grothendieck group supplies one common native
stabilizer. No cancellation of arbitrary bundles is assumed. -/
theorem kClass_eq_iff (V W : FiniteComplexBundle B) :
    kClass V = kClass W ↔
      ∃ S : FiniteComplexBundle B, Nonempty (Iso (V.sum S) (W.sum S)) := by
  change (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (Class B))).toMap (classOf V) =
    (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (Class B))).toMap (classOf W) ↔ _
  rw [AddSubmonoid.LocalizationMap.eq_iff_exists]
  constructor
  · rintro ⟨⟨c, _⟩, hc⟩
    induction c using Quotient.inductionOn with
    | h S =>
      have he : classOf (S.sum V) = classOf (S.sum W) := hc
      obtain ⟨e⟩ := (class_eq_iff _ _).mp he
      exact ⟨S, ⟨((sumComm V S).trans e).trans (sumComm S W)⟩⟩
  · rintro ⟨S, ⟨e⟩⟩
    refine ⟨⟨classOf S, by trivial⟩, ?_⟩
    exact Quotient.sound ⟨((sumComm S V).trans e).trans (sumComm W S)⟩

theorem kClass_sum (V W : FiniteComplexBundle B) :
    kClass (V.sum W) = kClass V + kClass W := by
  exact ((AddLocalization.addMonoidOf (⊤ : AddSubmonoid (Class B))).toMap.map_add
    (classOf V) (classOf W))

end FiniteComplexBundle
end
end Sigma
