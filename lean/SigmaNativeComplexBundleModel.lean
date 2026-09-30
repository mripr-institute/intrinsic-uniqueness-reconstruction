import SigmaNativeComplexKTheory

namespace Sigma.FiniteComplexBundle
noncomputable section
open Bundle
variable {B : Type} [TopologicalSpace B]
variable (V : FiniteComplexBundle B) (F : Type) [NormedAddCommGroup F]
  [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- Changing a finite-dimensional model transports the original total-space
topology; it does not replace it by a product topology. -/
def modelTopology : TopologicalSpace (TotalSpace F V.Fiber) :=
  TopologicalSpace.induced (fun z : TotalSpace F V.Fiber =>
    (⟨z.proj, z.snd⟩ : V.Total)) V.totalTopology

local instance : TopologicalSpace (TotalSpace F V.Fiber) := modelTopology V F

def modelHomeomorph : TotalSpace F V.Fiber ≃ₜ V.Total where
  toFun z := ⟨z.proj, z.snd⟩
  invFun z := ⟨z.proj, z.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

variable (h : V.Model ≃L[ℂ] F)

def modelTrivialization (e : Trivialization V.Model (π V.Model V.Fiber)) :
    Trivialization F (π F V.Fiber) :=
  (e.compHomeomorph (modelHomeomorph V F)).transFiberHomeomorph h.toHomeomorph

instance modelTrivialization_linear
    (e : Trivialization V.Model (π V.Model V.Fiber)) [e.IsLinear ℂ] :
    (modelTrivialization V F h e).IsLinear ℂ where
  linear b hb := by
    have he := e.linear ℂ hb
    constructor
    · intro v w
      change h (e ⟨b, v + w⟩).2 = h (e ⟨b, v⟩).2 + h (e ⟨b, w⟩).2
      rw [he.1, map_add]
    · intro c v
      change h (e ⟨b, c • v⟩).2 = c • h (e ⟨b, v⟩).2
      rw [he.2, map_smul]

def modelFiberBundle : FiberBundle F V.Fiber where
  totalSpaceMk_isInducing' b :=
    (modelHomeomorph V F).symm.isInducing.comp (FiberBundle.totalSpaceMk_isInducing V.Model V.Fiber b)
  trivializationAtlas' := modelTrivialization V F h '' trivializationAtlas V.Model V.Fiber
  trivializationAt' b := modelTrivialization V F h (trivializationAt V.Model V.Fiber b)
  mem_baseSet_trivializationAt' b := mem_baseSet_trivializationAt V.Model V.Fiber b
  trivialization_mem_atlas' b :=
    ⟨trivializationAt V.Model V.Fiber b, trivialization_mem_atlas V.Model V.Fiber b, rfl⟩

def modelVectorBundle :
    letI := modelFiberBundle V F h
    VectorBundle ℂ F V.Fiber :=
  letI := modelFiberBundle V F h
  {
  trivialization_linear' := by
    rintro _ ⟨e, he, rfl⟩
    letI : MemTrivializationAtlas e := ⟨he⟩
    exact modelTrivialization_linear V F h e
  continuousOn_coordChange' := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    letI : MemTrivializationAtlas e := ⟨he⟩
    letI : MemTrivializationAtlas e' := ⟨he'⟩
    have hc := (continuousOn_coordChange ℂ e e')
    have hc' := ((show ContinuousOn (fun _ : B => h.toContinuousLinearMap)
      (e.baseSet ∩ e'.baseSet) from continuousOn_const).clm_comp hc).clm_comp
      (show ContinuousOn (fun _ : B => h.symm.toContinuousLinearMap)
        (e.baseSet ∩ e'.baseSet) from continuousOn_const)
    apply hc'.congr
    intro b hb
    ext v
    change Trivialization.coordChangeL ℂ (modelTrivialization V F h e)
      (modelTrivialization V F h e') b v = h (Trivialization.coordChangeL ℂ e e' b (h.symm v))
    rw [Trivialization.coordChangeL_apply', Trivialization.coordChangeL_apply']
    · rfl
    · exact hb
    · exact hb
  }

/-- The same native bundle, expressed with a different finite-dimensional model. -/
def withModel : FiniteComplexBundle B where
  Model := F
  Fiber := V.Fiber
  totalTopology := modelTopology V F
  fiberBundle := modelFiberBundle V F h
  vectorBundle := modelVectorBundle V F h

def withModelIso : Iso (withModel V F h) V where
  fiber b := LinearEquiv.refl ℂ (V.Fiber b)
  continuous := (modelHomeomorph V F).continuous
  continuous_symm := (modelHomeomorph V F).symm.continuous

end
end Sigma.FiniteComplexBundle
