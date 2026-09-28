import SigmaRealProjectiveSquareNativeBundle

namespace Sigma
noncomputable section
open Bundle Topology
open scoped TensorProduct

private def realProjectiveTensorSquareFiberScalarEquiv (p : RealProjectivePlane) :
    RealProjectiveComplexTensorSquareFiber p ≃ₗ[ℂ] ℂ :=
  (real_projective_complex_tensor_square_total_trivialization_fiberwise_linear p).choose

private theorem real_projective_tensor_square_fiber_scalar_equiv_apply
    (p : RealProjectivePlane) (w : RealProjectiveComplexTensorSquareFiber p) :
    realProjectiveComplexTensorSquareTotalTrivialization ⟨p, w⟩ =
      (p, realProjectiveTensorSquareFiberScalarEquiv p w) :=
  (real_projective_complex_tensor_square_total_trivialization_fiberwise_linear p).choose_spec w

instance real_projective_tensor_square_fiber_topology (p : RealProjectivePlane) :
    TopologicalSpace (RealProjectiveComplexTensorSquareFiber p) :=
  TopologicalSpace.induced (realProjectiveTensorSquareFiberScalarEquiv p) inferInstance

private def complexFinOneHomeomorph : ℂ ≃ₜ (Fin 1 → ℂ) where
  toFun c := fun _ => c
  invFun z := z 0
  left_inv _ := rfl
  right_inv z := by
    funext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    rfl
  continuous_toFun := continuous_pi (fun _ => continuous_id)
  continuous_invFun := continuous_apply 0

/-- The actual tensor-square total space is homeomorphic over RP² to the
rank-one product bundle. -/
def realProjectiveComplexTensorSquareFinOneHomeomorph :
    RealProjectiveComplexTensorSquareTotalSpace ≃ₜ
      (RealProjectivePlane × (Fin 1 → ℂ)) :=
  realProjectiveComplexTensorSquareTotalTrivialization.trans
    ((Homeomorph.refl RealProjectivePlane).prodCongr complexFinOneHomeomorph)

private theorem real_projective_complex_tensor_square_fin_one_projection
    (z : RealProjectiveComplexTensorSquareTotalSpace) :
    (realProjectiveComplexTensorSquareFinOneHomeomorph z).1 = z.1 := rfl

private def realProjectiveComplexTensorSquareGlobalTrivialization :
    Trivialization (Fin 1 → ℂ)
      (π (Fin 1 → ℂ) RealProjectiveComplexTensorSquareFiber) where
  toPartialHomeomorph :=
    realProjectiveComplexTensorSquareFinOneHomeomorph.toPartialHomeomorph
  baseSet := Set.univ
  open_baseSet := isOpen_univ
  source_eq := rfl
  target_eq := Set.univ_prod_univ.symm
  proj_toFun z _ := real_projective_complex_tensor_square_fin_one_projection z

private theorem real_projective_tensor_square_total_mk_isInducing
    (p : RealProjectivePlane) :
    IsInducing (fun w : RealProjectiveComplexTensorSquareFiber p =>
      (⟨p, w⟩ : RealProjectiveComplexTensorSquareTotalSpace)) := by
  apply (realProjectiveComplexTensorSquareTotalTrivialization.isInducing.of_comp_iff).mp
  have he : IsInducing (realProjectiveTensorSquareFiberScalarEquiv p) := ⟨rfl⟩
  convert isInducing_const_prod.mpr he using 1
  funext w
  exact real_projective_tensor_square_fiber_scalar_equiv_apply p w

private theorem real_projective_tensor_square_global_trivialization_fiber
    (p : RealProjectivePlane) (w : RealProjectiveComplexTensorSquareFiber p) :
    (realProjectiveComplexTensorSquareGlobalTrivialization ⟨p, w⟩).2 =
      fun _ : Fin 1 => realProjectiveTensorSquareFiberScalarEquiv p w := by
  change (fun _ : Fin 1 =>
    (realProjectiveComplexTensorSquareTotalTrivialization ⟨p, w⟩).2) = _
  rw [real_projective_tensor_square_fiber_scalar_equiv_apply]

private instance real_projective_tensor_square_global_trivialization_linear :
    realProjectiveComplexTensorSquareGlobalTrivialization.IsLinear ℂ where
  linear p _ := by
    constructor
    · intro x y
      funext k
      simp [real_projective_tensor_square_global_trivialization_fiber]
    · intro c x
      funext k
      simp [real_projective_tensor_square_global_trivialization_fiber]

instance real_projective_complex_tensor_square_fiberBundle :
    FiberBundle (Fin 1 → ℂ) RealProjectiveComplexTensorSquareFiber where
  totalSpaceMk_isInducing' := real_projective_tensor_square_total_mk_isInducing
  trivializationAtlas' := {realProjectiveComplexTensorSquareGlobalTrivialization}
  trivializationAt' _ := realProjectiveComplexTensorSquareGlobalTrivialization
  mem_baseSet_trivializationAt' _ := Set.mem_univ _
  trivialization_mem_atlas' _ := Set.mem_singleton _

instance real_projective_complex_tensor_square_vectorBundle :
    VectorBundle ℂ (Fin 1 → ℂ) RealProjectiveComplexTensorSquareFiber where
  trivialization_linear' := by
    intro e he
    have h : e = realProjectiveComplexTensorSquareGlobalTrivialization :=
      Set.mem_singleton_iff.mp he.out
    subst e
    infer_instance
  continuousOn_coordChange' := by
    intro e e' he he'
    have h : e = realProjectiveComplexTensorSquareGlobalTrivialization :=
      Set.mem_singleton_iff.mp he.out
    have h' : e' = realProjectiveComplexTensorSquareGlobalTrivialization :=
      Set.mem_singleton_iff.mp he'.out
    subst e
    subst e'
    have hconst : (fun p : RealProjectivePlane =>
        (Trivialization.coordChangeL ℂ
          realProjectiveComplexTensorSquareGlobalTrivialization
          realProjectiveComplexTensorSquareGlobalTrivialization p :
            (Fin 1 → ℂ) →L[ℂ] (Fin 1 → ℂ))) =
        fun _ => ContinuousLinearMap.id ℂ (Fin 1 → ℂ) := by
      funext p
      ext v k
      have hp : p ∈ realProjectiveComplexTensorSquareGlobalTrivialization.baseSet ∩
          realProjectiveComplexTensorSquareGlobalTrivialization.baseSet := by
        simp [realProjectiveComplexTensorSquareGlobalTrivialization]
      change (Trivialization.coordChangeL ℂ
        realProjectiveComplexTensorSquareGlobalTrivialization
        realProjectiveComplexTensorSquareGlobalTrivialization p v) k = v k
      rw [Trivialization.coordChangeL_apply _ _ hp]
      exact congrFun (congrArg Prod.snd
        (realProjectiveComplexTensorSquareGlobalTrivialization.apply_mk_symm hp.1 v)) k
    rw [hconst]
    exact continuousOn_const

/-- A native Mathlib complex vector bundle whose fibers are literally the
algebraic tensor squares of the actual complexified tautological fibers. -/
def realProjectiveComplexTensorSquareNativeBundle : NativeComplexBundle where
  base := TopCat.of RealProjectivePlane
  rank := 1
  Fiber := RealProjectiveComplexTensorSquareFiber
  fiberTopology := real_projective_tensor_square_fiber_topology
  fiberAdd := inferInstance
  fiberModule := inferInstance
  totalTopology := real_projective_complex_tensor_square_topology
  fiberBundle := real_projective_complex_tensor_square_fiberBundle
  vectorBundle := real_projective_complex_tensor_square_vectorBundle

theorem real_projective_complex_tensor_square_native_trivialization_fiberwise_linear
    (p : RealProjectivePlane) :
    ∃ e : RealProjectiveComplexTensorSquareFiber p ≃ₗ[ℂ] (Fin 1 → ℂ),
      ∀ w, realProjectiveComplexTensorSquareFinOneHomeomorph ⟨p, w⟩ =
        (p, e w) := by
  let t := realProjectiveComplexTensorSquareGlobalTrivialization
  refine ⟨t.linearEquivAt ℂ p (by simp [t, realProjectiveComplexTensorSquareGlobalTrivialization]), ?_⟩
  intro w
  apply Prod.ext
  · exact real_projective_complex_tensor_square_fin_one_projection ⟨p, w⟩
  · rfl

end
end Sigma
