import SigmaRealProjectiveSquareTriviality
import SigmaRealProjectiveSquareTransition

namespace Sigma
noncomputable section
open scoped BigOperators TensorProduct

/-- The squared-cocycle bundle already constructed for the complexified
tautological line. -/
abbrev realProjectiveComplexTensorSquareCore := realProjectiveComplexSquareCore

theorem real_projective_tensor_square_core_eq_square_core :
    realProjectiveComplexTensorSquareCore = realProjectiveComplexSquareCore := rfl

/-- The native Mathlib vector bundle whose cocycle is the tensor square of the
complexified tautological line's cocycle. -/
def realProjectiveComplexTensorSquareBundle : NativeComplexBundle where
  base := TopCat.of RealProjectivePlane
  rank := 1
  Fiber := realProjectiveComplexTensorSquareCore.Fiber

private def realProjectiveTensorSquareSectionCoordinate (i : Fin 3)
    (p : RealProjectivePlane) : ℂ := (realProjectiveProjector p i i : ℂ)

private theorem real_projective_tensor_square_coordinate_transition
    (i j : Fin 3) (p : RealProjectivePlane)
    (hi : p ∈ realProjectiveChart i) (hj : p ∈ realProjectiveChart j) :
    realProjectiveTensorSquareSectionCoordinate j p =
      (realProjectiveCoordinate i j p : ℂ) ^ 2 *
        realProjectiveTensorSquareSectionCoordinate i p := by
  induction p using Projectivization.ind with
  | h v hv =>
    have hi' := (real_projective_chart_mk v hv i).mp hi
    have hj' := (real_projective_chart_mk v hv j).mp hj
    simp only [realProjectiveTensorSquareSectionCoordinate,
      real_projective_projector_mk, real_projective_coordinate_mk v hv i j hi']
    push_cast
    field_simp [ne_of_gt (real_vector_square_pos hv), hi']
    ring

/-- A global section in the native tensor-square bundle, expressed in the
chosen chart at each point. -/
private def realProjectiveTensorSquareCoreSection
    (p : RealProjectivePlane) : realProjectiveComplexTensorSquareCore.TotalSpace :=
  ⟨p, fun _ => realProjectiveTensorSquareSectionCoordinate
    (realProjectiveComplexTensorSquareCore.indexAt p) p⟩

private theorem real_projective_tensor_square_core_section_chart
    (p : RealProjectivePlane) (i : Fin 3) (hi : p ∈ realProjectiveChart i) :
    realProjectiveComplexTensorSquareCore.localTriv i
      (realProjectiveTensorSquareCoreSection p) =
        (p, fun _ => realProjectiveTensorSquareSectionCoordinate i p) := by
  apply Prod.ext
  · rfl
  · funext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    change (realProjectiveCoordinate
      (realProjectiveComplexTensorSquareCore.indexAt p) i p : ℂ) ^ 2 *
        realProjectiveTensorSquareSectionCoordinate
          (realProjectiveComplexTensorSquareCore.indexAt p) p = _
    exact (real_projective_tensor_square_coordinate_transition
      (realProjectiveComplexTensorSquareCore.indexAt p) i p
      (realProjectiveComplexTensorSquareCore.mem_baseSet_at p) hi).symm

private def realProjectiveTensorSquareCoreTrivializeFun
    (z : realProjectiveComplexTensorSquareCore.TotalSpace) : RealProjectivePlane × ℂ :=
  (z.1, z.2 0 /
    realProjectiveTensorSquareSectionCoordinate
      (realProjectiveComplexTensorSquareCore.indexAt z.1) z.1)

private def realProjectiveTensorSquareCoreTrivializeInvFun
    (q : RealProjectivePlane × ℂ) : realProjectiveComplexTensorSquareCore.TotalSpace :=
  ⟨q.1, fun _ => q.2 * realProjectiveTensorSquareSectionCoordinate
    (realProjectiveComplexTensorSquareCore.indexAt q.1) q.1⟩

private theorem real_projective_tensor_square_core_trivialize_left_inv
    (z : realProjectiveComplexTensorSquareCore.TotalSpace) :
    realProjectiveTensorSquareCoreTrivializeInvFun
      (realProjectiveTensorSquareCoreTrivializeFun z) = z := by
  cases z with
  | mk p z =>
    change Bundle.TotalSpace.mk p
      (fun _ => (z 0 /
        realProjectiveTensorSquareSectionCoordinate
          (realProjectiveComplexTensorSquareCore.indexAt p) p) *
        realProjectiveTensorSquareSectionCoordinate
          (realProjectiveComplexTensorSquareCore.indexAt p) p) =
        Bundle.TotalSpace.mk p z
    congr 1
    funext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    have ha : realProjectiveTensorSquareSectionCoordinate
        (realProjectiveComplexTensorSquareCore.indexAt p) p ≠ 0 := by
      simp only [realProjectiveTensorSquareSectionCoordinate]
      have hc := realProjectiveComplexTensorSquareCore.mem_baseSet_at p
      change realProjectiveProjector p
        (realProjectiveComplexTensorSquareCore.indexAt p)
        (realProjectiveComplexTensorSquareCore.indexAt p) ≠ 0 at hc
      exact Complex.ofReal_ne_zero.mpr hc
    field_simp

private theorem real_projective_tensor_square_core_trivialize_right_inv
    (q : RealProjectivePlane × ℂ) :
    realProjectiveTensorSquareCoreTrivializeFun
      (realProjectiveTensorSquareCoreTrivializeInvFun q) = q := by
  apply Prod.ext
  · rfl
  · simp only [realProjectiveTensorSquareCoreTrivializeFun,
      realProjectiveTensorSquareCoreTrivializeInvFun]
    have ha : realProjectiveTensorSquareSectionCoordinate
        (realProjectiveComplexTensorSquareCore.indexAt q.1) q.1 ≠ 0 := by
      simp only [realProjectiveTensorSquareSectionCoordinate]
      have hc := realProjectiveComplexTensorSquareCore.mem_baseSet_at q.1
      change realProjectiveProjector q.1
        (realProjectiveComplexTensorSquareCore.indexAt q.1)
        (realProjectiveComplexTensorSquareCore.indexAt q.1) ≠ 0 at hc
      exact Complex.ofReal_ne_zero.mpr hc
    field_simp

private theorem real_projective_tensor_square_core_trivialize_chart
    (z : realProjectiveComplexTensorSquareCore.TotalSpace) (i : Fin 3)
    (hi : z.1 ∈ realProjectiveChart i) :
    (realProjectiveComplexTensorSquareCore.localTriv i z).2 0 /
        realProjectiveTensorSquareSectionCoordinate i z.1 =
      (realProjectiveTensorSquareCoreTrivializeFun z).2 := by
  simp only [realProjectiveTensorSquareCoreTrivializeFun, div_eq_mul_inv]
  have htrans := real_projective_tensor_square_coordinate_transition
    (realProjectiveComplexTensorSquareCore.indexAt z.1) i z.1
    (realProjectiveComplexTensorSquareCore.mem_baseSet_at z.1) hi
  have hsec : realProjectiveTensorSquareSectionCoordinate i z.1 ≠ 0 := by
    simp only [realProjectiveTensorSquareSectionCoordinate]
    change realProjectiveProjector z.1 i i ≠ 0 at hi
    exact Complex.ofReal_ne_zero.mpr hi
  have hbase :
      realProjectiveTensorSquareSectionCoordinate
        (realProjectiveComplexTensorSquareCore.indexAt z.1) z.1 ≠ 0 := by
    simp only [realProjectiveTensorSquareSectionCoordinate]
    have hc := realProjectiveComplexTensorSquareCore.mem_baseSet_at z.1
    change realProjectiveProjector z.1
      (realProjectiveComplexTensorSquareCore.indexAt z.1)
      (realProjectiveComplexTensorSquareCore.indexAt z.1) ≠ 0 at hc
    exact Complex.ofReal_ne_zero.mpr hc
  have hcoord : (realProjectiveComplexTensorSquareCore.localTriv i z).2 0 =
      (realProjectiveCoordinate
        (realProjectiveComplexTensorSquareCore.indexAt z.1) i z.1 : ℂ) ^ 2 * z.2 0 := by
    rfl
  rw [hcoord, htrans]
  have hden : (realProjectiveCoordinate
      (realProjectiveComplexTensorSquareCore.indexAt z.1) i z.1 : ℂ) ^ 2 *
        realProjectiveTensorSquareSectionCoordinate
          (realProjectiveComplexTensorSquareCore.indexAt z.1) z.1 ≠ 0 := by
    rw [← htrans]
    exact hsec
  field_simp [hden]
  ring

private theorem real_projective_tensor_square_core_inverse_chart
    (q : RealProjectivePlane × ℂ) (i : Fin 3)
    (hi : q.1 ∈ realProjectiveChart i) :
    realProjectiveComplexTensorSquareCore.localTriv i
      (realProjectiveTensorSquareCoreTrivializeInvFun q) =
        (q.1, fun _ => q.2 * realProjectiveTensorSquareSectionCoordinate i q.1) := by
  apply Prod.ext
  · rfl
  · funext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    change (realProjectiveCoordinate
      (realProjectiveComplexTensorSquareCore.indexAt q.1) i q.1 : ℂ) ^ 2 *
        (q.2 * realProjectiveTensorSquareSectionCoordinate
          (realProjectiveComplexTensorSquareCore.indexAt q.1) q.1) = _
    rw [real_projective_tensor_square_coordinate_transition
      (realProjectiveComplexTensorSquareCore.indexAt q.1) i q.1
      (realProjectiveComplexTensorSquareCore.mem_baseSet_at q.1) hi]
    ring

private theorem real_projective_tensor_square_core_trivialize_continuous :
    Continuous realProjectiveTensorSquareCoreTrivializeFun := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let i := realProjectiveComplexTensorSquareCore.indexAt z.1
  have hi : z.1 ∈ realProjectiveChart i := realProjectiveComplexTensorSquareCore.mem_baseSet_at z.1
  have hp : Continuous (fun z : realProjectiveComplexTensorSquareCore.TotalSpace => z.1) :=
    realProjectiveComplexTensorSquareCore.continuous_proj
  have hmem : (fun z : realProjectiveComplexTensorSquareCore.TotalSpace => z.1) ⁻¹'
      realProjectiveChart i ∈ nhds z :=
    (real_projective_chart_open i).preimage hp |>.mem_nhds hi
  have ht : ContinuousAt (fun z : realProjectiveComplexTensorSquareCore.TotalSpace =>
      (realProjectiveComplexTensorSquareCore.localTriv i z).2 0 /
        realProjectiveTensorSquareSectionCoordinate i z.1) z := by
    have htr := (realProjectiveComplexTensorSquareCore.localTriv i).continuousAt
      ((realProjectiveComplexTensorSquareCore.mem_localTriv_source i z).2 hi)
    have hden : ContinuousAt (fun w : realProjectiveComplexTensorSquareCore.TotalSpace =>
        realProjectiveTensorSquareSectionCoordinate i w.1) z := by
      exact Complex.continuous_ofReal.continuousAt.comp
        ((real_projective_projector_continuous i i).continuousAt.comp hp.continuousAt)
    exact (continuous_apply 0).continuousAt.comp htr.snd |>.div hden (by
      simp only [realProjectiveTensorSquareSectionCoordinate]
      exact Complex.ofReal_ne_zero.mpr hi)
  apply (hp.continuousAt.prod ht).congr_of_eventuallyEq
  filter_upwards [hmem] with w hw
  exact Prod.ext rfl (real_projective_tensor_square_core_trivialize_chart w i hw).symm

private theorem real_projective_tensor_square_core_trivialize_inverse_continuous :
    Continuous realProjectiveTensorSquareCoreTrivializeInvFun := by
  apply continuous_iff_continuousAt.mpr
  intro q
  let i := realProjectiveComplexTensorSquareCore.indexAt q.1
  have hi : q.1 ∈ realProjectiveChart i := realProjectiveComplexTensorSquareCore.mem_baseSet_at q.1
  have hp : Continuous (fun q : RealProjectivePlane × ℂ => q.1) := continuous_fst
  have hmem : realProjectiveTensorSquareCoreTrivializeInvFun ⁻¹'
      (realProjectiveComplexTensorSquareCore.localTriv i).source ∈ nhds q := by
    change (fun q : RealProjectivePlane × ℂ => q.1) ⁻¹' realProjectiveChart i ∈ nhds q
    exact (real_projective_chart_open i).preimage hp |>.mem_nhds hi
  apply ((realProjectiveComplexTensorSquareCore.localTriv i).toPartialHomeomorph.continuousAt_iff_continuousAt_comp_left
    hmem).mpr
  have hv : Continuous (fun q : RealProjectivePlane × ℂ =>
      (q.1, fun _ : Fin 1 => q.2 * realProjectiveTensorSquareSectionCoordinate i q.1)) := by
    apply continuous_fst.prod_mk
    apply continuous_pi
    intro k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    exact continuous_snd.mul (Complex.continuous_ofReal.comp
      ((real_projective_projector_continuous i i).comp continuous_fst))
  apply hv.continuousAt.congr_of_eventuallyEq
  filter_upwards [hp.continuousAt ((real_projective_chart_open i).mem_nhds hi)] with q hq
  exact real_projective_tensor_square_core_inverse_chart q i hq

/-- The total space of the bundle defined by the squared coordinate cocycle is
homeomorphic over RP² to a product. -/
def realProjectiveComplexTensorSquareBundleTrivialization :
    realProjectiveComplexTensorSquareCore.TotalSpace ≃ₜ
      (RealProjectivePlane × ℂ) where
  toFun := realProjectiveTensorSquareCoreTrivializeFun
  invFun := realProjectiveTensorSquareCoreTrivializeInvFun
  left_inv := real_projective_tensor_square_core_trivialize_left_inv
  right_inv := real_projective_tensor_square_core_trivialize_right_inv
  continuous_toFun := real_projective_tensor_square_core_trivialize_continuous
  continuous_invFun := real_projective_tensor_square_core_trivialize_inverse_continuous

theorem real_projective_tensor_square_bundle_projection_preserved
    (z : realProjectiveComplexTensorSquareCore.TotalSpace) :
    (realProjectiveComplexTensorSquareBundleTrivialization z).1 = z.1 := rfl

theorem real_projective_tensor_square_bundle_fiberwise_linear
    (p : RealProjectivePlane) :
    ∃ e : realProjectiveComplexTensorSquareCore.Fiber p ≃ₗ[ℂ] ℂ,
      ∀ z, (realProjectiveComplexTensorSquareBundleTrivialization ⟨p, z⟩).2 = e z := by
  let e : realProjectiveComplexTensorSquareCore.Fiber p ≃ₗ[ℂ] ℂ :=
    { toFun := fun z => z 0 /
        realProjectiveTensorSquareSectionCoordinate
          (realProjectiveComplexTensorSquareCore.indexAt p) p
      invFun := fun c => fun _ => c * realProjectiveTensorSquareSectionCoordinate
        (realProjectiveComplexTensorSquareCore.indexAt p) p
      left_inv := by
        intro z
        funext k
        have hk : k = 0 := Subsingleton.elim _ _
        subst k
        have ha : realProjectiveTensorSquareSectionCoordinate
            (realProjectiveComplexTensorSquareCore.indexAt p) p ≠ 0 := by
          simp only [realProjectiveTensorSquareSectionCoordinate]
          have hc := realProjectiveComplexTensorSquareCore.mem_baseSet_at p
          change realProjectiveProjector p
            (realProjectiveComplexTensorSquareCore.indexAt p)
            (realProjectiveComplexTensorSquareCore.indexAt p) ≠ 0 at hc
          exact Complex.ofReal_ne_zero.mpr hc
        simp [div_eq_mul_inv, ha]
      right_inv := by
        intro c
        have ha : realProjectiveTensorSquareSectionCoordinate
            (realProjectiveComplexTensorSquareCore.indexAt p) p ≠ 0 := by
          simp only [realProjectiveTensorSquareSectionCoordinate]
          have hc := realProjectiveComplexTensorSquareCore.mem_baseSet_at p
          change realProjectiveProjector p
            (realProjectiveComplexTensorSquareCore.indexAt p)
            (realProjectiveComplexTensorSquareCore.indexAt p) ≠ 0 at hc
          exact Complex.ofReal_ne_zero.mpr hc
        simp [div_eq_mul_inv, ha]
      map_add' := by
        intro x y
        change (x 0 + y 0) / _ = x 0 / _ + y 0 / _
        ring
      map_smul' := by
        intro c x
        change (c * x 0) / _ = c * (x 0 / _)
        ring
    }
  refine ⟨e, ?_⟩
  intro z
  rfl

/-- The squared-cocycle bundle has the concrete tensor-square incidence space
as its total space, with the latter's subspace topology from RP² × ℂ⁹. -/
def realProjectiveSquaredCocycleIncidenceHomeomorph :
    realProjectiveComplexTensorSquareCore.TotalSpace ≃ₜ
      realProjectiveTensorSquareTotalSpace :=
  realProjectiveComplexTensorSquareBundleTrivialization.trans
    realProjectiveComplexificationTensorSquareTrivialization.totalHomeomorph.symm

/-- On each base point, the total-space identification is a complex-linear
equivalence between the cocycle fiber and the tensor-square incidence fiber. -/
theorem real_projective_squared_cocycle_incidence_fiberwise_linear
    (p : RealProjectivePlane) :
    ∃ e : realProjectiveComplexTensorSquareCore.Fiber p ≃ₗ[ℂ]
      realProjectiveTensorSquareFiber p,
      ∀ z, realProjectiveSquaredCocycleIncidenceHomeomorph ⟨p, z⟩ =
        ⟨(p, (e z).1), (e z).2⟩ := by
  obtain ⟨e, he⟩ := real_projective_tensor_square_bundle_fiberwise_linear p
  let t := realProjectiveComplexificationTensorSquareTrivialization
  refine ⟨e.trans (t.fiberEquiv p).symm, ?_⟩
  intro z
  apply t.totalHomeomorph.injective
  simp only [realProjectiveSquaredCocycleIncidenceHomeomorph,
    Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
  rw [t.total_apply]
  apply Prod.ext
  · rfl
  · simpa only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] using he z

/-- The algebraic tensor square of an actual complexified tautological fiber. -/
abbrev RealProjectiveComplexTensorSquareFiber (p : RealProjectivePlane) :=
  (realProjectiveComplexification p).submodule ⊗[ℂ]
    (realProjectiveComplexification p).submodule

/-- The total family of algebraic tensor squares of the actual complexified
tautological fibers. -/
abbrev RealProjectiveComplexTensorSquareTotalSpace :=
  Bundle.TotalSpace (Fin 1 → ℂ) RealProjectiveComplexTensorSquareFiber

/-- The canonical tensor-coordinate map into the concrete incidence bundle. -/
def realProjectiveComplexTensorSquareToIncidence
    (z : RealProjectiveComplexTensorSquareTotalSpace) :
    realProjectiveTensorSquareTotalSpace :=
  ⟨(z.1, (realProjectiveComplexTensorSquareFiberEquiv z.1 z.2).1),
    (realProjectiveComplexTensorSquareFiberEquiv z.1 z.2).2⟩

theorem real_projective_complex_tensor_square_to_incidence_tmul
    (p : RealProjectivePlane)
    (x y : (realProjectiveComplexification p).submodule)
    (ij : Fin 3 × Fin 3) :
    (realProjectiveComplexTensorSquareToIncidence
      ⟨p, x ⊗ₜ[ℂ] y⟩).1.2 ij = x.1 ij.1 * y.1 ij.2 := by
  change ((realProjectiveComplexTensorSquareFiberEquiv p) (x ⊗ₜ[ℂ] y)).1 ij = _
  exact congrFun (congrArg Subtype.val
    (real_projective_complex_tensor_square_map_tmul p x y)) ij

/-- The tensor-square total space carries the topology induced by its canonical
tensor-coordinate embedding into RP² × ℂ⁹. -/
instance real_projective_complex_tensor_square_topology :
    TopologicalSpace RealProjectiveComplexTensorSquareTotalSpace :=
  TopologicalSpace.induced realProjectiveComplexTensorSquareToIncidence inferInstance

private def realProjectiveComplexTensorSquareIncidenceEquiv :
    RealProjectiveComplexTensorSquareTotalSpace ≃
      realProjectiveTensorSquareTotalSpace where
  toFun := realProjectiveComplexTensorSquareToIncidence
  invFun z := ⟨z.1.1,
    (realProjectiveComplexTensorSquareFiberEquiv z.1.1).symm ⟨z.1.2, z.2⟩⟩
  left_inv z := by
    cases z with
    | mk p w =>
      change (⟨p, (realProjectiveComplexTensorSquareFiberEquiv p).symm
        (realProjectiveComplexTensorSquareFiberEquiv p w)⟩ :
          RealProjectiveComplexTensorSquareTotalSpace) = ⟨p, w⟩
      simp
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val
        ((realProjectiveComplexTensorSquareFiberEquiv z.1.1).apply_symm_apply
          ⟨z.1.2, z.2⟩)

/-- The coordinate embedding identifies the algebraic tensor-square family
homeomorphically with its concrete incidence realization. -/
def realProjectiveComplexTensorSquareIncidenceHomeomorph :
    RealProjectiveComplexTensorSquareTotalSpace ≃ₜ
      realProjectiveTensorSquareTotalSpace :=
  realProjectiveComplexTensorSquareIncidenceEquiv.toHomeomorphOfIsInducing ⟨rfl⟩

/-- The squared-transition bundle is identified with the topologized family
whose fibers are the actual algebraic tensor squares of the complexified line. -/
def realProjectiveSquaredCocycleTensorSquareHomeomorph :
    realProjectiveComplexTensorSquareCore.TotalSpace ≃ₜ
      RealProjectiveComplexTensorSquareTotalSpace :=
  realProjectiveSquaredCocycleIncidenceHomeomorph.trans
    realProjectiveComplexTensorSquareIncidenceHomeomorph.symm

theorem real_projective_squared_cocycle_tensor_square_projection
    (z : realProjectiveComplexTensorSquareCore.TotalSpace) :
    (realProjectiveSquaredCocycleTensorSquareHomeomorph z).1 = z.1 := rfl

theorem real_projective_squared_cocycle_tensor_square_fiberwise_linear
    (p : RealProjectivePlane) :
    ∃ e : realProjectiveComplexTensorSquareCore.Fiber p ≃ₗ[ℂ]
      ((realProjectiveComplexification p).submodule ⊗[ℂ]
        (realProjectiveComplexification p).submodule),
      ∀ z, realProjectiveSquaredCocycleTensorSquareHomeomorph ⟨p, z⟩ =
        ⟨p, e z⟩ := by
  obtain ⟨e, he⟩ := real_projective_squared_cocycle_incidence_fiberwise_linear p
  refine ⟨e.trans (realProjectiveComplexTensorSquareFiberEquiv p).symm, ?_⟩
  intro z
  apply realProjectiveComplexTensorSquareIncidenceHomeomorph.injective
  simp only [realProjectiveSquaredCocycleTensorSquareHomeomorph,
    Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
  rw [he]
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (e z).1 = ((realProjectiveComplexTensorSquareFiberEquiv p)
        ((realProjectiveComplexTensorSquareFiberEquiv p).symm (e z))).1
    simp

/-- A product trivialization of the topologized family of actual algebraic
tensor squares of the complexified tautological fibers. -/
def realProjectiveComplexTensorSquareTotalTrivialization :
    RealProjectiveComplexTensorSquareTotalSpace ≃ₜ
      (RealProjectivePlane × ℂ) :=
  realProjectiveSquaredCocycleTensorSquareHomeomorph.symm.trans
    realProjectiveComplexTensorSquareBundleTrivialization

theorem real_projective_complex_tensor_square_total_trivialization_fiberwise_linear
    (p : RealProjectivePlane) :
    ∃ e : ((realProjectiveComplexification p).submodule ⊗[ℂ]
      (realProjectiveComplexification p).submodule) ≃ₗ[ℂ] ℂ,
      ∀ w, realProjectiveComplexTensorSquareTotalTrivialization ⟨p, w⟩ =
        (p, e w) := by
  obtain ⟨e₁, he₁⟩ := real_projective_squared_cocycle_tensor_square_fiberwise_linear p
  obtain ⟨e₂, he₂⟩ := real_projective_tensor_square_bundle_fiberwise_linear p
  refine ⟨e₁.symm.trans e₂, ?_⟩
  intro w
  have hinv : realProjectiveSquaredCocycleTensorSquareHomeomorph.symm ⟨p, w⟩ =
      ⟨p, e₁.symm w⟩ := by
    apply realProjectiveSquaredCocycleTensorSquareHomeomorph.injective
    rw [Homeomorph.apply_symm_apply, he₁]
    simp
  change realProjectiveComplexTensorSquareBundleTrivialization
    (realProjectiveSquaredCocycleTensorSquareHomeomorph.symm ⟨p, w⟩) =
      (p, (e₁.symm.trans e₂) w)
  rw [hinv]
  exact Prod.ext rfl (he₂ (e₁.symm w))

end
end Sigma
