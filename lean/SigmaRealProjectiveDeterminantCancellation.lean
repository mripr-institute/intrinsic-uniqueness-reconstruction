import SigmaRealProjectiveF5Characteristic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.VectorBundle.Constructions

namespace Sigma
noncomputable section
open Matrix
open Bundle

/-- The transition matrix for a line added to an arbitrary rank-`n`
complex bundle. Its right block is the actual stabilizer transition. -/
def lineStabilizationTransition (n : ℕ) (c : ℂ) (E : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℂ :=
  Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin 1 => c)) 0 0 E

theorem line_stabilization_transition_det (n : ℕ) (c : ℂ)
    (E : Matrix (Fin n) (Fin n) ℂ) :
    (lineStabilizationTransition n c E).det = c * E.det := by
  rw [lineStabilizationTransition, Matrix.det_fromBlocks_zero₂₁]
  simp

/-- Coordinate change on the line factor, keeping an arbitrary stabilizer
coordinate fixed. -/
def lineStabilizationCoordinateChange (n : ℕ) (c : ℂ) :
    ((Fin 1 ⊕ Fin n) → ℂ) →ₗ[ℂ] ((Fin 1 ⊕ Fin n) → ℂ) where
  toFun v s := match s with
    | Sum.inl i => c * v (Sum.inl i)
    | Sum.inr j => v (Sum.inr j)
  map_add' x y := by
    funext s
    cases s <;> simp [mul_add]
  map_smul' a x := by
    funext s
    cases s <;> simp [mul_assoc, mul_left_comm, mul_comm]

theorem line_stabilization_coordinate_change_matrix (n : ℕ) (c : ℂ) :
    LinearMap.toMatrix' (lineStabilizationCoordinateChange n c) =
      lineStabilizationTransition n c 1 := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  cases i <;> cases j <;>
    simp [lineStabilizationCoordinateChange, lineStabilizationTransition,
      Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply]

/-- Taking determinants cancels the transition of any stabilizing bundle,
regardless of its rank or topology. The coefficients `Mᵢ`, `Mⱼ` arise
from a putative actual stabilized bundle isomorphism in local charts. -/
theorem line_transition_coboundary_of_stabilized_isomorphism
    (n : ℕ) (c : ℂ) (E : Matrix (Fin n) (Fin n) ℂ)
    (Mi Mj : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℂ)
    (hE : E.det ≠ 0) (hj : Mj.det ≠ 0)
    (hcompat : Mj * lineStabilizationTransition n c E =
      lineStabilizationTransition n 1 E * Mi) :
    c = Mi.det / Mj.det := by
  have hd := congrArg Matrix.det hcompat
  rw [Matrix.det_mul, Matrix.det_mul,
    line_stabilization_transition_det,
    line_stabilization_transition_det] at hd
  have hc : Mj.det * c = Mi.det := by
    apply mul_right_cancel₀ hE
    calc
      (Mj.det * c) * E.det = Mj.det * (c * E.det) := by ring
      _ = (1 * E.det) * Mi.det := hd
      _ = Mi.det * E.det := by ring
  exact (eq_div_iff hj).mpr (by simpa only [mul_comm] using hc)

theorem line_transition_coboundary_nonzero
    (n : ℕ) (c : ℂ) (E : Matrix (Fin n) (Fin n) ℂ)
    (Mi Mj : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℂ)
    (hE : E.det ≠ 0) (hi : Mi.det ≠ 0) (hj : Mj.det ≠ 0)
    (hcompat : Mj * lineStabilizationTransition n c E =
      lineStabilizationTransition n 1 E * Mi) : c ≠ 0 := by
  rw [line_transition_coboundary_of_stabilized_isomorphism n c E Mi Mj
    hE hj hcompat]
  exact div_ne_zero hi hj

/-- An actual stabilized bundle isomorphism over the fixed RP² base. The
stabilizer is any native rank-`n` complex vector bundle on that base, including
nontrivial ones. The displayed total spaces have the Mathlib product-bundle
topology, and each map is fiberwise complex linear. -/
structure RealProjectiveStableLineIsomorphism (n : ℕ)
    (S : RealProjectivePlane → Type*)
    [∀ p, TopologicalSpace (S p)]
    [∀ p, AddCommGroup (S p)] [∀ p, Module ℂ (S p)]
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) S)]
    [FiberBundle (Fin n → ℂ) S]
    [VectorBundle ℂ (Fin n → ℂ) S] where
  totalHomeomorph : Bundle.TotalSpace ((Fin 1 → ℂ) × (Fin n → ℂ))
      (realProjectiveComplexCore.Fiber ×ᵇ S) ≃ₜ
      Bundle.TotalSpace ((Fin 1 → ℂ) × (Fin n → ℂ))
        ((Bundle.Trivial RealProjectivePlane (Fin 1 → ℂ)) ×ᵇ S)
  fiberEquiv : ∀ p,
    (realProjectiveComplexCore.Fiber p × S p) ≃ₗ[ℂ] ((Fin 1 → ℂ) × S p)
  total_apply : ∀ p z,
    totalHomeomorph ⟨p, z⟩ = ⟨p, fiberEquiv p z⟩

/-- Local determinants arising from a stabilized bundle isomorphism would
give precisely this transition relation on the native RP² line charts. -/
structure RealProjectiveLineDeterminantCoboundary where
  determinant : Fin 3 → RealProjectivePlane → ℂ
  continuousOn : ∀ i, ContinuousOn (determinant i) (realProjectiveChart i)
  nonzero : ∀ i p, p ∈ realProjectiveChart i → determinant i p ≠ 0
  compatibility : ∀ i j p, p ∈ realProjectiveChart i →
    p ∈ realProjectiveChart j →
    determinant j p * (realProjectiveCoordinate i j p : ℂ) = determinant i p

private def RealProjectiveLineDeterminantCoboundary.sectionValue
    (D : RealProjectiveLineDeterminantCoboundary) (p : RealProjectivePlane) :
    Fin 3 → ℂ :=
  (realProjectiveComplexFiberMap p
    (fun _ => (D.determinant (realProjectiveComplexCore.indexAt p) p)⁻¹)).val

private theorem RealProjectiveLineDeterminantCoboundary.sectionValue_chart
    (D : RealProjectiveLineDeterminantCoboundary) (p : RealProjectivePlane)
    (i : Fin 3) (hi : p ∈ realProjectiveChart i) (k : Fin 3) :
    D.sectionValue p k =
      (D.determinant i p)⁻¹ * (realProjectiveCoordinate i k p : ℂ) := by
  let m := realProjectiveComplexCore.indexAt p
  have hm : p ∈ realProjectiveChart m := realProjectiveComplexCore.mem_baseSet_at p
  have hd := D.compatibility m i p hm hi
  have hc := real_projective_coordinate_cocycle m i k p hm hi
  have hcC := congrArg Complex.ofReal hc
  simp only [Complex.ofReal_mul] at hcC
  change (D.determinant m p)⁻¹ * (realProjectiveCoordinate m k p : ℂ) = _
  rw [← hcC]
  have hdm := D.nonzero m p hm
  have hdi := D.nonzero i p hi
  field_simp [hdm, hdi]
  calc
    (realProjectiveCoordinate i k p : ℂ) *
        (realProjectiveCoordinate m i p : ℂ) * D.determinant i p =
      (realProjectiveCoordinate i k p : ℂ) *
        (D.determinant i p * (realProjectiveCoordinate m i p : ℂ)) := by ring
    _ = (realProjectiveCoordinate i k p : ℂ) * D.determinant m p := by rw [hd]

private theorem RealProjectiveLineDeterminantCoboundary.sectionValue_continuous
    (D : RealProjectiveLineDeterminantCoboundary) : Continuous D.sectionValue := by
  apply continuous_pi
  intro k
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨i, hi⟩ := real_projective_chart_cover p
  have hlocal : ContinuousAt
      (fun q : RealProjectivePlane =>
        (D.determinant i q)⁻¹ * (realProjectiveCoordinate i k q : ℂ)) p := by
    have hdi : ContinuousAt (D.determinant i) p :=
      (D.continuousOn i).continuousAt ((real_projective_chart_open i).mem_nhds hi)
    have hci : ContinuousAt
        (fun q : RealProjectivePlane => (realProjectiveCoordinate i k q : ℂ)) p :=
      ((Complex.continuous_ofReal.comp_continuousOn
        (real_projective_coordinate_continuousOn i k)).continuousAt
          ((real_projective_chart_open i).mem_nhds hi))
    exact hdi.inv₀ (D.nonzero i p hi) |>.mul hci
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [(real_projective_chart_open i).mem_nhds hi] with q hq
  exact D.sectionValue_chart q i hq k

/-- No continuous nonzero determinant coboundary exists for the actual
complexified tautological line. This is the RP² topological half of the
arbitrary-stabilizer determinant cancellation argument. -/
theorem real_projective_line_has_no_determinant_coboundary :
    ¬ Nonempty RealProjectiveLineDeterminantCoboundary := by
  rintro ⟨D⟩
  apply real_projective_complexification_has_no_nonvanishing_section
  refine ⟨D.sectionValue, D.sectionValue_continuous, ?_, ?_⟩
  · intro p
    exact (realProjectiveComplexFiberMap p
      (fun _ => (D.determinant (realProjectiveComplexCore.indexAt p) p)⁻¹)).property
  · intro p hz
    let m := realProjectiveComplexCore.indexAt p
    have hm : p ∈ realProjectiveChart m := realProjectiveComplexCore.mem_baseSet_at p
    have hzero := congrFun hz m
    rw [D.sectionValue_chart p m hm m,
      real_projective_coordinate_self m p hm] at hzero
    simp only [Complex.ofReal_one, mul_one] at hzero
    exact inv_ne_zero (D.nonzero m p hm) hzero

private def realProjectiveLineFrame (i : Fin 3) (p : RealProjectivePlane)
    (hi : p ∈ realProjectiveChart i) :
    (Fin 1 → ℂ) ≃ₗ[ℂ] realProjectiveComplexCore.Fiber p :=
  ((realProjectiveComplexCore.localTriv i).linearEquivAt ℂ p hi).symm

private theorem realProjectiveLineFrame_transition
    (i j : Fin 3) (p : RealProjectivePlane)
    (hi : p ∈ realProjectiveChart i) (hj : p ∈ realProjectiveChart j)
    (z : Fin 1 → ℂ) :
    realProjectiveLineFrame i p hi z =
      realProjectiveLineFrame j p hj
        ((realProjectiveCoordinate i j p : ℂ) • z) := by
  let ei := (realProjectiveComplexCore.localTriv i).linearEquivAt ℂ p hi
  let ej := (realProjectiveComplexCore.localTriv j).linearEquivAt ℂ p hj
  apply ej.injective
  have h := realProjectiveComplexCore.localTriv_coordChange_eq i j
    (show p ∈ realProjectiveComplexCore.baseSet i ∩
      realProjectiveComplexCore.baseSet j from ⟨hi, hj⟩) z
  change ej (ei.symm z) = ej (ej.symm ((realProjectiveCoordinate i j p : ℂ) • z))
  rw [ej.apply_symm_apply]
  calc
    ej (ei.symm z) =
        ((realProjectiveComplexCore.localTriv i).coordChangeL ℂ
          (realProjectiveComplexCore.localTriv j) p) z := by
      exact (Trivialization.coordChangeL_apply
        (realProjectiveComplexCore.localTriv i)
        (realProjectiveComplexCore.localTriv j) (⟨hi, hj⟩) z).symm
    _ = (realProjectiveCoordinate i j p : ℂ) • z := by
      rw [h]
      rfl

/-- The stabilizer fibers really are finite dimensional; this is obtained
from the native vector-bundle trivialization at each base point. -/
private theorem stableFiberFinite (n : ℕ) (S : RealProjectivePlane → Type*)
    [∀ p, TopologicalSpace (S p)] [∀ p, AddCommGroup (S p)]
    [∀ p, Module ℂ (S p)]
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) S)]
    [FiberBundle (Fin n → ℂ) S]
    [VectorBundle ℂ (Fin n → ℂ) S] (p : RealProjectivePlane) :
    FiniteDimensional ℂ (S p) := by
  let e := (trivializationAt (Fin n → ℂ) S p).linearEquivAt ℂ p
    (mem_baseSet_trivializationAt (Fin n → ℂ) S p)
  exact FiniteDimensional.of_injective (e : S p →ₗ[ℂ] (Fin n → ℂ)) e.injective

/-- Basis-independent determinant of an actual stabilized fiber isomorphism,
expressed in the native line chart. -/
private def RealProjectiveStableLineIsomorphism.frameDeterminant
    {n : ℕ} {S : RealProjectivePlane → Type*}
    [∀ p, TopologicalSpace (S p)] [∀ p, AddCommGroup (S p)]
    [∀ p, Module ℂ (S p)]
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) S)]
    [FiberBundle (Fin n → ℂ) S]
    [VectorBundle ℂ (Fin n → ℂ) S]
    (I : RealProjectiveStableLineIsomorphism n S)
    (i : Fin 3) (p : RealProjectivePlane)
    (hi : p ∈ realProjectiveChart i) : ℂ := by
  letI := stableFiberFinite n S p
  let e : ((Fin 1 → ℂ) × S p) ≃ₗ[ℂ] ((Fin 1 → ℂ) × S p) :=
    (realProjectiveLineFrame i p hi).prod (LinearEquiv.refl ℂ (S p)) |>.trans
      (I.fiberEquiv p)
  exact LinearMap.det (e : ((Fin 1 → ℂ) × S p) →ₗ[ℂ] ((Fin 1 → ℂ) × S p))

private theorem RealProjectiveStableLineIsomorphism.frameDeterminant_ne_zero
    {n : ℕ} {S : RealProjectivePlane → Type*}
    [∀ p, TopologicalSpace (S p)] [∀ p, AddCommGroup (S p)]
    [∀ p, Module ℂ (S p)]
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) S)]
    [FiberBundle (Fin n → ℂ) S]
    [VectorBundle ℂ (Fin n → ℂ) S]
    (I : RealProjectiveStableLineIsomorphism n S)
    (i : Fin 3) (p : RealProjectivePlane)
    (hi : p ∈ realProjectiveChart i) : I.frameDeterminant i p hi ≠ 0 := by
  letI := stableFiberFinite n S p
  let e : ((Fin 1 → ℂ) × S p) ≃ₗ[ℂ] ((Fin 1 → ℂ) × S p) :=
    (realProjectiveLineFrame i p hi).prod (LinearEquiv.refl ℂ (S p)) |>.trans
      (I.fiberEquiv p)
  change LinearMap.det (e : ((Fin 1 → ℂ) × S p) →ₗ[ℂ] ((Fin 1 → ℂ) × S p)) ≠ 0
  simpa only [LinearEquiv.coe_det] using (LinearEquiv.det e).ne_zero

section StableLocalMatrices

variable (n : ℕ) (S : RealProjectivePlane → Type*)
    [∀ p, TopologicalSpace (S p)]
    [∀ p, AddCommGroup (S p)] [∀ p, Module ℂ (S p)]
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) S)]
    [FiberBundle (Fin n → ℂ) S]
    [VectorBundle ℂ (Fin n → ℂ) S]

private def stabilizerFrame (p : RealProjectivePlane) :
    S p ≃ₗ[ℂ] (Fin n → ℂ) :=
  ((trivializationAt (Fin n → ℂ) S p).continuousLinearEquivAt ℂ p
    (mem_baseSet_trivializationAt (Fin n → ℂ) S p)).toLinearEquiv

private def lineChartFrame (i : Fin 3) (p : RealProjectivePlane)
    (hi : p ∈ realProjectiveChart i) :
    realProjectiveComplexCore.Fiber p ≃ₗ[ℂ] (Fin 1 → ℂ) :=
  ((realProjectiveComplexCore.localTriv i).continuousLinearEquivAt ℂ p hi).toLinearEquiv

private theorem line_chart_frame_change (i j : Fin 3) (p : RealProjectivePlane)
    (hi : p ∈ realProjectiveChart i) (hj : p ∈ realProjectiveChart j)
    (z : Fin 1 → ℂ) :
    lineChartFrame j p hj ((lineChartFrame i p hi).symm z) =
      (realProjectiveCoordinate i j p : ℂ) • z := by
  change ((realProjectiveComplexCore.localTriv j)
    ⟨p, (realProjectiveComplexCore.localTriv i).symm p z⟩).2 = _
  calc
    _ = (realProjectiveComplexCore.localTriv i).coordChangeL ℂ
        (realProjectiveComplexCore.localTriv j) p z :=
      ((realProjectiveComplexCore.localTriv i).coordChangeL_apply
        (R := ℂ) (realProjectiveComplexCore.localTriv j)
        (show p ∈ (realProjectiveComplexCore.localTriv i).baseSet ∩
          (realProjectiveComplexCore.localTriv j).baseSet from ⟨hi, hj⟩) z).symm
    _ = _ := by
      rw [realProjectiveComplexCore.localTriv_coordChange_eq i j ⟨hi, hj⟩ z]
      rfl

/-- Coordinate linear equivalence of an actual stabilized bundle
isomorphism, using the same local stabilizer frame on both sides. -/
def stableLineLocalEquiv
    (I : RealProjectiveStableLineIsomorphism n S) (i : Fin 3)
    (p : RealProjectivePlane) (hi : p ∈ realProjectiveChart i) :
    ((Fin 1 ⊕ Fin n) → ℂ) ≃ₗ[ℂ] ((Fin 1 ⊕ Fin n) → ℂ) :=
  let ep := LinearEquiv.sumArrowLequivProdArrow (Fin 1) (Fin n) ℂ ℂ
  let source := (lineChartFrame i p hi).prod (stabilizerFrame n S p)
  let target := (LinearEquiv.refl ℂ (Fin 1 → ℂ)).prod (stabilizerFrame n S p)
  let e := ((ep.trans source.symm).trans (I.fiberEquiv p)).trans target
  e.trans ep.symm

/-- Matrix of the actual stabilized isomorphism in the line's `i`-th
native chart. -/
def stableLineLocalMatrix
    (I : RealProjectiveStableLineIsomorphism n S) (i : Fin 3)
    (p : RealProjectivePlane) (hi : p ∈ realProjectiveChart i) :
    Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℂ :=
  LinearMap.toMatrix' (stableLineLocalEquiv n S I i p hi).toLinearMap

private theorem frame_determinant_eq_local_matrix
    (I : RealProjectiveStableLineIsomorphism n S) (i : Fin 3)
    (p : RealProjectivePlane) (hi : p ∈ realProjectiveChart i) :
    I.frameDeterminant i p hi = (stableLineLocalMatrix n S I i p hi).det := by
  letI := stableFiberFinite n S p
  let ep := LinearEquiv.sumArrowLequivProdArrow (Fin 1) (Fin n) ℂ ℂ
  let b : ((Fin 1 → ℂ) × S p) ≃ₗ[ℂ] ((Fin 1 ⊕ Fin n) → ℂ) :=
    ((LinearEquiv.refl ℂ (Fin 1 → ℂ)).prod (stabilizerFrame n S p)).trans ep.symm
  let e : ((Fin 1 → ℂ) × S p) ≃ₗ[ℂ] ((Fin 1 → ℂ) × S p) :=
    ((realProjectiveLineFrame i p hi).prod (LinearEquiv.refl ℂ (S p))).trans
      (I.fiberEquiv p)
  have he : (stableLineLocalEquiv n S I i p hi).toLinearMap =
      (b.toLinearMap.comp e.toLinearMap).comp b.symm.toLinearMap := by
    ext v
    rfl
  change LinearMap.det e.toLinearMap =
    (LinearMap.toMatrix' (stableLineLocalEquiv n S I i p hi).toLinearMap).det
  rw [LinearMap.det_toMatrix', he]
  exact (LinearMap.det_conj e.toLinearMap b).symm

private def stableLineFixedLocalEquiv
    (I : RealProjectiveStableLineIsomorphism n S)
    (eS : Trivialization (Fin n → ℂ) (π (Fin n → ℂ) S))
    [MemTrivializationAtlas eS]
    (i : Fin 3) (p : RealProjectivePlane)
    (hi : p ∈ realProjectiveChart i) (hs : p ∈ eS.baseSet) :
    ((Fin 1 ⊕ Fin n) → ℂ) ≃ₗ[ℂ] ((Fin 1 ⊕ Fin n) → ℂ) :=
  let ep := LinearEquiv.sumArrowLequivProdArrow (Fin 1) (Fin n) ℂ ℂ
  let fs := (eS.continuousLinearEquivAt ℂ p hs).toLinearEquiv
  let source := (lineChartFrame i p hi).prod fs
  let target := (LinearEquiv.refl ℂ (Fin 1 → ℂ)).prod fs
  ((ep.trans source.symm).trans (I.fiberEquiv p)).trans target |>.trans ep.symm

private theorem frame_determinant_eq_fixed_local
    (I : RealProjectiveStableLineIsomorphism n S)
    (eS : Trivialization (Fin n → ℂ) (π (Fin n → ℂ) S))
    [MemTrivializationAtlas eS]
    (i : Fin 3) (p : RealProjectivePlane)
    (hi : p ∈ realProjectiveChart i) (hs : p ∈ eS.baseSet) :
    I.frameDeterminant i p hi =
      LinearMap.det (stableLineFixedLocalEquiv n S I eS i p hi hs).toLinearMap := by
  letI := stableFiberFinite n S p
  let ep := LinearEquiv.sumArrowLequivProdArrow (Fin 1) (Fin n) ℂ ℂ
  let fs := (eS.continuousLinearEquivAt ℂ p hs).toLinearEquiv
  let b : ((Fin 1 → ℂ) × S p) ≃ₗ[ℂ] ((Fin 1 ⊕ Fin n) → ℂ) :=
    ((LinearEquiv.refl ℂ (Fin 1 → ℂ)).prod fs).trans ep.symm
  let e : ((Fin 1 → ℂ) × S p) ≃ₗ[ℂ] ((Fin 1 → ℂ) × S p) :=
    ((realProjectiveLineFrame i p hi).prod (LinearEquiv.refl ℂ (S p))).trans
      (I.fiberEquiv p)
  have he : (stableLineFixedLocalEquiv n S I eS i p hi hs).toLinearMap =
      (b.toLinearMap.comp e.toLinearMap).comp b.symm.toLinearMap := by
    ext v
    rfl
  change LinearMap.det e.toLinearMap = _
  rw [he]
  exact (LinearMap.det_conj e.toLinearMap b).symm

private theorem stable_fixed_local_equiv_continuous
    (I : RealProjectiveStableLineIsomorphism n S)
    (eS : Trivialization (Fin n → ℂ) (π (Fin n → ℂ) S))
    [MemTrivializationAtlas eS] (i : Fin 3) :
    Continuous (fun q : {p : RealProjectivePlane // p ∈ realProjectiveChart i ∩ eS.baseSet} =>
      (stableLineFixedLocalEquiv n S I eS i q.val q.property.1 q.property.2).toLinearMap.toContinuousLinearMap) := by
  let ep := LinearEquiv.sumArrowLequivProdArrow (Fin 1) (Fin n) ℂ ℂ
  let src := (realProjectiveComplexCore.localTriv i).prod eS
  let tgt := (Bundle.Trivial.trivialization RealProjectivePlane (Fin 1 → ℂ)).prod eS
  apply (continuous_clm_apply).2
  intro v
  have hsrc : Continuous (fun q : {p : RealProjectivePlane // p ∈ realProjectiveChart i ∩ eS.baseSet} =>
      (⟨q.val, src.symm q.val (ep v)⟩ :
        Bundle.TotalSpace ((Fin 1 → ℂ) × (Fin n → ℂ))
          (realProjectiveComplexCore.Fiber ×ᵇ S))) := by
    have hf : Continuous (fun q :
        {p : RealProjectivePlane // p ∈ realProjectiveChart i ∩ eS.baseSet} =>
        (q.val, ep v)) := continuous_subtype_val.prod_mk continuous_const
    have h := src.continuousOn_symm.comp_continuous
      hf (fun q :
        {p : RealProjectivePlane // p ∈ realProjectiveChart i ∩ eS.baseSet} => by
        change q.val ∈ src.baseSet ∧ True
        exact ⟨q.property, True.intro⟩)
    simpa only [Function.comp_def] using h
  have htgt : Continuous (fun q : {p : RealProjectivePlane // p ∈ realProjectiveChart i ∩ eS.baseSet} =>
      tgt (I.totalHomeomorph ⟨q.val, src.symm q.val (ep v)⟩)) := by
    apply tgt.continuousOn.comp_continuous (I.totalHomeomorph.continuous.comp hsrc)
    intro q
    change (I.totalHomeomorph ⟨q.val, src.symm q.val (ep v)⟩).proj ∈ tgt.baseSet
    rw [I.total_apply]
    exact ⟨Set.mem_univ _, q.property.2⟩
  have heval (q : {p : RealProjectivePlane // p ∈ realProjectiveChart i ∩ eS.baseSet}) :
      (stableLineFixedLocalEquiv n S I eS i q.val q.property.1 q.property.2).toLinearMap v =
      ep.symm ((tgt (I.totalHomeomorph
        ⟨q.val, src.symm q.val (ep v)⟩)).2) := by
    let fs := (eS.continuousLinearEquivAt ℂ q.val q.property.2).toLinearEquiv
    have hsrcfib : src.symm q.val (ep v) =
        ((lineChartFrame i q.val q.property.1).prod fs).symm (ep v) := by
      have hs : q.val ∈ src.baseSet := q.property
      have hp := (src.mk_symm hs (ep v)).trans
          (Trivialization.prod_symm_apply
            (realProjectiveComplexCore.localTriv i) eS q.val (ep v).1 (ep v).2)
      exact (Bundle.TotalSpace.mk_injective q.val) hp
    have htgtfib (z : (Fin 1 → ℂ) × S q.val) :
        (tgt ⟨q.val, z⟩).2 =
          ((LinearEquiv.refl ℂ (Fin 1 → ℂ)).prod fs) z := rfl
    rw [I.total_apply, hsrcfib, htgtfib]
    rfl
  simpa only [LinearMap.coe_toContinuousLinearMap', heval] using
    ep.symm.toLinearMap.continuous_of_finiteDimensional.comp
      (continuous_snd.comp htgt)

theorem stable_line_local_matrix_det_ne_zero
    (I : RealProjectiveStableLineIsomorphism n S) (i : Fin 3)
    (p : RealProjectivePlane) (hi : p ∈ realProjectiveChart i) :
    (stableLineLocalMatrix n S I i p hi).det ≠ 0 := by
  let e := stableLineLocalEquiv n S I i p hi
  have hlin : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact e.apply_symm_apply v
  have hmat : (LinearMap.toMatrix' e.toLinearMap) *
      (LinearMap.toMatrix' e.symm.toLinearMap) = 1 := by
    rw [← LinearMap.toMatrix'_comp, hlin, LinearMap.toMatrix'_id]
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  change e.toLinearMap.toMatrix'.det ≠ 0
  exact left_ne_zero_of_mul_eq_one hdet

private theorem stable_line_local_equiv_chart_change
    (I : RealProjectiveStableLineIsomorphism n S) (i j : Fin 3)
    (p : RealProjectivePlane) (hi : p ∈ realProjectiveChart i)
    (hj : p ∈ realProjectiveChart j) :
    (stableLineLocalEquiv n S I i p hi).toLinearMap =
      (stableLineLocalEquiv n S I j p hj).toLinearMap.comp
        (lineStabilizationCoordinateChange n (realProjectiveCoordinate i j p : ℂ)) := by
  let ep := LinearEquiv.sumArrowLequivProdArrow (Fin 1) (Fin n) ℂ ℂ
  let fi := (lineChartFrame i p hi).prod (stabilizerFrame n S p)
  let fj := (lineChartFrame j p hj).prod (stabilizerFrame n S p)
  let c : ℂ := realProjectiveCoordinate i j p
  have hframes (v : (Fin 1 ⊕ Fin n) → ℂ) :
      fj.symm (ep (lineStabilizationCoordinateChange n c v)) =
        fi.symm (ep v) := by
    apply fj.injective
    rw [fj.apply_symm_apply]
    change ep (lineStabilizationCoordinateChange n c v) =
      ((lineChartFrame j p hj).prod (stabilizerFrame n S p))
        (((lineChartFrame i p hi).prod (stabilizerFrame n S p)).symm (ep v))
    apply Prod.ext
    · funext k
      change c * v (Sum.inl k) =
        lineChartFrame j p hj ((lineChartFrame i p hi).symm ((ep v).1)) k
      rw [line_chart_frame_change i j p hi hj]
      rfl
    · change (fun k => v (Sum.inr k)) =
        stabilizerFrame n S p ((stabilizerFrame n S p).symm
          (fun k => v (Sum.inr k)))
      rw [LinearEquiv.apply_symm_apply]
  apply LinearMap.ext
  intro v
  change ep.symm ((LinearEquiv.refl ℂ (Fin 1 → ℂ)).prod (stabilizerFrame n S p)
      (I.fiberEquiv p (fi.symm (ep v)))) =
    ep.symm ((LinearEquiv.refl ℂ (Fin 1 → ℂ)).prod (stabilizerFrame n S p)
      (I.fiberEquiv p (fj.symm (ep (lineStabilizationCoordinateChange n c v)))))
  rw [hframes]

theorem stable_line_local_matrix_chart_change
    (I : RealProjectiveStableLineIsomorphism n S) (i j : Fin 3)
    (p : RealProjectivePlane) (hi : p ∈ realProjectiveChart i)
    (hj : p ∈ realProjectiveChart j) :
    stableLineLocalMatrix n S I i p hi =
      stableLineLocalMatrix n S I j p hj *
        lineStabilizationTransition n (realProjectiveCoordinate i j p : ℂ) 1 := by
  change LinearMap.toMatrix' (stableLineLocalEquiv n S I i p hi).toLinearMap = _
  rw [stable_line_local_equiv_chart_change n S I i j p hi hj,
    LinearMap.toMatrix'_comp,
    line_stabilization_coordinate_change_matrix]
  rfl

theorem stable_line_local_determinant_chart_change
    (I : RealProjectiveStableLineIsomorphism n S) (i j : Fin 3)
    (p : RealProjectivePlane) (hi : p ∈ realProjectiveChart i)
    (hj : p ∈ realProjectiveChart j) :
    (stableLineLocalMatrix n S I j p hj).det *
      (realProjectiveCoordinate i j p : ℂ) =
        (stableLineLocalMatrix n S I i p hi).det := by
  rw [stable_line_local_matrix_chart_change n S I i j p hi hj,
    Matrix.det_mul, line_stabilization_transition_det]
  simp

private def stableFrameDeterminantChart
    (I : RealProjectiveStableLineIsomorphism n S)
    (i : Fin 3) (p : RealProjectivePlane) : ℂ := by
  classical
  exact if hi : p ∈ realProjectiveChart i then I.frameDeterminant i p hi else 0

private theorem stable_frame_determinant_chart_continuousOn
    (I : RealProjectiveStableLineIsomorphism n S) (i : Fin 3) :
    ContinuousOn (stableFrameDeterminantChart n S I i) (realProjectiveChart i) := by
  classical
  intro p hp
  let eS := trivializationAt (Fin n → ℂ) S p
  let U : Set RealProjectivePlane := realProjectiveChart i ∩ eS.baseSet
  have hU : IsOpen U := (real_projective_chart_open i).inter eS.open_baseSet
  have hpU : p ∈ U :=
    ⟨hp, mem_baseSet_trivializationAt (Fin n → ℂ) S p⟩
  have hfixed := stable_fixed_local_equiv_continuous n S I eS i
  have hdet : Continuous (fun q : U =>
      LinearMap.det
        (stableLineFixedLocalEquiv n S I eS i q.val q.property.1 q.property.2).toLinearMap) := by
    simpa only [LinearMap.det_toContinuousLinearMap] using
      (ContinuousLinearMap.continuous_det.comp hfixed)
  have hlocal : ContinuousOn (stableFrameDeterminantChart n S I i) U := by
    apply continuousOn_iff_continuous_restrict.mpr
    convert hdet using 1
    funext q
    change stableFrameDeterminantChart n S I i q.val = _
    simp only [stableFrameDeterminantChart, dif_pos q.property.1]
    exact frame_determinant_eq_fixed_local n S I eS i q.val
      q.property.1 q.property.2
  exact (hlocal.continuousAt (hU.mem_nhds hpU)).continuousWithinAt

/-- Every actual stable bundle isomorphism produces a continuous nonzero
determinant coboundary on the native RP² line charts. -/
def stable_isomorphism_determinant_coboundary
    (I : RealProjectiveStableLineIsomorphism n S) :
    RealProjectiveLineDeterminantCoboundary where
  determinant := stableFrameDeterminantChart n S I
  continuousOn := stable_frame_determinant_chart_continuousOn n S I
  nonzero := by
    intro i p hi
    simp only [stableFrameDeterminantChart, dif_pos hi]
    exact I.frameDeterminant_ne_zero i p hi
  compatibility := by
    intro i j p hi hj
    simp only [stableFrameDeterminantChart, dif_pos hi, dif_pos hj]
    rw [frame_determinant_eq_local_matrix n S I i p hi,
      frame_determinant_eq_local_matrix n S I j p hj]
    exact stable_line_local_determinant_chart_change n S I i j p hi hj

/-- The complexified tautological line cannot become trivial after adding
any native finite-rank complex bundle on the same RP² base. -/
theorem real_projective_complex_line_not_stably_trivial
    (n : ℕ) (S : RealProjectivePlane → Type*)
    [∀ p, TopologicalSpace (S p)]
    [∀ p, AddCommGroup (S p)] [∀ p, Module ℂ (S p)]
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) S)]
    [FiberBundle (Fin n → ℂ) S]
    [VectorBundle ℂ (Fin n → ℂ) S] :
    ¬ Nonempty (RealProjectiveStableLineIsomorphism n S) := by
  rintro ⟨I⟩
  exact real_projective_line_has_no_determinant_coboundary
    ⟨stable_isomorphism_determinant_coboundary n S I⟩

end StableLocalMatrices

end
end Sigma
