import SigmaRealProjectiveNoSection

namespace Sigma
noncomputable section
open scoped LinearAlgebra.Projectivization

/-- Squaring the transition function of the actual complexified tautological
line gives the coboundary of its positive projector coordinate. -/
theorem real_projective_squared_coordinate_projector
    (p : RealProjectivePlane) (i j : Fin 3)
    (hi : p ∈ realProjectiveChart i) :
    realProjectiveProjector p i i * (realProjectiveCoordinate i j p) ^ 2 =
      realProjectiveProjector p j j := by
  induction p using Projectivization.ind with
  | h v hv =>
    have hvi : v i ≠ 0 := (real_projective_chart_mk v hv i).mp hi
    have hs : (∑ k : Fin 3, v k ^ 2) ≠ 0 := by
      have hpos : 0 < ∑ k : Fin 3, v k ^ 2 :=
        Finset.sum_pos' (fun k _ => sq_nonneg (v k))
          ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hvi⟩
      exact ne_of_gt hpos
    rw [real_projective_coordinate_mk v hv i j hvi,
      real_projective_projector_mk v hv i i,
      real_projective_projector_mk v hv j j]
    change (v i * v i / (∑ k : Fin 3, v k ^ 2)) *
      (v j / v i) ^ 2 = v j * v j / (∑ k : Fin 3, v k ^ 2)
    field_simp [hvi, hs]
    ring

theorem real_projective_projector_diagonal_pos
    (p : RealProjectivePlane) (i : Fin 3)
    (hi : p ∈ realProjectiveChart i) :
    0 < realProjectiveProjector p i i := by
  induction p using Projectivization.ind with
  | h v hv =>
    have hvi : v i ≠ 0 := (real_projective_chart_mk v hv i).mp hi
    rw [real_projective_projector_mk]
    have hs : 0 < ∑ k : Fin 3, v k ^ 2 :=
      Finset.sum_pos' (fun k _ => sq_nonneg (v k))
        ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hvi⟩
    change 0 < v i * v i / (∑ k : Fin 3, v k ^ 2)
    exact div_pos (mul_self_pos.mpr hvi) hs

/-- This is the native bundle with the square of the actual tautological
complex line's chart transitions. -/
def realProjectiveComplexSquareCore :
    VectorBundleCore ℂ RealProjectivePlane (Fin 1 → ℂ) (Fin 3) where
  baseSet := realProjectiveChart
  isOpen_baseSet := real_projective_chart_open
  indexAt p := realProjectiveComplexCore.indexAt p
  mem_baseSet_at p := realProjectiveComplexCore.mem_baseSet_at p
  coordChange i j p :=
    ((realProjectiveCoordinate i j p : ℂ) ^ 2) •
      ContinuousLinearMap.id ℂ (Fin 1 → ℂ)
  coordChange_self i p hp z := by
    simp [real_projective_coordinate_self i p hp]
  continuousOn_coordChange i j := by
    exact (((Complex.continuous_ofReal.comp_continuousOn
      (real_projective_coordinate_continuousOn i j)).pow 2).mono
        Set.inter_subset_left).smul continuousOn_const
  coordChange_comp i j k p hp z := by
    change ((realProjectiveCoordinate j k p : ℂ) ^ 2) •
      (((realProjectiveCoordinate i j p : ℂ) ^ 2) • z) =
      ((realProjectiveCoordinate i k p : ℂ) ^ 2) • z
    rw [smul_smul, ← mul_pow, ← Complex.ofReal_mul,
      real_projective_coordinate_cocycle i j k p hp.1.1 hp.1.2]

/-- The square-transition bundle has a literal nowhere-zero section. Its
fiber coordinate is the corresponding positive projector diagonal. -/
def realProjectiveSquareSection (p : RealProjectivePlane) :
    realProjectiveComplexSquareCore.Fiber p :=
  fun _ => (realProjectiveProjector p
    (realProjectiveComplexSquareCore.indexAt p)
    (realProjectiveComplexSquareCore.indexAt p) : ℂ)

theorem real_projective_square_section_nonzero (p : RealProjectivePlane) :
    realProjectiveSquareSection p ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have hp := real_projective_projector_diagonal_pos p
    (realProjectiveComplexSquareCore.indexAt p)
    (realProjectiveComplexSquareCore.mem_baseSet_at p)
  norm_num [realProjectiveSquareSection] at h0
  exact ne_of_gt hp (Complex.ofReal_injective h0)

def realProjectiveSquareSectionTotal (p : RealProjectivePlane) :
    realProjectiveComplexSquareCore.TotalSpace :=
  ⟨p, realProjectiveSquareSection p⟩

theorem real_projective_square_section_chart (p : RealProjectivePlane)
    (i : Fin 3) :
    (realProjectiveComplexSquareCore.localTriv i)
      (realProjectiveSquareSectionTotal p) =
      (p, fun _ : Fin 1 => (realProjectiveProjector p i i : ℂ)) := by
  rw [VectorBundleCore.localTriv_apply]
  apply Prod.ext
  · rfl
  · funext k
    have hh := real_projective_squared_coordinate_projector p
      (realProjectiveComplexSquareCore.indexAt p) i
      (realProjectiveComplexSquareCore.mem_baseSet_at p)
    have hh' := congrArg Complex.ofReal hh
    change ((realProjectiveCoordinate
      (realProjectiveComplexSquareCore.indexAt p) i p : ℂ) ^ 2) *
      (realProjectiveProjector p
        (realProjectiveComplexSquareCore.indexAt p)
        (realProjectiveComplexSquareCore.indexAt p) : ℂ) =
      (realProjectiveProjector p i i : ℂ)
    simpa only [Complex.ofReal_mul, Complex.ofReal_pow, mul_comm] using hh'

theorem real_projective_square_section_continuous :
    Continuous realProjectiveSquareSectionTotal := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let i := realProjectiveComplexSquareCore.indexAt p
  have hi : p ∈ realProjectiveChart i :=
    realProjectiveComplexSquareCore.mem_baseSet_at p
  have hmem : realProjectiveSquareSectionTotal ⁻¹'
      (realProjectiveComplexSquareCore.localTriv i).source ∈ nhds p := by
    change realProjectiveChart i ∈ nhds p
    exact (real_projective_chart_open i).mem_nhds hi
  apply ((realProjectiveComplexSquareCore.localTriv i).toPartialHomeomorph.continuousAt_iff_continuousAt_comp_left
    hmem).mpr
  have hcont : Continuous (fun q : RealProjectivePlane =>
      (q, fun _ : Fin 1 => (realProjectiveProjector q i i : ℂ))) :=
    continuous_id.prod_mk (continuous_pi (fun _ =>
      Complex.continuous_ofReal.comp (real_projective_projector_continuous i i)))
  apply hcont.continuousAt.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun q =>
    real_projective_square_section_chart q i)

end
end Sigma
