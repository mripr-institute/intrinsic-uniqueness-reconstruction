import SigmaRealProjectiveCech
import Mathlib.Analysis.Convex.Topology

namespace Sigma
noncomputable section
open Set Topology
open scoped LinearAlgebra.Projectivization

private theorem affine_vector_ne_zero (x y : ℝ) : ![1, x, y] ≠ (0 : Fin 3 → ℝ) := by
  intro h
  have h0 := congrFun h 0
  norm_num at h0

def realProjectiveAffinePoint (x y : ℝ) : RealProjectivePlane :=
  Projectivization.mk ℝ ![1, x, y] (affine_vector_ne_zero x y)

theorem real_projective_affine_point_continuous :
    Continuous (fun z : ℝ × ℝ => realProjectiveAffinePoint z.1 z.2) := by
  apply continuous_coinduced_rng.comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_const
  · exact continuous_fst
  · exact continuous_snd

@[simp] theorem real_projective_affine_chart_zero (x y : ℝ) :
    realProjectiveAffinePoint x y ∈ realProjectiveChart 0 := by
  rw [realProjectiveAffinePoint, real_projective_chart_mk]
  norm_num

@[simp] theorem real_projective_affine_chart_one (x y : ℝ) :
    realProjectiveAffinePoint x y ∈ realProjectiveChart 1 ↔ x ≠ 0 := by
  rw [realProjectiveAffinePoint, real_projective_chart_mk]
  rfl

@[simp] theorem real_projective_affine_chart_two (x y : ℝ) :
    realProjectiveAffinePoint x y ∈ realProjectiveChart 2 ↔ y ≠ 0 := by
  rw [realProjectiveAffinePoint, real_projective_chart_mk]
  rfl

@[simp] theorem real_projective_affine_coordinate_one (x y : ℝ) :
    realProjectiveCoordinate 0 1 (realProjectiveAffinePoint x y) = x := by
  rw [realProjectiveAffinePoint, real_projective_coordinate_mk _ _ _ _ (by norm_num)]
  simp

@[simp] theorem real_projective_affine_coordinate_two (x y : ℝ) :
    realProjectiveCoordinate 0 2 (realProjectiveAffinePoint x y) = y := by
  rw [realProjectiveAffinePoint, real_projective_coordinate_mk _ _ _ _ (by norm_num)]
  simp

theorem real_projective_affine_point_inverse (p : RealProjectivePlane)
    (hp : p ∈ realProjectiveChart 0) :
    realProjectiveAffinePoint (realProjectiveCoordinate 0 1 p)
      (realProjectiveCoordinate 0 2 p) = p := by
  have hp0 := (real_projective_chart_rep p 0).mp hp
  rw [real_projective_coordinate_rep p 0 1 hp, real_projective_coordinate_rep p 0 2 hp]
  conv_rhs => rw [← p.mk_rep]
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
  refine ⟨(p.rep 0)⁻¹, ?_⟩
  funext i
  fin_cases i <;> simp [hp0, div_eq_mul_inv] <;> ring

private def signChamber (negative : Bool) : Set ℝ :=
  if negative then Iio 0 else Ioi 0

private theorem sign_chamber_preconnected (negative : Bool) :
    IsPreconnected (signChamber negative) := by
  cases negative
  · exact (convex_Ioi (0 : ℝ)).isPreconnected
  · exact (convex_Iio (0 : ℝ)).isPreconnected

private theorem sign_chamber_nonzero {negative : Bool} {x : ℝ}
    (hx : x ∈ signChamber negative) : x ≠ 0 := by
  cases negative
  · exact ne_of_gt hx
  · exact ne_of_lt hx

private def signValue (negative : Bool) : ℝ := if negative then -1 else 1

private theorem sign_value_mem (negative : Bool) : signValue negative ∈ signChamber negative := by
  cases negative <;> norm_num [signValue, signChamber]

def realProjectiveSignPoint (a b : Bool) : RealProjectiveTripleOverlap :=
  ⟨realProjectiveAffinePoint (signValue a) (signValue b), by
    exact ⟨⟨real_projective_affine_chart_zero _ _,
      (real_projective_affine_chart_one _ _).mpr (sign_chamber_nonzero (sign_value_mem a))⟩,
      (real_projective_affine_chart_two _ _).mpr (sign_chamber_nonzero (sign_value_mem b))⟩⟩

private def chamberToTriple (a b : Bool) :
    C((signChamber a) × (signChamber b), RealProjectiveTripleOverlap) where
  toFun z := ⟨realProjectiveAffinePoint z.1.val z.2.val, by
      exact ⟨⟨real_projective_affine_chart_zero _ _,
        (real_projective_affine_chart_one _ _).mpr (sign_chamber_nonzero z.1.property)⟩,
        (real_projective_affine_chart_two _ _).mpr (sign_chamber_nonzero z.2.property)⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact real_projective_affine_point_continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prod_mk
        (continuous_subtype_val.comp continuous_snd))

/-- Each of the four sign components of the actual triple overlap is
connected: its affine coordinates range over a product of real half-lines. -/
theorem real_projective_triple_locally_constant (A : Type*)
    (f : LocallyConstant RealProjectiveTripleOverlap A)
    (p : RealProjectiveTripleOverlap) :
    f p = f (realProjectiveSignPoint
      (decide (realProjectiveCoordinate 0 1 p.val < 0))
      (decide (realProjectiveCoordinate 0 2 p.val < 0))) := by
  let a := decide (realProjectiveCoordinate 0 1 p.val < 0)
  let b := decide (realProjectiveCoordinate 0 2 p.val < 0)
  letI := Subtype.preconnectedSpace (sign_chamber_preconnected a)
  letI := Subtype.preconnectedSpace (sign_chamber_preconnected b)
  have mem (x : ℝ) (hx : x ≠ 0) : x ∈ signChamber (decide (x < 0)) := by
    by_cases h : x < 0
    · simp [signChamber, h]
    · simpa [signChamber, h] using lt_of_le_of_ne (le_of_not_gt h) hx.symm
  let z : (signChamber a) × (signChamber b) :=
    (⟨realProjectiveCoordinate 0 1 p.val,
      mem _ (real_projective_overlap_coordinate_ne_zero 0 1 (realProjectiveOverlap01 p))⟩,
     ⟨realProjectiveCoordinate 0 2 p.val,
      mem _ (real_projective_overlap_coordinate_ne_zero 0 2 (realProjectiveOverlap02 p))⟩)
  let w : (signChamber a) × (signChamber b) :=
    (⟨signValue a, sign_value_mem a⟩, ⟨signValue b, sign_value_mem b⟩)
  have he := (f.comap (chamberToTriple a b)).apply_eq_of_preconnectedSpace z w
  have hz : chamberToTriple a b z = p :=
    Subtype.ext (real_projective_affine_point_inverse p.val p.property.1.1)
  change f (chamberToTriple a b z) = f (realProjectiveSignPoint a b) at he
  rwa [hz] at he

private def signCochain (i j : Fin 3) (negative positive : ℚ) :
    LocallyConstant (RealProjectiveOverlap i j) ℚ := by
  classical
  exact ⟨fun p => if realProjectiveCoordinate i j p.val < 0 then negative else positive,
    (real_projective_overlap_negative_locally_constant i j).comp
      (fun b : Prop => if b then negative else positive)⟩

/-- Solve the four-component Čech boundary equations over ℚ. The factor 1/2
is the torsion-killing step; there is no corresponding integral surjectivity. -/
def realProjectiveRationalCechPrimitive (f : RealProjectiveCechTwo ℚ) :
    RealProjectiveCechOne ℚ :=
  let A := f (realProjectiveSignPoint false false)
  let B := f (realProjectiveSignPoint false true)
  let C := f (realProjectiveSignPoint true false)
  let D := f (realProjectiveSignPoint true true)
  let b := (A + C - B - D) / 2
  (signCochain 0 1 (C - B - b) 0,
    signCochain 0 2 b 0, signCochain 1 2 (B + b) A)

theorem real_projective_rational_cech_differential_surjective :
    Function.Surjective (realProjectiveCechDifferential ℚ) := by
  intro f
  refine ⟨realProjectiveRationalCechPrimitive f, ?_⟩
  ext p
  have hf := real_projective_triple_locally_constant ℚ f p
  have hc := real_projective_coordinate_cocycle 0 1 2 p.val
    p.property.1.1 p.property.1.2
  have h01 := real_projective_overlap_coordinate_ne_zero 0 1 (realProjectiveOverlap01 p)
  have h12 := real_projective_overlap_coordinate_ne_zero 1 2 (realProjectiveOverlap12 p)
  change realProjectiveCoordinate 0 1 p.val ≠ 0 at h01
  change realProjectiveCoordinate 1 2 p.val ≠ 0 at h12
  rw [hf]
  rcases lt_or_gt_of_ne h01 with h01 | h01 <;>
    rcases lt_or_gt_of_ne h12 with h12 | h12
  · have h02 : 0 < realProjectiveCoordinate 0 2 p.val := hc ▸ mul_pos_of_neg_of_neg h12 h01
    simp [realProjectiveCechDifferential, realProjectiveRationalCechPrimitive,
      LocallyConstant.sub_apply, LocallyConstant.coe_comap_apply, signCochain,
      realProjectiveOverlap01, realProjectiveOverlap02, realProjectiveOverlap12,
      h01, h12, h02.not_lt]
  · have h02 : realProjectiveCoordinate 0 2 p.val < 0 := hc ▸ mul_neg_of_pos_of_neg h12 h01
    simp [realProjectiveCechDifferential, realProjectiveRationalCechPrimitive,
      LocallyConstant.sub_apply, LocallyConstant.coe_comap_apply, signCochain,
      realProjectiveOverlap01, realProjectiveOverlap02, realProjectiveOverlap12,
      h01, h12.not_lt, h02]
    ring
  · have h02 : realProjectiveCoordinate 0 2 p.val < 0 := hc ▸ mul_neg_of_neg_of_pos h12 h01
    simp [realProjectiveCechDifferential, realProjectiveRationalCechPrimitive,
      LocallyConstant.sub_apply, LocallyConstant.coe_comap_apply, signCochain,
      realProjectiveOverlap01, realProjectiveOverlap02, realProjectiveOverlap12,
      h01.not_lt, h12, h02]
  · have h02 : 0 < realProjectiveCoordinate 0 2 p.val := hc ▸ mul_pos h12 h01
    simp [realProjectiveCechDifferential, realProjectiveRationalCechPrimitive,
      LocallyConstant.sub_apply, LocallyConstant.coe_comap_apply, signCochain,
      realProjectiveOverlap01, realProjectiveOverlap02, realProjectiveOverlap12,
      h01.not_lt, h12.not_lt, h02.not_lt]

/-- Every rational degree-two Čech class on the actual standard cover is
zero. The computation uses the topology of its four overlap components. -/
theorem real_projective_rational_cech_h2_zero (x : RealProjectiveCechH2 ℚ) : x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H f =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact real_projective_rational_cech_differential_surjective f

end
end Sigma
