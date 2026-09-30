import SigmaRealProjectiveComplexification
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.LinearAlgebra.Quotient.Basic

namespace Sigma
noncomputable section
open Set Filter Topology
attribute [local instance] Classical.propDecidable

/-- The pairwise overlaps of the actual three standard open RP² charts. -/
abbrev RealProjectiveOverlap (i j : Fin 3) :=
  {p : RealProjectivePlane // p ∈ realProjectiveChart i ∩ realProjectiveChart j}

abbrev RealProjectiveTripleOverlap :=
  {p : RealProjectivePlane // p ∈ realProjectiveChart 0 ∩
    realProjectiveChart 1 ∩ realProjectiveChart 2}

def realProjectiveOverlap01 : C(RealProjectiveTripleOverlap, RealProjectiveOverlap 0 1) :=
  ⟨fun p => ⟨p.val, p.property.1⟩, continuous_subtype_val.subtype_mk _⟩

def realProjectiveOverlap02 : C(RealProjectiveTripleOverlap, RealProjectiveOverlap 0 2) :=
  ⟨fun p => ⟨p.val, p.property.1.1, p.property.2⟩, continuous_subtype_val.subtype_mk _⟩

def realProjectiveOverlap12 : C(RealProjectiveTripleOverlap, RealProjectiveOverlap 1 2) :=
  ⟨fun p => ⟨p.val, p.property.1.2, p.property.2⟩, continuous_subtype_val.subtype_mk _⟩

theorem real_projective_overlap_coordinate_ne_zero (i j : Fin 3)
    (p : RealProjectiveOverlap i j) : realProjectiveCoordinate i j p.val ≠ 0 := by
  have hc := real_projective_coordinate_cocycle i j i p.val p.property.1 p.property.2
  rw [real_projective_coordinate_self i p.val p.property.1] at hc
  exact right_ne_zero_of_mul_eq_one hc

/-- The real transition has a locally constant sign on every chart overlap. -/
theorem real_projective_overlap_negative_locally_constant (i j : Fin 3) :
    IsLocallyConstant (fun p : RealProjectiveOverlap i j =>
      realProjectiveCoordinate i j p.val < 0) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro p
  have hc : Continuous (fun q : RealProjectiveOverlap i j =>
      realProjectiveCoordinate i j q.val) :=
    (real_projective_coordinate_continuousOn i j).comp_continuous
      continuous_subtype_val (fun q => q.property.1)
  by_cases hn : realProjectiveCoordinate i j p.val < 0
  · filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hn)] with q hq
    exact propext ⟨fun _ => hn, fun _ => hq⟩
  · have hp : 0 < realProjectiveCoordinate i j p.val :=
      lt_of_le_of_ne (le_of_not_gt hn) (real_projective_overlap_coordinate_ne_zero i j p).symm
    filter_upwards [hc.continuousAt.eventually (lt_mem_nhds hp)] with q hq
    exact propext ⟨fun h => False.elim ((not_lt_of_gt hq) h),
      fun h => False.elim (hn h)⟩

/-- A logarithm of the normalized sign transition, in turns: 0 or 1/2. -/
def realProjectiveTransitionLog (i j : Fin 3) :
    LocallyConstant (RealProjectiveOverlap i j) ℚ :=
  ⟨fun p => if realProjectiveCoordinate i j p.val < 0 then 1 / 2 else 0,
    (real_projective_overlap_negative_locally_constant i j).comp
      (fun b : Prop => if b then (1 / 2 : ℚ) else 0)⟩

section Cech
variable (R : Type*) [CommRing R]

/-- Degree-one Čech cochains of the ordered three-chart cover, with constant
coefficients: locally constant functions on each of the three overlaps. -/
abbrev RealProjectiveCechOne :=
  LocallyConstant (RealProjectiveOverlap 0 1) R ×
    LocallyConstant (RealProjectiveOverlap 0 2) R ×
      LocallyConstant (RealProjectiveOverlap 1 2) R

abbrev RealProjectiveCechTwo := LocallyConstant RealProjectiveTripleOverlap R

/-- The actual alternating Čech differential, c12 - c02 + c01. -/
def realProjectiveCechDifferential :
    RealProjectiveCechOne R →ₗ[R] RealProjectiveCechTwo R where
  toFun c := c.2.2.comap realProjectiveOverlap12 -
    c.2.1.comap realProjectiveOverlap02 + c.1.comap realProjectiveOverlap01
  map_add' c d := by ext p; simp only [LocallyConstant.add_apply,
      LocallyConstant.sub_apply, LocallyConstant.coe_comap_apply, Prod.fst_add,
      Prod.snd_add]; abel
  map_smul' r c := by ext p; simp only [LocallyConstant.add_apply,
      LocallyConstant.sub_apply, LocallyConstant.coe_comap_apply,
      LocallyConstant.smul_apply, Prod.smul_fst, Prod.smul_snd,
      RingHom.id_apply, smul_sub, smul_add]

/-- Degree-two cohomology of this actual cover. There are no ordered
fourfold intersections in a cover indexed by three elements. -/
abbrev RealProjectiveCechH2 :=
  RealProjectiveCechTwo R ⧸ LinearMap.range (realProjectiveCechDifferential R)

end Cech

/-- The integer Bockstein cocycle of the actual sign transitions. -/
def realProjectiveIntegralChernCocycle : RealProjectiveCechTwo ℤ :=
  ⟨fun p => if realProjectiveCoordinate 0 1 p.val < 0 ∧
      realProjectiveCoordinate 1 2 p.val < 0 then 1 else 0,
    (((real_projective_overlap_negative_locally_constant 0 1).comp_continuous
      realProjectiveOverlap01.continuous).prod_mk
      ((real_projective_overlap_negative_locally_constant 1 2).comp_continuous
        realProjectiveOverlap12.continuous)).comp
      (fun b : Prop × Prop => if b.1 ∧ b.2 then (1 : ℤ) else 0)⟩

def realProjectiveRationalChernCocycle : RealProjectiveCechTwo ℚ :=
  realProjectiveIntegralChernCocycle.map (fun z : ℤ => (z : ℚ))

def realProjectiveChernPrimitive : RealProjectiveCechOne ℚ :=
  ⟨realProjectiveTransitionLog 0 1,
    realProjectiveTransitionLog 0 2, realProjectiveTransitionLog 1 2⟩

/-- Continuous complex logarithms of the genuine (not just normalized)
bundle transitions. The real part retains their absolute values. -/
def realProjectiveTransitionComplexLog (i j : Fin 3)
    (p : RealProjectiveOverlap i j) : ℂ :=
  (Real.log |realProjectiveCoordinate i j p.val| : ℂ) +
    if realProjectiveCoordinate i j p.val < 0 then (Real.pi : ℂ) * Complex.I else 0

theorem real_projective_transition_complex_log_continuous (i j : Fin 3) :
    Continuous (realProjectiveTransitionComplexLog i j) := by
  have hc : Continuous (fun p : RealProjectiveOverlap i j =>
      realProjectiveCoordinate i j p.val) :=
    (real_projective_coordinate_continuousOn i j).comp_continuous
      continuous_subtype_val (fun p => p.property.1)
  exact (Complex.continuous_ofReal.comp (hc.abs.log
    (fun p => abs_ne_zero.mpr (real_projective_overlap_coordinate_ne_zero i j p)))).add
    (((real_projective_overlap_negative_locally_constant i j).comp
      (fun b : Prop => if b then (Real.pi : ℂ) * Complex.I else 0)).continuous)

theorem real_projective_transition_complex_log_exp (i j : Fin 3)
    (p : RealProjectiveOverlap i j) :
    Complex.exp (realProjectiveTransitionComplexLog i j p) =
      (realProjectiveCoordinate i j p.val : ℂ) := by
  have hn := real_projective_overlap_coordinate_ne_zero i j p
  unfold realProjectiveTransitionComplexLog
  rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (abs_pos.mpr hn)]
  by_cases h : realProjectiveCoordinate i j p.val < 0
  · simp [h, Complex.exp_pi_mul_I, abs_of_neg h]
  · simp [h, abs_of_nonneg (le_of_not_gt h)]

/-- The integral Chern cocycle becomes an explicit coboundary over ℚ. Its
primitive is the half-integral logarithm of the genuine chart transitions. -/
theorem real_projective_rational_chern_cocycle_exact :
    realProjectiveCechDifferential ℚ realProjectiveChernPrimitive =
      realProjectiveRationalChernCocycle := by
  ext p
  have hc := real_projective_coordinate_cocycle 0 1 2 p.val
    p.property.1.1 p.property.1.2
  have h01 := real_projective_overlap_coordinate_ne_zero 0 1 (realProjectiveOverlap01 p)
  have h12 := real_projective_overlap_coordinate_ne_zero 1 2 (realProjectiveOverlap12 p)
  change realProjectiveCoordinate 0 1 p.val ≠ 0 at h01
  change realProjectiveCoordinate 1 2 p.val ≠ 0 at h12
  dsimp [realProjectiveCechDifferential, realProjectiveChernPrimitive,
    realProjectiveTransitionLog, realProjectiveRationalChernCocycle,
    realProjectiveIntegralChernCocycle, LocallyConstant.map, LocallyConstant.comap,
    realProjectiveOverlap01, realProjectiveOverlap02, realProjectiveOverlap12]
  simp only [LocallyConstant.sub_apply]
  change (if realProjectiveCoordinate 1 2 p.val < 0 then (1 / 2 : ℚ) else 0) -
    (if realProjectiveCoordinate 0 2 p.val < 0 then 1 / 2 else 0) +
    (if realProjectiveCoordinate 0 1 p.val < 0 then 1 / 2 else 0) =
    Int.cast (if realProjectiveCoordinate 0 1 p.val < 0 ∧
      realProjectiveCoordinate 1 2 p.val < 0 then 1 else 0)
  rw [← hc]
  rcases lt_or_gt_of_ne h01 with h01 | h01 <;>
    rcases lt_or_gt_of_ne h12 with h12 | h12
  · norm_num [h01, h12, not_lt_of_gt (mul_pos_of_neg_of_neg h12 h01)]
  · simp [h01, h12.not_lt, mul_neg_of_pos_of_neg h12 h01]
  · simp [h01.not_lt, h12, mul_neg_of_neg_of_pos h12 h01]
  · simp [h01.not_lt, h12.not_lt, not_lt_of_gt (mul_pos h12 h01)]

def realProjectiveRationalFirstChern : RealProjectiveCechH2 ℚ :=
  (realProjectiveCechDifferential ℚ).range.mkQ realProjectiveRationalChernCocycle

theorem real_projective_rational_first_chern_zero :
    realProjectiveRationalFirstChern = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨realProjectiveChernPrimitive, real_projective_rational_chern_cocycle_exact⟩

private theorem transition_complex_log_decomposition (i j : Fin 3)
    (p : RealProjectiveOverlap i j) :
    realProjectiveTransitionComplexLog i j p =
      (Real.log |realProjectiveCoordinate i j p.val| : ℂ) +
        (2 * (Real.pi : ℂ) * Complex.I) * (realProjectiveTransitionLog i j p : ℂ) := by
  by_cases h : realProjectiveCoordinate i j p.val < 0
  · simp [realProjectiveTransitionComplexLog, realProjectiveTransitionLog, h]
    ring
  · simp [realProjectiveTransitionComplexLog, realProjectiveTransitionLog, h]

/-- The cocycle is literally the exponential-sequence connecting cocycle:
the coboundary of continuous transition logarithms, divided by 2πi. -/
theorem real_projective_complex_log_chern_coboundary (p : RealProjectiveTripleOverlap) :
    realProjectiveTransitionComplexLog 1 2 (realProjectiveOverlap12 p) -
      realProjectiveTransitionComplexLog 0 2 (realProjectiveOverlap02 p) +
      realProjectiveTransitionComplexLog 0 1 (realProjectiveOverlap01 p) =
    (2 * (Real.pi : ℂ) * Complex.I) * (realProjectiveIntegralChernCocycle p : ℂ) := by
  have hc := real_projective_coordinate_cocycle 0 1 2 p.val
    p.property.1.1 p.property.1.2
  have h01 := real_projective_overlap_coordinate_ne_zero 0 1 (realProjectiveOverlap01 p)
  have h12 := real_projective_overlap_coordinate_ne_zero 1 2 (realProjectiveOverlap12 p)
  change realProjectiveCoordinate 0 1 p.val ≠ 0 at h01
  change realProjectiveCoordinate 1 2 p.val ≠ 0 at h12
  have hr : Real.log |realProjectiveCoordinate 1 2 p.val| -
      Real.log |realProjectiveCoordinate 0 2 p.val| +
      Real.log |realProjectiveCoordinate 0 1 p.val| = 0 := by
    rw [← hc, abs_mul, Real.log_mul (abs_ne_zero.mpr h12) (abs_ne_zero.mpr h01)]
    ring
  have hq : realProjectiveTransitionLog 1 2 (realProjectiveOverlap12 p) -
      realProjectiveTransitionLog 0 2 (realProjectiveOverlap02 p) +
      realProjectiveTransitionLog 0 1 (realProjectiveOverlap01 p) =
        (realProjectiveIntegralChernCocycle p : ℚ) := by
    have he := congrArg (fun c : RealProjectiveCechTwo ℚ => c p)
      real_projective_rational_chern_cocycle_exact
    simpa only [realProjectiveCechDifferential, realProjectiveChernPrimitive,
      LinearMap.coe_mk, AddHom.coe_mk, LocallyConstant.add_apply,
      LocallyConstant.sub_apply, LocallyConstant.coe_comap_apply,
      realProjectiveRationalChernCocycle, LocallyConstant.map_apply,
      Function.comp_apply] using he
  have hrC : (Real.log |realProjectiveCoordinate 1 2 p.val| : ℂ) -
      (Real.log |realProjectiveCoordinate 0 2 p.val| : ℂ) +
      (Real.log |realProjectiveCoordinate 0 1 p.val| : ℂ) = 0 := by exact_mod_cast hr
  have hqC : (realProjectiveTransitionLog 1 2 (realProjectiveOverlap12 p) : ℂ) -
      (realProjectiveTransitionLog 0 2 (realProjectiveOverlap02 p) : ℂ) +
      (realProjectiveTransitionLog 0 1 (realProjectiveOverlap01 p) : ℂ) =
        (realProjectiveIntegralChernCocycle p : ℂ) := by exact_mod_cast hq
  rw [transition_complex_log_decomposition, transition_complex_log_decomposition,
    transition_complex_log_decomposition]
  change (Real.log |realProjectiveCoordinate 1 2 p.val| : ℂ) + _ -
    ((Real.log |realProjectiveCoordinate 0 2 p.val| : ℂ) + _) +
    ((Real.log |realProjectiveCoordinate 0 1 p.val| : ℂ) + _) = _
  linear_combination hrC + (2 * (Real.pi : ℂ) * Complex.I) * hqC

/-- The degree-zero and degree-two components of the line Chern character
on the three-chart Čech complex. Higher ordered cochain degrees vanish. -/
def realProjectiveCechChernCharacter : ℚ × RealProjectiveCechH2 ℚ :=
  (1, realProjectiveRationalFirstChern)

theorem real_projective_cech_chern_character_one :
    realProjectiveCechChernCharacter = (1, 0) := by
  simp [realProjectiveCechChernCharacter, real_projective_rational_first_chern_zero]

end
end Sigma
