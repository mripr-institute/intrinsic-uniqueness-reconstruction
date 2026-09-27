import SigmaOpResolvent
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.NormedSpace.OperatorNorm.Completeness

/-! The native shift inverse of an arbitrary nonnegative self-adjoint operator.
No eigenbasis or spectral representation is assumed. -/

namespace Sigma
noncomputable section
open scoped ComplexConjugate
open LinearPMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local notation "⟪" x ", " y "⟫" => @inner ℂ H _ x y

/-- The quadratic-form definition of nonnegativity on the full native domain. -/
def OpNonnegative (B : H →ₗ.[ℂ] H) : Prop :=
  ∀ x : B.domain, 0 ≤ (⟪x.val, B x⟫).re

def opShift (B : H →ₗ.[ℂ] H) : B.domain →ₗ[ℂ] H :=
  B.toFun + B.domain.subtype

omit [CompleteSpace H] in
theorem op_shift_norm_lower (B : H →ₗ.[ℂ] H) (hB : OpNonnegative B)
    (x : B.domain) : ‖x.val‖ ≤ ‖opShift B x‖ := by
  have hp := hB x
  have hi := re_inner_le_norm (𝕜 := ℂ) x.val (opShift B x)
  change (⟪x.val, B x + x.val⟫).re ≤ ‖x.val‖ * ‖opShift B x‖ at hi
  rw [inner_add_right, Complex.add_re] at hi
  have hn : (⟪x.val,x.val⟫).re = ‖x.val‖ ^ 2 := by
    exact (norm_sq_eq_inner (𝕜 := ℂ) x.val).symm
  rw [hn] at hi
  nlinarith [norm_nonneg x.val, norm_nonneg (opShift B x)]

omit [CompleteSpace H] in
theorem op_shift_injective (B : H →ₗ.[ℂ] H) (hB : OpNonnegative B) :
    Function.Injective (opShift B) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  apply Subtype.ext
  apply norm_eq_zero.mp
  have hn := op_shift_norm_lower B hB x
  exact le_antisymm (by simpa only [LinearMap.mem_ker.mp hx, norm_zero] using hn)
    (norm_nonneg _)

theorem op_shift_dense_range (B : H →ₗ.[ℂ] H) (hsa : IsSelfAdjoint B)
    (hB : OpNonnegative B) : DenseRange (opShift B) := by
  change Dense (LinearMap.range (opShift B) : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro y hy
  have hh (x : B.domain) : ⟪-y, x.val⟫ = ⟪y, B x⟫ := by
    have he := (Submodule.mem_orthogonal' _ _).mp hy (opShift B x)
      (LinearMap.mem_range_self _ x)
    change ⟪y, B x + x.val⟫ = 0 at he
    rw [inner_add_right] at he
    rw [inner_neg_left]
    exact (eq_neg_of_add_eq_zero_left he).symm
  have hyadj := B.mem_adjoint_domain_of_exists y ⟨-y, hh⟩
  have hydom : y ∈ B.domain := by
    rw [← LinearPMap.isSelfAdjoint_def.mp hsa]
    exact hyadj
  have hact : B ⟨y, hydom⟩ = -y := by
    have hsymm : B.IsFormalAdjoint B := by
      have h := B.adjoint_isFormalAdjoint hsa.dense_domain
      rwa [LinearPMap.isSelfAdjoint_def.mp hsa] at h
    exact hsa.dense_domain.eq_of_inner_left fun x =>
      (hsymm ⟨y,hydom⟩ x).trans (hh x).symm
  have hn := hB ⟨y,hydom⟩
  rw [hact, inner_neg_right, Complex.neg_re] at hn
  have hnself : (⟪y,y⟫).re = ‖y‖ ^ 2 := by
    exact (norm_sq_eq_inner (𝕜 := ℂ) y).symm
  rw [hnself] at hn
  simpa using (norm_eq_zero.mp (by nlinarith [norm_nonneg y]) : y = 0)

def opShiftInverseOnRange (B : H →ₗ.[ℂ] H) (hB : OpNonnegative B) :
    LinearMap.range (opShift B) →L[ℂ] H :=
  (B.domain.subtype.comp
    (LinearEquiv.ofInjective (opShift B) (op_shift_injective B hB)).symm.toLinearMap).mkContinuous 1 (by
      intro y
      have h := op_shift_norm_lower B hB
        ((LinearEquiv.ofInjective (opShift B) (op_shift_injective B hB)).symm y)
      simpa only [LinearMap.comp_apply, Submodule.subtype_apply, one_mul,
        LinearEquiv.coe_coe, LinearEquiv.ofInjective_symm_apply, Submodule.norm_coe] using h)

omit [CompleteSpace H] in
theorem op_shift_inverse_on_range (B : H →ₗ.[ℂ] H) (hB : OpNonnegative B)
    (x : B.domain) :
    opShiftInverseOnRange B hB ⟨opShift B x, LinearMap.mem_range_self _ x⟩ = x.val := by
  change ((LinearEquiv.ofInjective (opShift B) (op_shift_injective B hB)).symm
    ((LinearEquiv.ofInjective (opShift B) (op_shift_injective B hB)) x)).val = x.val
  rw [LinearEquiv.symm_apply_apply]

/-- Extend the contractive inverse along its proved dense range. -/
def opNonnegativeResolvent (B : H →ₗ.[ℂ] H) (hsa : IsSelfAdjoint B)
    (hB : OpNonnegative B) : H →L[ℂ] H :=
  (opShiftInverseOnRange B hB).extend
    (Submodule.subtypeL (LinearMap.range (opShift B)))
    ((op_shift_dense_range B hsa hB).denseRange_val)
    isometry_subtype_coe.isUniformInducing

theorem op_nonnegative_resolvent_left_inverse (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) (x : B.domain) :
    opNonnegativeResolvent B hsa hB (B x + x.val) = x.val := by
  change opNonnegativeResolvent B hsa hB
    (Submodule.subtypeL (LinearMap.range (opShift B))
      ⟨opShift B x, LinearMap.mem_range_self _ x⟩) = x.val
  rw [opNonnegativeResolvent, ContinuousLinearMap.extend_eq,
    op_shift_inverse_on_range]

theorem op_nonnegative_resolvent_inner (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) (z : H) (u : B.domain) :
    ⟪opNonnegativeResolvent B hsa hB z, B u + u.val⟫ = ⟪z,u.val⟫ := by
  have hsymm : B.IsFormalAdjoint B := by
    have h := B.adjoint_isFormalAdjoint hsa.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hsa] at h
  apply isClosed_property (op_shift_dense_range B hsa hB)
    (isClosed_eq ((opNonnegativeResolvent B hsa hB).continuous.inner continuous_const)
      (continuous_id.inner continuous_const)) (fun x => ?_) z
  change ⟪opNonnegativeResolvent B hsa hB (B x + x.val), B u + u.val⟫ =
    ⟪B x + x.val,u.val⟫
  rw [op_nonnegative_resolvent_left_inverse, inner_add_left, inner_add_right, hsymm x u]

theorem op_nonnegative_resolvent_mem (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) (z : H) :
    opNonnegativeResolvent B hsa hB z ∈ B.domain := by
  have hm : opNonnegativeResolvent B hsa hB z ∈ B.adjoint.domain := by
    apply B.mem_adjoint_domain_of_exists
    refine ⟨z - opNonnegativeResolvent B hsa hB z, fun u => ?_⟩
    have hi := op_nonnegative_resolvent_inner B hsa hB z u
    rw [inner_add_right] at hi
    rw [inner_sub_left]
    exact (eq_sub_of_add_eq hi).symm
  exact (congrArg LinearPMap.domain (LinearPMap.isSelfAdjoint_def.mp hsa)) ▸ hm

theorem op_nonnegative_resolvent_action (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) (z : H) :
    B ⟨opNonnegativeResolvent B hsa hB z, op_nonnegative_resolvent_mem B hsa hB z⟩ =
      z - opNonnegativeResolvent B hsa hB z := by
  have hsymm : B.IsFormalAdjoint B := by
    have h := B.adjoint_isFormalAdjoint hsa.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hsa] at h
  apply hsa.dense_domain.eq_of_inner_left
  intro u
  rw [hsymm, inner_sub_left]
  have hi := op_nonnegative_resolvent_inner B hsa hB z u
  rw [inner_add_right] at hi
  exact eq_sub_of_add_eq hi

/-- Actual two-sided bounded inverse on the full domain, for every native
nonnegative self-adjoint operator. -/
theorem op_nonnegative_shift_resolvent (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) :
    OpIsResolvent B 1 (opNonnegativeResolvent B hsa hB) := by
  refine ⟨op_nonnegative_resolvent_mem B hsa hB, ?_, ?_⟩
  · intro z
    rw [op_nonnegative_resolvent_action, one_smul, sub_add_cancel]
  · intro x
    simpa only [one_smul] using op_nonnegative_resolvent_left_inverse B hsa hB x

theorem op_nonnegative_resolvent_contraction (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) (z : H) :
    ‖opNonnegativeResolvent B hsa hB z‖ ≤ ‖z‖ := by
  apply isClosed_property (op_shift_dense_range B hsa hB)
    (isClosed_le (opNonnegativeResolvent B hsa hB).continuous.norm continuous_norm)
    (fun x => ?_) z
  change ‖opNonnegativeResolvent B hsa hB (B x + x.val)‖ ≤ ‖opShift B x‖
  rw [op_nonnegative_resolvent_left_inverse]
  exact op_shift_norm_lower B hB x

theorem op_nonnegative_resolvent_norm (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) :
    ‖opNonnegativeResolvent B hsa hB‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [one_mul] using op_nonnegative_resolvent_contraction B hsa hB z

theorem op_nonnegative_resolvent_selfAdjoint (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) :
    IsSelfAdjoint (opNonnegativeResolvent B hsa hB) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  have hi := op_nonnegative_resolvent_inner B hsa hB x
    ⟨opNonnegativeResolvent B hsa hB y, op_nonnegative_resolvent_mem B hsa hB y⟩
  rw [op_nonnegative_resolvent_action, sub_add_cancel] at hi
  exact hi

theorem op_nonnegative_resolvent_positive (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) (z : H) :
    0 ≤ (⟪z,opNonnegativeResolvent B hsa hB z⟫).re := by
  have hi := op_nonnegative_resolvent_inner B hsa hB z
    ⟨opNonnegativeResolvent B hsa hB z, op_nonnegative_resolvent_mem B hsa hB z⟩
  have hire := congrArg Complex.re hi
  rw [inner_add_right, Complex.add_re] at hire
  have hp := hB
    ⟨opNonnegativeResolvent B hsa hB z, op_nonnegative_resolvent_mem B hsa hB z⟩
  rw [← hire]
  exact add_nonneg hp (inner_self_nonneg (𝕜 := ℂ))

theorem op_nonnegative_resolvent_injective (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) :
    Function.Injective (opNonnegativeResolvent B hsa hB) :=
  operator_resolvent_injective B 1 _ (op_nonnegative_shift_resolvent B hsa hB)

theorem op_nonnegative_resolvent_nonneg (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) :
    0 ≤ opNonnegativeResolvent B hsa hB := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  refine ⟨op_nonnegative_resolvent_selfAdjoint B hsa hB, fun z => ?_⟩
  change 0 ≤ RCLike.re (⟪opNonnegativeResolvent B hsa hB z,z⟫)
  rw [inner_re_symm]
  exact op_nonnegative_resolvent_positive B hsa hB z

theorem op_nonnegative_resolvent_dense_range (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) :
    DenseRange (opNonnegativeResolvent B hsa hB) := by
  change Dense (Set.range (opNonnegativeResolvent B hsa hB))
  rw [← operator_resolvent_domain B 1 _ (op_nonnegative_shift_resolvent B hsa hB)]
  exact hsa.dense_domain

end
end Sigma
