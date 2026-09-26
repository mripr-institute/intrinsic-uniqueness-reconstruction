import SigmaThomNativeNaturality
import SigmaRealToddAlgebra
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace Sigma
noncomputable section
open PowerSeries

/-- The actual finite universal-line coefficient ring, with its nilpotent
positive-degree generator. -/
def thomStageIdeal (n : ℕ) : Ideal (PowerSeries ℚ) := Ideal.span {X^(n+1)}
abbrev ThomStage (n : ℕ) := PowerSeries ℚ ⧸ thomStageIdeal n

def thomStageMap (n : ℕ) : PowerSeries ℚ →+* ThomStage n := Ideal.Quotient.mk _

theorem thom_stage_eq_iff (n : ℕ) (F G : PowerSeries ℚ) :
    thomStageMap n F = thomStageMap n G ↔ ∀ k ≤ n, coeff ℚ k F = coeff ℚ k G := by
  rw [thomStageMap, Ideal.Quotient.eq, thomStageIdeal, Ideal.mem_span_singleton,
    PowerSeries.X_pow_dvd_iff]
  simp only [map_sub, sub_eq_zero, Nat.lt_succ_iff]

theorem thom_stage_ideal_decreasing (n : ℕ) : thomStageIdeal (n+1) ≤ thomStageIdeal n := by
  apply Ideal.span_le.mpr
  intro x hx
  have hx' : x = (X : PowerSeries ℚ)^(n+1+1) := Set.mem_singleton_iff.mp hx
  rw [hx']
  exact Ideal.mem_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ _))

def thomStageRestriction (n : ℕ) : ThomStage (n+1) →+* ThomStage n :=
  Ideal.Quotient.factor _ _ (thom_stage_ideal_decreasing n)

@[simp] theorem thom_stage_restrict_map (n : ℕ) (F : PowerSeries ℚ) :
    thomStageRestriction n (thomStageMap (n+1) F) = thomStageMap n F := rfl

/-- Compatible finite-stage classes, with their native inverse-limit ring. -/
def thomCompatibleSubring : Subring (∀ n, ThomStage n) where
  carrier := {a | ∀ n, thomStageRestriction n (a (n+1)) = a n}
  zero_mem' := by intro n; simp
  one_mem' := by intro n; simp
  add_mem' := by intro a b ha hb n; simp only [Pi.add_apply, map_add, ha n, hb n]
  neg_mem' := by intro a ha n; simp only [Pi.neg_apply, map_neg, ha n]
  mul_mem' := by intro a b ha hb n; simp only [Pi.mul_apply, map_mul, ha n, hb n]

abbrev ThomCompletedLine := thomCompatibleSubring

def thomCompletionMap : PowerSeries ℚ →+* ThomCompletedLine where
  toFun F := ⟨fun n => thomStageMap n F, fun _ => rfl⟩
  map_zero' := by ext n; exact map_zero _
  map_one' := by ext n; exact map_one _
  map_add' F G := by ext n; exact map_add _ _ _
  map_mul' F G := by ext n; exact map_mul _ _ _

theorem thom_completion_map_injective : Function.Injective thomCompletionMap := by
  intro F G h
  apply PowerSeries.ext
  intro k
  exact (thom_stage_eq_iff k F G).mp (congrArg (fun a : ThomCompletedLine => a.val k) h) k le_rfl

/-- A stage coefficient is independent of the chosen quotient representative
in every degree visible at that stage. -/
def thomStageCoeff (n k : ℕ) (a : ThomStage n) : ℚ :=
  coeff ℚ k (Classical.choose (Ideal.Quotient.mk_surjective a))

theorem thom_stage_coeff_map (n k : ℕ) (hk : k ≤ n) (F : PowerSeries ℚ) :
    thomStageCoeff n k (thomStageMap n F) = coeff ℚ k F := by
  apply (thom_stage_eq_iff n _ F).mp
    (Classical.choose_spec (Ideal.Quotient.mk_surjective (thomStageMap n F))) k hk

theorem thom_stage_coeff_restriction (n k : ℕ) (hk : k ≤ n) (a : ThomStage (n+1)) :
    thomStageCoeff n k (thomStageRestriction n a) = thomStageCoeff (n+1) k a := by
  obtain ⟨F,rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [show Ideal.Quotient.mk (thomStageIdeal (n+1)) F = thomStageMap (n+1) F from rfl,
    thom_stage_restrict_map, thom_stage_coeff_map n k hk,
    thom_stage_coeff_map (n+1) k (hk.trans (Nat.le_succ n))]

theorem thom_compatible_coeff (a : ThomCompletedLine) {n m k : ℕ} (hnm : n ≤ m) (hk : k ≤ n) :
    thomStageCoeff n k (a.val n) = thomStageCoeff m k (a.val m) := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [ih, ← a.property m, thom_stage_coeff_restriction m k (hk.trans hnm)]

def thomCompletionInverse (a : ThomCompletedLine) : PowerSeries ℚ :=
  PowerSeries.mk (fun k => thomStageCoeff k k (a.val k))

theorem thom_completion_inverse_left (F : PowerSeries ℚ) :
    thomCompletionInverse (thomCompletionMap F) = F := by
  apply PowerSeries.ext
  intro k
  simpa only [thomCompletionInverse, coeff_mk] using thom_stage_coeff_map k k le_rfl F

theorem thom_completion_inverse_right (a : ThomCompletedLine) :
    thomCompletionMap (thomCompletionInverse a) = a := by
  apply Subtype.ext
  funext n
  obtain ⟨F,hF⟩ := Ideal.Quotient.mk_surjective (a.val n)
  change thomStageMap n (thomCompletionInverse a) = a.val n
  rw [← hF]
  apply (thom_stage_eq_iff n _ F).mpr
  intro k hk
  simp only [thomCompletionInverse, coeff_mk]
  change thomStageCoeff k k (a.val k) = coeff ℚ k F
  rw [thom_compatible_coeff a hk le_rfl, ← hF]
  exact thom_stage_coeff_map n k hk F

/-- The universal inverse limit is proved to be the full rational power-series
ring, including surjectivity, rather than merely an injective coefficient map. -/
def thomCompletedLineEquiv : PowerSeries ℚ ≃+* ThomCompletedLine :=
  RingEquiv.ofBijective thomCompletionMap
    ⟨thom_completion_map_injective, fun a => ⟨thomCompletionInverse a, thom_completion_inverse_right a⟩⟩

end
end Sigma
