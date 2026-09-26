import SigmaThomNativeCompletion

namespace Sigma
noncomputable section
open PowerSeries

/-- Supplied finite-stage Thom groups after the ordinary-cohomology coordinate
identifications for the universal line. Naturality is imposed on primitive
Thom classes; compatibility of their correction classes will be derived. -/
structure NativeUniversalLine where
  K : ℕ → Type
  KR : ℕ → Type
  HR : ℕ → Type
  [kRing : ∀ n, CommRing (K n)]
  [krGroup : ∀ n, AddCommGroup (KR n)]
  [hrGroup : ∀ n, AddCommGroup (HR n)]
  [krModule : ∀ n, Module (K n) (KR n)]
  [hrModule : ∀ n, Module (ThomStage n) (HR n)]
  thom : ∀ n, NativeThomContext (K n) (ThomStage n) (KR n) (HR n)
  line : ∀ n, NativeThomLine (thom n) (thomStageMap n X)
    (thomStageMap n (formalExponentialOver ℚ (-1)))
  restriction : ∀ n, NativeThomPullback (thom (n+1)) (thom n)
  restriction_base : ∀ n, (restriction n).hBase = thomStageRestriction n

attribute [instance] NativeUniversalLine.kRing NativeUniversalLine.krGroup
  NativeUniversalLine.hrGroup NativeUniversalLine.krModule NativeUniversalLine.hrModule

namespace NativeUniversalLine
variable (L : NativeUniversalLine)

def completedCorrection : ThomCompletedLine := ⟨fun n => (L.thom n).correction, by
  intro n
  rw [← L.restriction_base n]
  exact (L.restriction n).correction_natural⟩

def correctionSeries : PowerSeries ℚ := thomCompletedLineEquiv.symm L.completedCorrection

theorem correctionSeries_stage (n : ℕ) :
    thomStageMap n L.correctionSeries = (L.thom n).correction := by
  exact congrArg (fun a : ThomCompletedLine => a.val n)
    (thomCompletedLineEquiv.apply_symm_apply L.completedCorrection)

/-- Finite-stage zero-section identities produce the complete equation only
after passing to the proved inverse limit. No finite-base cancellation occurs. -/
theorem correctionSeries_euler :
    X * L.correctionSeries = 1-formalExponentialOver ℚ (-1) := by
  apply thom_completion_map_injective
  apply Subtype.ext
  funext n
  change thomStageMap n (X * L.correctionSeries) =
    thomStageMap n (1-formalExponentialOver ℚ (-1))
  rw [map_mul, map_sub, map_one, L.correctionSeries_stage]
  exact native_thom_line_euler (L.thom n) (L.line n)

/-- The entire universal correction is the inverse Todd unit, derived from
primitive supplied topology data and the actual universal inverse limit. -/
theorem correctionSeries_eq_inverseTodd :
    L.correctionSeries = (↑(formalToddUnitOver ℚ)⁻¹ : PowerSeries ℚ) := by
  apply mul_left_cancel₀ (show (X : PowerSeries ℚ) ≠ 0 from PowerSeries.X_ne_zero)
  rw [L.correctionSeries_euler, mul_comm X, formal_todd_over_denominator]

theorem finite_correction_eq_inverseTodd (n : ℕ) :
    (L.thom n).correction = thomStageMap n (↑(formalToddUnitOver ℚ)⁻¹ : PowerSeries ℚ) := by
  rw [← L.correctionSeries_stage n, L.correctionSeries_eq_inverseTodd]

theorem correctionSeries_isUnit : IsUnit L.correctionSeries := by
  rw [L.correctionSeries_eq_inverseTodd]
  exact Units.isUnit _

/-- Full universal-line correction data, unlike a single finite stage, recover
any competing normalized unit and hence recover the Todd unit exactly. -/
theorem todd_reconstruction (T : (PowerSeries ℚ)ˣ)
    (hT : (↑T⁻¹ : PowerSeries ℚ) = L.correctionSeries) : T = formalToddUnitOver ℚ := by
  apply inv_injective
  apply Units.ext
  exact hT.trans L.correctionSeries_eq_inverseTodd

end NativeUniversalLine
end
end Sigma
