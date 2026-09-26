import SigmaThomNativePullback
import SigmaThomNativeProjective
import SigmaThomNativeUniversalLine

namespace Sigma
noncomputable section
open PowerSeries

/-- The supplied ordinary-cohomology coordinates and natural oriented Thom
data on the actual finite universal line bundles. The stage coordinate rings
are the finite projective cohomology calculations; correction identities are
not among the hypotheses. -/
structure NativeUniversalBundleTower (T : SuppliedComplexThomTheory) where
  stage : ℕ → NativeComplexBundle
  admissible : ∀ n, T.admissible (stage n)
  tautological : ∀ n, NativeTautologicalIdentification n (stage n)
  coordinate : ∀ n, T.HBase (stage n).base ≃+* ThomStage n
  firstChern_coordinate : ∀ n, coordinate n (T.firstChern (stage n)) = thomStageMap n X
  line : ∀ n, NativeThomLine (T.context (stage n) (admissible n)) (T.firstChern (stage n))
    ((coordinate n).symm (thomStageMap n (formalExponentialOver ℚ (-1))))
  line_zeroK : ∀ n, (line n).zeroK = T.zeroK (stage n)
  line_zeroH : ∀ n, (line n).zeroH = T.zeroH (stage n)
  line_class : ∀ n, ((line n).line : T.KBase (stage n).base) = T.bundleClass (stage n)
  inclusion : ∀ n, NativeBundlePullback (stage n) (stage (n+1))
  inclusion_base : ∀ n b, (tautological (n+1)).base ((inclusion n).base b) =
    nativeProjectiveInclusion n ((tautological n).base b)
  pullback : ∀ n, SuppliedThomPullback T (admissible n) (admissible (n+1)) (inclusion n)
  coordinate_restriction : ∀ n a, coordinate n ((pullback n).hBase a) =
    thomStageRestriction n (coordinate (n+1) a)

namespace NativeUniversalBundleTower
variable {T : SuppliedComplexThomTheory} (U : NativeUniversalBundleTower T)

def completedCorrection : ThomCompletedLine :=
  ⟨fun n => U.coordinate n (T.correction (U.stage n) (U.admissible n)), by
    intro n
    rw [← U.coordinate_restriction, (U.pullback n).correction_natural]⟩

def correctionSeries : PowerSeries ℚ := thomCompletedLineEquiv.symm U.completedCorrection

theorem correctionSeries_stage (n : ℕ) :
    thomStageMap n U.correctionSeries = U.coordinate n (T.correction (U.stage n) (U.admissible n)) :=
  congrArg (fun a : ThomCompletedLine => a.val n)
    (thomCompletedLineEquiv.apply_symm_apply U.completedCorrection)

theorem correctionSeries_euler : X * U.correctionSeries = 1-formalExponentialOver ℚ (-1) := by
  apply thom_completion_map_injective
  apply Subtype.ext
  funext n
  change thomStageMap n (X * U.correctionSeries) =
    thomStageMap n (1-formalExponentialOver ℚ (-1))
  rw [map_mul, map_sub, map_one, U.correctionSeries_stage]
  have h := congrArg (U.coordinate n)
    (native_thom_line_euler (T.context (U.stage n) (U.admissible n)) (U.line n))
  simpa only [map_mul, map_sub, map_one, U.firstChern_coordinate,
    RingEquiv.apply_symm_apply] using h

theorem correctionSeries_eq_inverseTodd :
    U.correctionSeries = (↑(formalToddUnitOver ℚ)⁻¹ : PowerSeries ℚ) := by
  apply mul_left_cancel₀ (show (X : PowerSeries ℚ) ≠ 0 from PowerSeries.X_ne_zero)
  rw [U.correctionSeries_euler, mul_comm X, formal_todd_over_denominator]

/-- Exact comparison on every actual universal bundle, not merely on a
free-standing scalar truncation ring. -/
theorem stage_correction (n : ℕ) :
    T.correction (U.stage n) (U.admissible n) =
      (U.coordinate n).symm (thomStageMap n (↑(formalToddUnitOver ℚ)⁻¹ : PowerSeries ℚ)) := by
  apply (U.coordinate n).injective
  rw [RingEquiv.apply_symm_apply, ← U.correctionSeries_stage, U.correctionSeries_eq_inverseTodd]

/-- Full actual universal-line observations recover the complete Todd unit. -/
theorem universal_unit_identification (Q : (PowerSeries ℚ)ˣ)
    (hQ : ∀ n, thomStageMap n (↑Q⁻¹ : PowerSeries ℚ) =
      U.coordinate n (T.correction (U.stage n) (U.admissible n))) : Q = formalToddUnitOver ℚ := by
  have he : (↑Q⁻¹ : PowerSeries ℚ) = U.correctionSeries := by
    apply thom_completion_map_injective
    apply Subtype.ext
    funext n
    exact (hQ n).trans (U.correctionSeries_stage n).symm
  apply inv_injective
  apply Units.ext
  exact he.trans U.correctionSeries_eq_inverseTodd

end NativeUniversalBundleTower

/-- A supplied classifying map for an actual line bundle, with its fibrewise
pullback identification and natural first Chern class. -/
structure NativeClassifiedLine (T : SuppliedComplexThomTheory) (U : NativeUniversalBundleTower T)
    (L : NativeComplexBundle) (hL : T.admissible L) where
  rank : L.rank = 1
  stage : ℕ
  map : NativeBundlePullback L (U.stage stage)
  pullback : SuppliedThomPullback T hL (U.admissible stage) map
  firstChern : pullback.hBase (T.firstChern (U.stage stage)) = T.firstChern L

namespace NativeClassifiedLine
variable {T : SuppliedComplexThomTheory} {U : NativeUniversalBundleTower T}
variable {L : NativeComplexBundle} {hL : T.admissible L}

def evaluate (C : NativeClassifiedLine T U L hL) : PowerSeries ℚ →+* T.HBase L.base :=
  C.pullback.hBase.comp ((U.coordinate C.stage).symm.toRingHom.comp (thomStageMap C.stage))

theorem evaluate_X (C : NativeClassifiedLine T U L hL) :
    C.evaluate X = T.firstChern L := by
  change C.pullback.hBase ((U.coordinate C.stage).symm (thomStageMap C.stage X)) = _
  rw [← U.firstChern_coordinate, RingEquiv.symm_apply_apply, C.firstChern]

theorem correction_eq_evaluate_inverseTodd (C : NativeClassifiedLine T U L hL) :
    T.correction L hL = C.evaluate (↑(formalToddUnitOver ℚ)⁻¹ : PowerSeries ℚ) := by
  rw [← C.pullback.correction_natural, U.stage_correction]
  rfl

end NativeClassifiedLine
end
end Sigma
