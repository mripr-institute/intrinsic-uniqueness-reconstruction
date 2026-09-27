import SigmaMatrixGeodesic
import Mathlib.MeasureTheory.Integral.FundThmCalculus

/-!
The noncommutative Duhamel identity for the matrix exponential.  This gives
the exact first-order difference as a Bochner integral, using only the
one-parameter derivative of `exp (t • A)` available in Mathlib.
-/

namespace Sigma
noncomputable section
open MeasureTheory NormedSpace
open scoped Matrix Topology

variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

def matrixExpDuhamelLeft (Z : Matrix n n ℝ) (r : ℝ) : Matrix n n ℝ :=
  NormedSpace.exp ℝ ((1-r) • Z)

def matrixExpDuhamelRight (Z U : Matrix n n ℝ) (r : ℝ) : Matrix n n ℝ :=
  NormedSpace.exp ℝ (r • (Z+U))

def matrixExpDuhamelIntegrand (Z U : Matrix n n ℝ) (r : ℝ) : Matrix n n ℝ :=
  matrixExpDuhamelLeft Z r * U * matrixExpDuhamelRight Z U r

def matrixExpDuhamelCurve (Z U : Matrix n n ℝ) (r : ℝ) : Matrix n n ℝ :=
  matrixExpDuhamelLeft Z r * matrixExpDuhamelRight Z U r

private theorem matrix_exp_duhamel_left_hasDerivAt (Z : Matrix n n ℝ) (r : ℝ) :
    HasDerivAt (matrixExpDuhamelLeft Z)
      (-(matrixExpDuhamelLeft Z r * Z)) r := by
  have harg : HasDerivAt (fun t : ℝ => (1-t : ℝ)) (-1) r := by
    convert (hasDerivAt_const r (1:ℝ)).sub (hasDerivAt_id r) using 1 <;> simp
  have h := (hasDerivAt_exp_smul_const Z (1-r)).scomp r harg
  convert h using 1 <;> simp [matrixExpDuhamelLeft, mul_assoc]

private theorem matrix_exp_duhamel_right_hasDerivAt
    (Z U : Matrix n n ℝ) (r : ℝ) :
    HasDerivAt (matrixExpDuhamelRight Z U)
      (matrixExpDuhamelRight Z U r * (Z+U)) r := by
  simpa only [matrixExpDuhamelRight, ← smul_add] using hasDerivAt_exp_smul_const (Z+U) r

/-- The Duhamel curve has derivative `exp((1-r)Z) U exp(r(Z+U))` even when
`Z` and `U` do not commute. -/
theorem matrix_exp_duhamel_curve_hasDerivAt (Z U : Matrix n n ℝ) (r : ℝ) :
    HasDerivAt (matrixExpDuhamelCurve Z U)
      (matrixExpDuhamelIntegrand Z U r) r := by
  have hleft := matrix_exp_duhamel_left_hasDerivAt Z r
  have hright := matrix_exp_duhamel_right_hasDerivAt Z U r
  have hcomm : Commute (matrixExpDuhamelRight Z U r) (Z+U) := by
    have h0 : Commute (Z+U) (r • (Z+U)) := (Commute.refl (Z+U)).smul_right r
    exact (h0.exp_right ℝ).symm
  have hmul := hleft.mul hright
  convert hmul using 1
  dsimp [matrixExpDuhamelIntegrand]
  rw [hcomm.eq]
  noncomm_ring

/-- Exact noncommutative Duhamel integral formula for the matrix exponential. -/
theorem matrix_exp_duhamel_integral (Z U : Matrix n n ℝ) :
    NormedSpace.exp ℝ (Z+U) - NormedSpace.exp ℝ Z =
      ∫ r : ℝ in (0:ℝ)..1, matrixExpDuhamelIntegrand Z U r := by
  have hL : Continuous (matrixExpDuhamelLeft Z) := continuous_iff_continuousAt.mpr fun r =>
      (matrix_exp_duhamel_left_hasDerivAt Z r).continuousAt
  have hR : Continuous (matrixExpDuhamelRight Z U) := continuous_iff_continuousAt.mpr fun r =>
      (matrix_exp_duhamel_right_hasDerivAt Z U r).continuousAt
  have hcont : Continuous (matrixExpDuhamelCurve Z U) := hL.mul hR
  have hcontI : Continuous (matrixExpDuhamelIntegrand Z U) :=
    (hL.mul continuous_const).mul hR
  have hint : IntervalIntegrable (matrixExpDuhamelIntegrand Z U) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact hcontI.continuousOn
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0:ℝ) ≤ 1) hcont.continuousOn
    (fun r _ => matrix_exp_duhamel_curve_hasDerivAt Z U r) hint
  have h0 : matrixExpDuhamelCurve Z U 0 = NormedSpace.exp ℝ Z := by
    simp [matrixExpDuhamelCurve, matrixExpDuhamelLeft, matrixExpDuhamelRight]
  have h1 : matrixExpDuhamelCurve Z U 1 = NormedSpace.exp ℝ (Z+U) := by
    simp [matrixExpDuhamelCurve, matrixExpDuhamelLeft, matrixExpDuhamelRight]
  rw [h0, h1] at hftc
  exact hftc.symm

/-- A local Lipschitz estimate for the matrix exponential, extracted directly from Duhamel.
The hypotheses only bound the exponentials along the two line segments that occur in the
integral. -/
theorem matrix_exp_difference_norm_le_of_segment_bounds
    (Z U : Matrix n n ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hZ : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖NormedSpace.exp ℝ (t • Z)‖ ≤ M)
    (hZU : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖NormedSpace.exp ℝ (t • (Z+U))‖ ≤ M) :
    ‖NormedSpace.exp ℝ (Z+U) - NormedSpace.exp ℝ Z‖ ≤ M^2 * ‖U‖ := by
  rw [matrix_exp_duhamel_integral]
  calc
    ‖∫ r : ℝ in (0:ℝ)..1, matrixExpDuhamelIntegrand Z U r‖
        ≤ (M^2 * ‖U‖) * |(1:ℝ) - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (C := M^2 * ‖U‖) (by
            intro r hr
            rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hr
            rcases hr with ⟨hr0, hr1⟩
            have hleft := hZ (1-r) (sub_nonneg.mpr hr1) (by linarith)
            have hright := hZU r hr0.le hr1
            dsimp [matrixExpDuhamelIntegrand, matrixExpDuhamelLeft,
              matrixExpDuhamelRight]
            calc
              ‖NormedSpace.exp ℝ ((1-r) • Z) * U * NormedSpace.exp ℝ (r • (Z+U))‖
                  ≤ ‖NormedSpace.exp ℝ ((1-r) • Z)‖ * ‖U‖ *
                    ‖NormedSpace.exp ℝ (r • (Z+U))‖ := by
                      calc
                        _ ≤ ‖NormedSpace.exp ℝ ((1-r) • Z) * U‖ *
                            ‖NormedSpace.exp ℝ (r • (Z+U))‖ := norm_mul_le _ _
                        _ ≤ (‖NormedSpace.exp ℝ ((1-r) • Z)‖ * ‖U‖) *
                            ‖NormedSpace.exp ℝ (r • (Z+U))‖ :=
                              mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
                        _ = _ := by ring
              _ ≤ M * ‖U‖ * M := by
                exact mul_le_mul (mul_le_mul hleft le_rfl (norm_nonneg _) hM)
                  hright (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))
              _ = M^2 * ‖U‖ := by ring)
    _ = M^2 * ‖U‖ := by norm_num

end
end Sigma
