import SigmaRealTreesProbability
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace Sigma
noncomputable section
open PowerSeries Filter
open scoped Topology BigOperators

theorem rooted_real_coefficient_positive (n : ℕ) :
    0 < coeff ℝ (n + 1) (rootedSeries ℝ) := by
  rw [rooted_series_coefficients]
  positivity

theorem rooted_real_coefficient_ratio (n : ℕ) :
    coeff ℝ (n + 1 + 1) (rootedSeries ℝ) / coeff ℝ (n + 1) (rootedSeries ℝ) =
      (1 + 1 / ((n + 1 : ℕ) : ℝ)) ^ n := by
  rw [rooted_series_coefficients, rooted_series_coefficients]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hn2 : ((n + 1 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hf : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
  have hb : 1 + 1 / ((n + 1 : ℕ) : ℝ) =
      ((n + 1 + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
    push_cast
    field_simp
  rw [hb, div_pow, Nat.factorial_succ (n + 1), Nat.cast_mul, pow_succ]
  field_simp
  ring

theorem rooted_ratio_tendsto :
    Tendsto (fun n => ‖coeff ℝ (n + 1) (rootedSeries ℝ)‖ /
      ‖coeff ℝ n (rootedSeries ℝ)‖) atTop (𝓝 (Real.exp 1)) := by
  have hn : Tendsto (fun n : ℕ => (n + 1 : ℕ)) atTop atTop := tendsto_add_atTop_nat 1
  have hp := (tendsto_one_plus_div_pow_exp 1).comp hn
  have hi : Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div] using
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hn).inv_tendsto_atTop
  have hb := (tendsto_const_nhds (x := (1 : ℝ))).add hi
  have hq := hp.div hb (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have hlim : Tendsto (fun n : ℕ => (1 + 1 / ((n + 1 : ℕ) : ℝ)) ^ n)
      atTop (𝓝 (Real.exp 1)) := by
    convert hq using 1
    · funext n
      dsimp only [Function.comp_def, Pi.div_apply]
      rw [pow_succ, mul_div_cancel_right₀]
      positivity
    · simp
  apply (tendsto_add_atTop_iff_nat 1).mp
  convert hlim using 1
  funext n
  rw [Real.norm_of_nonneg (rooted_real_coefficient_positive _).le,
    Real.norm_of_nonneg (rooted_real_coefficient_positive _).le, rooted_real_coefficient_ratio]

def rootedAnalyticSeries : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun n => coeff ℝ n (rootedSeries ℝ))

theorem rooted_series_convergence_radius :
    rootedAnalyticSeries.radius = ENNReal.ofReal (Real.exp (-1)) := by
  let r : NNReal := ⟨Real.exp 1, (Real.exp_pos 1).le⟩
  have hr : r ≠ 0 := by apply NNReal.coe_ne_zero.mp; exact (Real.exp_pos 1).ne'
  have h := FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto ℝ
    (fun n => coeff ℝ n (rootedSeries ℝ)) hr rooted_ratio_tendsto
  rw [rootedAnalyticSeries, h]
  rw [Real.exp_neg]
  congr 1
  apply NNReal.eq
  simp [r, Real.toNNReal_of_nonneg (inv_nonneg.mpr (Real.exp_pos 1).le)]

end
end Sigma
