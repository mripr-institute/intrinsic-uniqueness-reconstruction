import SigmaProbGammaExtension
import SigmaProbGammaProcessDyadic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecificLimits.Basic

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal

/-- The next dyadic mesh point strictly after t, including when t is already on the mesh. -/
def gammaDyadicUpperIndex (t : ℝ≥0) (n : ℕ) : ℕ × ℕ :=
  (n, ⌊(t : ℝ) * 2^n⌋₊ + 1)

theorem gamma_dyadic_upper_above (t : ℝ≥0) (n : ℕ) :
    t < gammaDyadicTime (gammaDyadicUpperIndex t n) := by
  change t < (⌊(t : ℝ) * 2^n⌋₊ + 1 : ℕ) / (2 : ℝ≥0)^n
  rw [lt_div_iff₀ (by positivity)]
  exact_mod_cast Nat.lt_floor_add_one ((t : ℝ)*2^n)

theorem gamma_dyadic_upper_bound (t : ℝ≥0) (n : ℕ) :
    gammaDyadicTime (gammaDyadicUpperIndex t n) ≤ t + 1/(2:ℝ≥0)^n := by
  change (⌊(t : ℝ) * 2^n⌋₊ + 1 : ℕ) / (2 : ℝ≥0)^n ≤ _
  rw [div_le_iff₀ (by positivity)]
  have hf := Nat.floor_le (show (0 : ℝ) ≤ (t : ℝ)*2^n by positivity)
  have hp : (2 : ℝ≥0)^n ≠ 0 := by positivity
  rw [add_mul, div_mul_cancel₀ _ hp]
  exact_mod_cast (add_le_add_right hf 1)

theorem gamma_dyadic_upper_monotone (n : ℕ) :
    Monotone (fun t => gammaDyadicTime (gammaDyadicUpperIndex t n)) := by
  intro s t hst
  change ((⌊(s : ℝ)*2^n⌋₊ + 1 : ℕ) : ℝ≥0) / (2:ℝ≥0)^n ≤
    ((⌊(t : ℝ)*2^n⌋₊ + 1 : ℕ) : ℝ≥0) / (2:ℝ≥0)^n
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh : (s : ℝ)*2^n ≤ (t : ℝ)*2^n :=
    mul_le_mul_of_nonneg_right hst (by positivity)
  exact_mod_cast Nat.add_le_add_right (Nat.floor_mono hh) 1

theorem gamma_dyadic_upper_tendsto (t : ℝ≥0) :
    Tendsto (fun n => gammaDyadicTime (gammaDyadicUpperIndex t n)) atTop (𝓝 t) := by
  have hi : Tendsto (fun n => 1/(2:ℝ≥0)^n) atTop (𝓝 0) := by
    simp_rw [one_div, ← inv_pow]
    exact NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by
      change (((2 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) < 1
      norm_num)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun n => t+1/(2:ℝ≥0)^n) atTop (𝓝 t) from by simpa using tendsto_const_nhds.add hi)
    (fun n => (gamma_dyadic_upper_above t n).le) (gamma_dyadic_upper_bound t)

theorem gamma_dyadic_time_cofinal (t : ℝ≥0) : ∃ i, t < gammaDyadicTime i :=
  ⟨gammaDyadicUpperIndex t 0, gamma_dyadic_upper_above t 0⟩

theorem gamma_dyadic_time_dense {s t : ℝ≥0} (hst : s < t) :
    ∃ i, s < gammaDyadicTime i ∧ gammaDyadicTime i < t := by
  obtain ⟨n, hn⟩ := ((gamma_dyadic_upper_tendsto s).eventually (gt_mem_nhds hst)).exists
  exact ⟨gammaDyadicUpperIndex s n, gamma_dyadic_upper_above s n, hn⟩

def gammaDyadicUpperApproximation : GammaGridUpperApproximation gammaDyadicTime where
  index := gammaDyadicUpperIndex
  above := gamma_dyadic_upper_above
  tendsto := gamma_dyadic_upper_tendsto
  monotone := gamma_dyadic_upper_monotone

end
end Sigma
