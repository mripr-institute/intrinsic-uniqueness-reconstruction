import SigmaOpMoments
import SigmaProbGamma
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral

/-! The full-line positive-measure inverse in final:O5.
Support is derived from the integer data, then the actual measure is
identified through Hausdorff uniqueness and the native Gamma distribution.
-/

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

def OpGammaIntegerSamples (μ : Measure ℝ) : Prop :=
  ∀ n : ℕ, (∫ t : ℝ, Real.exp (-(n : ℝ) * t) ∂μ) =
    (1 / (1 + (n : ℝ))) ^ (2 : ℕ)

theorem operator_integer_samples_integrable (μ : Measure ℝ)
    (h : OpGammaIntegerSamples μ) (n : ℕ) :
    Integrable (fun t : ℝ => Real.exp (-(n : ℝ) * t)) μ := by
  apply Integrable.of_integral_ne_zero
  rw [h n]
  positivity

/-- The samples derive strict positive support, including the zero-atom exclusion. -/
theorem operator_integer_samples_positive_support (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h : OpGammaIntegerSamples μ) : μ (Iic 0) = 0 := by
  have hbound : ∀ n : ℕ, (μ (Iic 0)).toReal ≤
      (1 / (1 + (n : ℝ))) ^ (2 : ℕ) := by
    intro n
    have hb : ∀ t : ℝ, (Iic (0 : ℝ)).indicator (1 : ℝ → ℝ) t ≤
        Real.exp (-(n : ℝ) * t) := by
      intro t
      by_cases ht : t ≤ 0
      · rw [indicator_of_mem (show t ∈ Iic (0 : ℝ) from ht)]
        exact Real.one_le_exp_iff.mpr
          (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg n)) ht)
      · rw [indicator_of_not_mem (show t ∉ Iic (0 : ℝ) from ht)]
        exact (Real.exp_pos _).le
    have hi : Integrable ((Iic (0 : ℝ)).indicator (1 : ℝ → ℝ)) μ :=
      (integrable_const (1 : ℝ)).indicator measurableSet_Iic
    have hh := integral_mono hi (operator_integer_samples_integrable μ h n) hb
    rw [integral_indicator_one measurableSet_Iic, h n] at hh
    exact hh
  have hl : Tendsto (fun n : ℕ => (1 / (1 + (n : ℝ))) ^ (2 : ℕ))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [add_comm, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      tendsto_one_div_add_atTop_nhds_zero_nat.pow 2
  have hz : (μ (Iic 0)).toReal = 0 :=
    le_antisymm (ge_of_tendsto' hl hbound) ENNReal.toReal_nonneg
  apply (ENNReal.toReal_eq_toReal (measure_ne_top μ _) (by simp)).mp
  simpa using hz

theorem operator_integer_samples_ae_pos (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h : OpGammaIntegerSamples μ) : ∀ᵐ t ∂μ, 0 < t := by
  rw [ae_iff]
  simpa only [not_lt] using operator_integer_samples_positive_support μ h

def opFullExpCoordinate (t : ℝ) : OpUnitInterval :=
  opExpCoordinate ⟨max t 0, le_max_right t 0⟩

theorem opFullExpCoordinate_continuous : Continuous opFullExpCoordinate :=
  opExpCoordinate_continuous.comp
    ((continuous_id.max continuous_const).subtype_mk _)

def opFullLogCoordinate (y : OpUnitInterval) : ℝ := -Real.log (y : ℝ)

theorem opFullLogCoordinate_measurable : Measurable opFullLogCoordinate :=
  (Real.measurable_log.comp measurable_subtype_coe).neg

theorem opFullLog_exp_coordinate {t : ℝ} (ht : 0 ≤ t) :
    opFullLogCoordinate (opFullExpCoordinate t) = t := by
  simp [opFullLogCoordinate, opFullExpCoordinate, opExpCoordinate, max_eq_left ht]

theorem operator_full_line_integer_laplace_unique (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : OpGammaIntegerSamples μ) (hν : OpGammaIntegerSamples ν) : μ = ν := by
  have hf := opFullExpCoordinate_continuous.measurable
  have hpush : μ.map opFullExpCoordinate = ν.map opFullExpCoordinate := by
    apply operator_hausdorff_moment_unique
    intro n
    have hi (ρ : Measure ℝ) [IsFiniteMeasure ρ] (hρ : OpGammaIntegerSamples ρ) :
        (∫ y : OpUnitInterval, (y : ℝ) ^ n ∂ρ.map opFullExpCoordinate) =
          (1 / (1 + (n : ℝ))) ^ (2 : ℕ) := by
      rw [integral_map hf.aemeasurable
        (continuous_subtype_val.pow n).measurable.aestronglyMeasurable]
      calc
        (∫ t, (opFullExpCoordinate t : ℝ) ^ n ∂ρ) =
            ∫ t, Real.exp (-(n : ℝ) * t) ∂ρ := by
          apply integral_congr_ae
          filter_upwards [operator_integer_samples_ae_pos ρ hρ] with t ht
          simp only [opFullExpCoordinate, opExpCoordinate, max_eq_left ht.le]
          rw [← Real.exp_nat_mul]
          congr 1
          ring
        _ = _ := hρ n
    exact (hi μ hμ).trans (hi ν hν).symm
  have hback (ρ : Measure ℝ) [IsFiniteMeasure ρ] (hρ : OpGammaIntegerSamples ρ) :
      (ρ.map opFullExpCoordinate).map opFullLogCoordinate = ρ := by
    rw [Measure.map_map opFullLogCoordinate_measurable hf]
    calc
      ρ.map (opFullLogCoordinate ∘ opFullExpCoordinate) = ρ.map id := by
        apply Measure.map_congr
        filter_upwards [operator_integer_samples_ae_pos ρ hρ] with t ht
        exact opFullLog_exp_coordinate ht.le
      _ = ρ := Measure.map_id
  calc
    μ = (μ.map opFullExpCoordinate).map opFullLogCoordinate := (hback μ hμ).symm
    _ = (ν.map opFullExpCoordinate).map opFullLogCoordinate := by rw [hpush]
    _ = ν := hback ν hν

theorem operator_gamma_probability_integer_samples : OpGammaIntegerSamples gammaProbability := by
  intro n
  have h := gamma_probability_laplace
    (s := (n : ℝ)) (by have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
  simpa only [neg_mul, one_div] using h

/-- The full positive-measure scalar clause of final:O5 on all of R. -/
theorem operator_full_line_mixing_characterization (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h : OpGammaIntegerSamples μ) : μ = gammaProbability := by
  letI := gamma_probability_is_probability
  exact operator_full_line_integer_laplace_unique μ gammaProbability h
    operator_gamma_probability_integer_samples

theorem operator_full_line_mixing_iff (μ : Measure ℝ) [IsFiniteMeasure μ] :
    OpGammaIntegerSamples μ ↔ μ = gammaProbability := by
  constructor
  · exact operator_full_line_mixing_characterization μ
  · intro h
    rw [h]
    exact operator_gamma_probability_integer_samples

end
end Sigma
