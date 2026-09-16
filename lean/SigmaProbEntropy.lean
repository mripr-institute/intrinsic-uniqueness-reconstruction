import SigmaProbGamma
import Mathlib.Data.Real.EReal

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

def entropyDefect (z : ℝ) : ℝ := z * Real.log z - z + 1

theorem entropy_defect_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ entropyDefect z := by
  rcases hz.eq_or_lt with rfl | hz
  · norm_num [entropyDefect]
  · have he := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hz) hz.le
    rw [mul_sub, mul_one, mul_inv_cancel₀ hz.ne'] at he
    unfold entropyDefect
    linarith

theorem entropy_defect_eq_zero {z : ℝ} (hz : 0 ≤ z) : entropyDefect z = 0 ↔ z = 1 := by
  constructor
  · intro he
    by_contra hne
    rcases hz.eq_or_lt with rfl | hz
    · norm_num [entropyDefect] at he
    · have hi := Real.log_lt_sub_one_of_pos (inv_pos.mpr hz)
        (fun h => hne (inv_eq_one.mp h))
      rw [Real.log_inv] at hi
      have hm := mul_lt_mul_of_pos_left hi hz
      rw [mul_sub, mul_neg, mul_inv_cancel₀ hz.ne', mul_one] at hm
      unfold entropyDefect at he
      linarith
  · rintro rfl
    simp [entropyDefect]

theorem entropy_defect_measurable : Measurable entropyDefect := by
  exact ((measurable_id.mul Real.measurable_log).sub measurable_id).add_const 1

def gammaDensityDivergence (f : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
    (SigmaPresentations.density t * entropyDefect (f t / SigmaPresentations.density t))

theorem gamma_density_divergence_zero_iff (f : ℝ → ℝ) (hf : Measurable f)
    (hpos : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ f t) :
    gammaDensityDivergence f = 0 ↔
      f =ᵐ[volume.restrict (Ioi 0)] SigmaPresentations.density := by
  have hp : Measurable SigmaPresentations.density :=
    (continuous_id.mul continuous_id.neg.rexp).measurable
  have hm : Measurable (fun t => ENNReal.ofReal
      (SigmaPresentations.density t * entropyDefect (f t / SigmaPresentations.density t))) :=
    (hp.mul (entropy_defect_measurable.comp (hf.div hp))).ennreal_ofReal
  rw [gammaDensityDivergence, lintegral_eq_zero_iff hm]
  constructor
  · intro he
    filter_upwards [he, hpos, ae_restrict_mem measurableSet_Ioi] with t ht hft ht0
    have hpt := SigmaPresentations.density_pos ht0
    have hd := entropy_defect_nonneg (div_nonneg hft hpt.le)
    have hz : SigmaPresentations.density t * entropyDefect (f t / SigmaPresentations.density t) = 0 := by
      apply le_antisymm
      · exact ENNReal.ofReal_eq_zero.mp ht
      · exact mul_nonneg hpt.le hd
    have hr := (entropy_defect_eq_zero (div_nonneg hft hpt.le)).mp
      ((mul_eq_zero.mp hz).resolve_left hpt.ne')
    exact (div_eq_one_iff_eq hpt.ne').mp hr
  · intro he
    filter_upwards [he, ae_restrict_mem measurableSet_Ioi] with t ht ht0
    rw [ht, div_self (SigmaPresentations.density_pos ht0).ne']
    simp [entropyDefect]

def calibratedExtendedEntropy (C : ℝ) (f : ℝ → ℝ) : EReal :=
  (C : EReal) - (gammaDensityDivergence f : EReal)

theorem calibrated_extended_entropy_bound (C : ℝ) (f : ℝ → ℝ) :
    calibratedExtendedEntropy C f ≤ (C : EReal) := by
  simpa [calibratedExtendedEntropy] using
    EReal.sub_le_sub (le_refl (C : EReal))
      (EReal.coe_ennreal_nonneg (gammaDensityDivergence f))

theorem calibrated_extended_entropy_equality_iff (C : ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) (hpos : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ f t) :
    calibratedExtendedEntropy C f = (C : EReal) ↔
      f =ᵐ[volume.restrict (Ioi 0)] SigmaPresentations.density := by
  rw [← gamma_density_divergence_zero_iff f hf hpos]
  unfold calibratedExtendedEntropy
  by_cases hT : gammaDensityDivergence f = ∞
  · simp [hT]
  · lift gammaDensityDivergence f to ℝ≥0 using hT with d hd
    simp only [EReal.coe_nnreal_eq_coe_real, ← EReal.coe_sub, EReal.coe_eq_coe_iff]
    constructor
    · intro he
      have hz : (d : ℝ) = 0 := by linarith
      exact_mod_cast hz
    · intro he
      have hz : (d : ℝ) = 0 := by exact_mod_cast he
      simp [hz]

end
end Sigma
