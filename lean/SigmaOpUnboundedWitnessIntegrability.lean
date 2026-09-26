import SigmaOpUnboundedWitnessCalculus
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

def endpointWitnessKernel (t : ℝ) : ℝ := (t*(t+1)*(endpointLogDenominator t)^2)⁻¹

def endpointWitnessPrimitive (t : ℝ) : ℝ := if 0 < t then (endpointLogDenominator t)⁻¹ else 0

theorem endpoint_witness_primitive_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt endpointWitnessPrimitive (endpointWitnessKernel t) t := by
  have hL : endpointLogDenominator t ≠ 0 := ne_of_gt
    (lt_of_lt_of_le zero_lt_one (endpoint_log_denominator_one_le ht))
  have hd := (endpoint_log_denominator_hasDerivAt ht).inv hL
  have he : endpointWitnessPrimitive =ᶠ[𝓝 t] (fun t => (endpointLogDenominator t)⁻¹) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    simp [endpointWitnessPrimitive,show 0 < s from hs]
  apply HasDerivAt.congr_of_eventuallyEq _ he
  convert hd using 1
  dsimp [endpointWitnessKernel]
  field_simp

theorem endpoint_witness_kernel_integrable : IntegrableOn endpointWitnessKernel (Ioi 0) volume := by
  have hz : Tendsto endpointWitnessPrimitive (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply (tendsto_inv_atTop_zero.comp endpoint_log_denominator_tendsto_zero).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [endpointWitnessPrimitive,show 0 < t from ht]
  have hc : ContinuousWithinAt endpointWitnessPrimitive (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    simpa [ContinuousWithinAt,endpointWitnessPrimitive] using hz
  have hinf : Tendsto endpointWitnessPrimitive atTop (𝓝 1) := by
    have hi := endpoint_log_denominator_tendsto_infinity.inv₀ (by norm_num : (1:ℝ) ≠ 0)
    simp only [inv_one] at hi
    apply hi.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    simp [endpointWitnessPrimitive,show 0 < t from ht]
  apply integrableOn_Ioi_deriv_of_nonneg hc (fun _ ht => endpoint_witness_primitive_hasDerivAt ht) _ hinf
  intro t ht
  change 0 < t at ht
  dsimp [endpointWitnessKernel]
  positivity

theorem endpoint_witness_image_bound {t : ℝ} (ht : 0 < t) :
    |endpointWitnessImage t| ≤ 2/(t*endpointLogDenominator t) := by
  have hL := endpoint_log_denominator_one_le ht
  have hLp : 0 < endpointLogDenominator t := lt_of_lt_of_le zero_lt_one hL
  have hA : |1-t-t^2| ≤ (t+1)^2 := abs_le.mpr ⟨by nlinarith,by nlinarith⟩
  have hn : |(1-t-t^2)*endpointLogDenominator t+1| ≤ 2*(t+1)^2*endpointLogDenominator t := by
    have h := abs_add_le ((1-t-t^2)*endpointLogDenominator t) 1
    simp only [abs_mul,abs_of_pos hLp,abs_one] at h
    have h := h.trans (add_le_add_right (mul_le_mul_of_nonneg_right hA hLp.le) 1)
    have hprod := mul_le_mul_of_nonneg_left hL (sq_nonneg (t+1))
    nlinarith
  rw [endpointWitnessImage,abs_div,abs_of_pos (show 0 < t*(t+1)^2*endpointLogDenominator t^2 by positivity)]
  calc
    _ ≤ (2*(t+1)^2*endpointLogDenominator t)/(t*(t+1)^2*endpointLogDenominator t^2) :=
      div_le_div_of_nonneg_right hn (by positivity)
    _ = _ := by field_simp; ring

theorem endpoint_witness_image_density_bound {t : ℝ} (ht : 0 < t) :
    SigmaPresentations.density t*(endpointWitnessImage t)^2 ≤ 4*endpointWitnessKernel t := by
  have hL := lt_of_lt_of_le zero_lt_one (endpoint_log_denominator_one_le ht)
  have hsq : (endpointWitnessImage t)^2 ≤ (2/(t*endpointLogDenominator t))^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (endpointWitnessImage t)) (endpoint_witness_image_bound ht) 2
  have hp : 0 ≤ SigmaPresentations.density t := (mul_pos ht (Real.exp_pos _)).le
  have he : (t+1)*Real.exp (-t) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp t) (Real.exp_pos (-t)).le
    rwa [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hh
  have heq : SigmaPresentations.density t*(2/(t*endpointLogDenominator t))^2 =
      4*((t+1)*Real.exp (-t))*endpointWitnessKernel t := by
    dsimp [SigmaPresentations.density,endpointWitnessKernel]
    field_simp
    ring
  have hk : 0 ≤ endpointWitnessKernel t := by dsimp [endpointWitnessKernel]; positivity
  calc
    _ ≤ SigmaPresentations.density t*(2/(t*endpointLogDenominator t))^2 := mul_le_mul_of_nonneg_left hsq hp
    _ = _ := heq
    _ ≤ 4*endpointWitnessKernel t := by nlinarith [mul_le_mul_of_nonneg_right he hk]


theorem endpoint_log_denominator_measurable : Measurable endpointLogDenominator :=
  measurable_const.add (Real.measurable_log.comp (measurable_const.add measurable_id.inv))

theorem laguerre_unbounded_representative_measurable : Measurable laguerreUnboundedRepresentative :=
  Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp endpoint_log_denominator_measurable)

theorem laguerre_unbounded_representative_norm_sq_bound {t : ℝ} (ht : 0 < t) :
    ‖laguerreUnboundedRepresentative t‖^2 ≤ 4*(1+t⁻¹) := by
  have hx : 0 < 1+t⁻¹ := by positivity
  have hL := endpoint_log_denominator_one_le ht
  have hLp := lt_of_lt_of_le zero_lt_one hL
  have hF0 : 0 ≤ Real.log (endpointLogDenominator t) := Real.log_nonneg hL
  have hF : Real.log (endpointLogDenominator t) ≤ Real.log (1+t⁻¹) := by
    have h := Real.log_le_sub_one_of_pos hLp
    dsimp [endpointLogDenominator] at h ⊢
    linarith
  have hlog := Real.log_le_rpow_div hx.le (by norm_num : (0:ℝ)<1/2)
  rw [← Real.sqrt_eq_rpow] at hlog
  have hb : Real.log (endpointLogDenominator t) ≤ 2*Real.sqrt (1+t⁻¹) := by linarith
  have hsq := pow_le_pow_left₀ hF0 hb 2
  simp only [mul_pow,Real.sq_sqrt hx.le] at hsq
  simpa only [laguerreUnboundedRepresentative,Complex.norm_real,Real.norm_eq_abs,sq_abs,show (2:ℝ)^2=4 by norm_num] using hsq

theorem laguerre_unbounded_representative_mem_l2 :
    Memℒp laguerreUnboundedRepresentative 2 gammaProbability := by
  rw [memℒp_two_iff_integrable_sq_norm laguerre_unbounded_representative_measurable.aestronglyMeasurable,
    gamma_integrable_iff_positive_density]
  have hi0 : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) volume := by
    simpa only [Real.rpow_one,Real.rpow_zero,one_mul,neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (p := 1) (b := 1)
        (by norm_num) le_rfl (by norm_num))
  have hi1 : IntegrableOn (fun t : ℝ => t*Real.exp (-t)) (Ioi 0) volume := by
    simpa only [Real.rpow_one,one_mul,neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := 1)
        (by norm_num) le_rfl (by norm_num))
  apply ((hi1.add hi0).const_mul 4).mono'
  · exact ((continuous_id.mul continuous_id.neg.rexp).measurable.mul
      (laguerre_unbounded_representative_measurable.norm.pow_const 2)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp : 0 ≤ SigmaPresentations.density t := (mul_pos ht (Real.exp_pos _)).le
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hp (sq_nonneg _))]
    have he : SigmaPresentations.density t*(4*(1+t⁻¹)) = 4*(t*Real.exp (-t)+Real.exp (-t)) := by
      dsimp [SigmaPresentations.density]
      field_simp [ne_of_gt ht]
      ring
    exact (mul_le_mul_of_nonneg_left (laguerre_unbounded_representative_norm_sq_bound ht) hp).trans_eq he

theorem laguerre_unbounded_divergence_mem_l2 :
    Memℒp (laguerreDivergenceExpression laguerreUnboundedRepresentative) 2 gammaProbability := by
  have hm : Measurable (laguerreDivergenceExpression laguerreUnboundedRepresentative) :=
    (((Complex.continuous_ofReal.comp (continuous_id.mul continuous_id.neg.rexp)).measurable.inv.neg).mul
      (measurable_deriv _))
  rw [memℒp_two_iff_integrable_sq_norm hm.aestronglyMeasurable,gamma_integrable_iff_positive_density]
  apply (endpoint_witness_kernel_integrable.const_mul 4).mono'
  · exact ((continuous_id.mul continuous_id.neg.rexp).measurable.mul (hm.norm.pow_const 2)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp : 0 ≤ SigmaPresentations.density t := (mul_pos ht (Real.exp_pos _)).le
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hp (sq_nonneg _))]
    rw [laguerre_unbounded_divergence ht]
    simpa only [Complex.norm_real,Real.norm_eq_abs,sq_abs] using endpoint_witness_image_density_bound ht

end
end Sigma
