import SigmaOpLimitPoint

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- A continuously differentiable function on the positive ray is literally
locally absolutely continuous there, without global smoothness assumptions. -/
theorem positive_ac_of_hasDerivAt {F g : ℝ → ℂ}
    (hg : ContinuousOn g (Ioi 0)) (hd : ∀ t, 0 < t → HasDerivAt F (g t) t) :
    PositiveRayLocallyAbsolutelyContinuous F := by
  have hgl : LocallyIntegrableOn g (Ioi 0) volume := hg.locallyIntegrableOn measurableSet_Ioi
  have hP : PositiveRayLocallyAbsolutelyContinuous (fun t => ∫ s in (1:ℝ)..t, g s) := by
    intro l r hl ε hε
    exact positive_primitive_absolute_continuity g hgl (by norm_num) hl ε hε
  apply (hP.const_add (F 1)).congr
  intro t ht
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s ((lt_min (by norm_num : (0:ℝ)<1) ht).trans_le hs.1))
    (positive_locally_integrable_interval g hgl (by norm_num) ht)
  linear_combination -he

/-- A globally positive regularization of log(1/t), used to avoid a cutoff
singularity away from zero in the paper's log-log domain witness. -/
def endpointLogDenominator (t : ℝ) : ℝ := 1+Real.log (1+t⁻¹)

def laguerreUnboundedRepresentative (t : ℝ) : ℂ := Real.log (endpointLogDenominator t)

def endpointWitnessFlux (t : ℝ) : ℝ :=
  -t*Real.exp (-t)/((t+1)*endpointLogDenominator t)

def endpointWitnessImage (t : ℝ) : ℝ :=
  ((1-t-t^2)*endpointLogDenominator t+1)/(t*(t+1)^2*(endpointLogDenominator t)^2)

theorem endpoint_log_denominator_one_le {t : ℝ} (ht : 0 < t) : 1 ≤ endpointLogDenominator t := by
  have hl : 0 ≤ Real.log (1+t⁻¹) := Real.log_nonneg (le_add_of_nonneg_right (inv_nonneg.mpr ht.le))
  dsimp [endpointLogDenominator]
  linarith

theorem endpoint_log_denominator_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt endpointLogDenominator (-(t*(t+1))⁻¹) t := by
  have ht0 : t ≠ 0 := ht.ne'
  have hp : 1+t⁻¹ ≠ 0 := ne_of_gt (by positivity)
  have hd := (((hasDerivAt_id t).inv ht0).const_add 1).log hp
  convert hd.const_add 1 using 1
  dsimp [endpointLogDenominator]
  field_simp
  ring

theorem laguerre_unbounded_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt laguerreUnboundedRepresentative
      (-(t*(t+1)*endpointLogDenominator t)⁻¹ : ℝ) t := by
  have hL : endpointLogDenominator t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (endpoint_log_denominator_one_le ht))
  have hd := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
    ((endpoint_log_denominator_hasDerivAt ht).log hL)
  convert hd using 1
  push_cast
  field_simp

theorem endpoint_witness_flux_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt endpointWitnessFlux (-SigmaPresentations.density t*endpointWitnessImage t) t := by
  have hL : endpointLogDenominator t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (endpoint_log_denominator_one_le ht))
  have hp : t+1 ≠ 0 := ne_of_gt (by linarith)
  have hd := (((hasDerivAt_id t).neg.mul ((hasDerivAt_id t).neg.exp)).div
    (((hasDerivAt_id t).add_const 1).mul (endpoint_log_denominator_hasDerivAt ht)) (mul_ne_zero hp hL))
  convert hd using 1
  dsimp [endpointWitnessImage,SigmaPresentations.density]
  field_simp
  ring

theorem endpoint_log_denominator_continuousOn : ContinuousOn endpointLogDenominator (Ioi 0) :=
  fun _ ht => (endpoint_log_denominator_hasDerivAt ht).continuousAt.continuousWithinAt

theorem endpoint_witness_image_continuousOn : ContinuousOn endpointWitnessImage (Ioi 0) := by
  apply (((continuousOn_const.sub continuousOn_id).sub (continuousOn_id.pow 2)).mul
    endpoint_log_denominator_continuousOn |>.add continuousOn_const).div
    ((continuousOn_id.mul ((continuousOn_id.add continuousOn_const).pow 2)).mul
      (endpoint_log_denominator_continuousOn.pow 2))
  intro t ht
  change 0 < t at ht
  change t*(t+1)^2*(endpointLogDenominator t)^2 ≠ 0
  have hL : 0 < endpointLogDenominator t := lt_of_lt_of_le zero_lt_one (endpoint_log_denominator_one_le ht)
  positivity


theorem endpoint_log_denominator_tendsto_zero :
    Tendsto endpointLogDenominator (𝓝[>] (0:ℝ)) atTop :=
  tendsto_atTop_add_const_left _ 1 (Real.tendsto_log_atTop.comp
    (tendsto_atTop_add_const_left _ 1 tendsto_inv_zero_atTop))

theorem endpoint_log_denominator_tendsto_infinity :
    Tendsto endpointLogDenominator atTop (𝓝 1) := by
  have hi : Tendsto (fun t : ℝ => 1+t⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_inv_atTop_zero.const_add 1 :
      Tendsto (fun t : ℝ => 1+t⁻¹) atTop (𝓝 (1+0)))
  have hl := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp hi
  simpa [endpointLogDenominator] using hl.const_add 1

theorem laguerre_unbounded_representative_tendsto :
    Tendsto (fun t => (laguerreUnboundedRepresentative t).re) (𝓝[>] (0:ℝ)) atTop :=
  Real.tendsto_log_atTop.comp endpoint_log_denominator_tendsto_zero

theorem laguerre_unbounded_representative_locally_ac :
    PositiveRayLocallyAbsolutelyContinuous laguerreUnboundedRepresentative := by
  apply positive_ac_of_hasDerivAt (g := fun t => (-(t*(t+1)*endpointLogDenominator t)⁻¹ : ℝ)) _
    (fun _ ht => laguerre_unbounded_hasDerivAt ht)
  apply Complex.continuous_ofReal.comp_continuousOn
  apply ContinuousOn.neg
  apply ((continuousOn_id.mul (continuousOn_id.add continuousOn_const)).mul
    endpoint_log_denominator_continuousOn).inv₀
  intro t ht
  change 0 < t at ht
  have hL := lt_of_lt_of_le zero_lt_one (endpoint_log_denominator_one_le ht)
  positivity

theorem laguerre_unbounded_flux_identity {t : ℝ} (ht : 0 < t) :
    (steinFlux t : ℂ)*deriv laguerreUnboundedRepresentative t = (endpointWitnessFlux t : ℂ) := by
  rw [(laguerre_unbounded_hasDerivAt ht).deriv]
  simp only [← Complex.ofReal_mul]
  congr 1
  dsimp [steinFlux,endpointWitnessFlux]
  have hL := ne_of_gt (lt_of_lt_of_le zero_lt_one (endpoint_log_denominator_one_le ht))
  field_simp
  ring

theorem endpoint_witness_flux_locally_ac :
    PositiveRayLocallyAbsolutelyContinuous (fun t => (endpointWitnessFlux t : ℂ)) := by
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt (fun t => (endpointWitnessFlux t : ℂ))
      (-SigmaPresentations.density t*endpointWitnessImage t : ℝ) t :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (endpoint_witness_flux_hasDerivAt ht)
  apply positive_ac_of_hasDerivAt _ hd
  apply Complex.continuous_ofReal.comp_continuousOn
  exact ((continuous_id.mul continuous_id.neg.rexp).neg.continuousOn).mul
    endpoint_witness_image_continuousOn

theorem laguerre_unbounded_flux_locally_ac :
    PositiveRayLocallyAbsolutelyContinuous
      (fun t => (steinFlux t : ℂ)*deriv laguerreUnboundedRepresentative t) :=
  endpoint_witness_flux_locally_ac.congr (fun _ ht => laguerre_unbounded_flux_identity ht)

theorem laguerre_unbounded_divergence {t : ℝ} (ht : 0 < t) :
    laguerreDivergenceExpression laguerreUnboundedRepresentative t = (endpointWitnessImage t : ℂ) := by
  have he : (fun t => (steinFlux t : ℂ)*deriv laguerreUnboundedRepresentative t) =ᶠ[𝓝 t]
      (fun t => (endpointWitnessFlux t : ℂ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact laguerre_unbounded_flux_identity hs
  have hd := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (endpoint_witness_flux_hasDerivAt ht)
  have hp : (SigmaPresentations.density t : ℂ) ≠ 0 := by
    have hh : 0 < SigmaPresentations.density t := mul_pos ht (Real.exp_pos _)
    exact_mod_cast hh.ne'
  change HasDerivAt (fun t => (endpointWitnessFlux t : ℂ))
    (-SigmaPresentations.density t*endpointWitnessImage t : ℝ) t at hd
  rw [laguerreDivergenceExpression,he.deriv_eq,hd.deriv]
  push_cast
  field_simp

end
end Sigma
