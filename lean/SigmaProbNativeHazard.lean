import SigmaProbSurvivalAC
import Mathlib.MeasureTheory.Decomposition.RadonNikodym

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology

/-- The actual real Radon--Nikodym density, not an independently specified
coefficient in a differential equation. -/
def lifetimeDensity (μ : Measure ℝ) (x : ℝ) : ℝ := (μ.rnDeriv volume x).toReal

def lifetimeHazard (μ : Measure ℝ) (x : ℝ) : ℝ :=
  lifetimeDensity μ x / lifetimeSurvival μ x

theorem lifetime_density_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (lifetimeDensity μ) := Measure.integrable_toReal_rnDeriv

/-- Native absolute continuity supplies the integral representation of the
survival at every pair of endpoints, without a differentiability premise. -/
theorem ac_lifetime_survival_increment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (a x : ℝ) :
    lifetimeSurvival μ x=lifetimeSurvival μ a-∫ t : ℝ in a..x, lifetimeDensity μ t := by
  have hi := lifetime_density_integrable μ
  have h := intervalIntegral.integral_Iic_sub_Iic
    (hi.integrableOn (s := Iic a)) (hi.integrableOn (s := Iic x))
  simp only [lifetimeDensity,Measure.setIntegral_toReal_rnDeriv hμ] at h
  rw [lifetime_survival_eq_one_sub_cdf,lifetime_survival_eq_one_sub_cdf,
    cdf_eq_toReal,cdf_eq_toReal]
  change (μ (Iic x)).toReal-(μ (Iic a)).toReal =
    ∫ t : ℝ in a..x,lifetimeDensity μ t at h
  linarith

theorem ac_lifetime_survival_continuous (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) : Continuous (lifetimeSurvival μ) := by
  have he : lifetimeSurvival μ = fun x => lifetimeSurvival μ 0-
      ∫ t : ℝ in (0:ℝ)..x,lifetimeDensity μ t :=
    funext (ac_lifetime_survival_increment μ hμ 0)
  rw [he]
  exact continuous_const.sub ((lifetime_density_integrable μ).continuous_primitive 0)

/-- An a.e. continuous density representative gives the classical survival
derivative by the native Radon--Nikodym formula and FTC. -/
theorem ac_lifetime_survival_derivative (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (R : ℝ → ℝ) (hR : ContinuousOn R (Ioi 0))
    (he : lifetimeDensity μ =ᵐ[volume.restrict (Ioi 0)] R)
    (t : ℝ) (ht : 0<t) : HasDerivAt (lifetimeSurvival μ) (-R t) t := by
  have he' := (ae_restrict_iff' measurableSet_Ioi).mp he
  have hpos : ∀ᶠ x in 𝓝 t, 0<x := Ioi_mem_nhds ht
  have heq : lifetimeDensity μ =ᶠ[𝓝 t ⊓ ae volume] R := by
    filter_upwards [hpos.filter_mono inf_le_left,
      he'.filter_mono inf_le_right] with x hx hex
    exact hex hx
  have hlim : Tendsto (lifetimeDensity μ) (𝓝 t ⊓ ae volume) (𝓝 (R t)) :=
    ((hR.continuousAt (Ioi_mem_nhds ht)).tendsto.mono_left inf_le_left).congr' heq.symm
  have hm : StronglyMeasurableAtFilter (lifetimeDensity μ) (𝓝 t) volume :=
    (Measure.measurable_rnDeriv μ volume).ennreal_toReal.aestronglyMeasurable.stronglyMeasurableAtFilter
  have hd := (intervalIntegral.integral_hasDerivAt_of_tendsto_ae_right (a := 0)
    (lifetime_density_integrable μ).intervalIntegrable hm hlim).const_sub (lifetimeSurvival μ 0)
  convert hd using 1
  · exact funext (ac_lifetime_survival_increment μ hμ 0)

theorem ac_lifetime_survival_local_ac_of_density (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (R : ℝ → ℝ) (hR : ContinuousOn R (Ioi 0))
    (he : lifetimeDensity μ =ᵐ[volume.restrict (Ioi 0)] R) :
    LocallyIntegralAbsolutelyContinuousPositive (lifetimeSurvival μ) := by
  intro a b ha hab
  refine ⟨fun x => -lifetimeDensity μ x,(lifetime_density_integrable μ).neg.integrableOn,?_,?_⟩
  · have he' := (ae_restrict_iff' measurableSet_Ioi).mp he
    filter_upwards [ae_restrict_of_ae he',ae_restrict_mem measurableSet_Ioo] with x hex hx
    rw [hex (ha.trans hx.1)]
    exact ac_lifetime_survival_derivative μ hμ R hR he x (ha.trans hx.1)
  · intro x hx
    rw [intervalIntegral.integral_neg,← sub_eq_add_neg]
    exact ac_lifetime_survival_increment μ hμ a x

/-- Native paper input: absolute continuity of the probability and equality
of its actual density-to-survival hazard. All tail regularity is derived. -/
theorem gamma_probability_native_hazard_inverse (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (hpos : ∀ x>0, 0<lifetimeSurvival μ x)
    (h0 : lifetimeSurvival μ 0=1)
    (hh : lifetimeHazard μ =ᵐ[volume.restrict (Ioi 0)] gammaHazard) :
    μ=gammaProbability := by
  let R : ℝ → ℝ := fun x => gammaHazard x*lifetimeSurvival μ x
  have hR : ContinuousOn R (Ioi 0) := by
    apply (continuousOn_id.div (continuousOn_const.add continuousOn_id)
      (fun x hx => by change 0<x at hx; dsimp; linarith)).mul
    exact (ac_lifetime_survival_continuous μ hμ).continuousOn
  have he : lifetimeDensity μ =ᵐ[volume.restrict (Ioi 0)] R := by
    filter_upwards [hh,ae_restrict_mem measurableSet_Ioi] with x hx hxp
    exact (div_eq_iff (hpos x hxp).ne').mp hx
  apply gamma_probability_local_ac_hazard_inverse μ
    (ac_lifetime_survival_local_ac_of_density μ hμ R hR he) h0
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa [R,neg_mul] using ac_lifetime_survival_derivative μ hμ R hR he x hx

/-- The logarithmic-coordinate hazard is the actual hazard of the supplied
probability, composed with exp, not a free solution to the logistic ODE. -/
theorem gamma_probability_native_marked_logistic_inverse (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    (hpos : ∀ x>0, 0<lifetimeSurvival μ x) (h0 : lifetimeSurvival μ 0=1)
    (v : ℝ → ℝ) (hv : ∀ u, HasDerivAt v (v u*(1-v u)) u) (hv0 : v 0=1/2)
    (hmark : ∀ᵐ x ∂volume.restrict (Ioi 0), lifetimeHazard μ x=v (Real.log x)) :
    μ=gammaProbability := by
  have he := logistic_hazard_unique v hv hv0
  apply gamma_probability_native_hazard_inverse μ hμ hpos h0
  filter_upwards [hmark,ae_restrict_mem measurableSet_Ioi] with x hx hxp
  simpa only [he,logistic_hazard_coordinate,Real.exp_log hxp] using hx

/-- Special case where the marked function is the fixed Radon--Nikodym
representative itself; the preceding theorem also permits any a.e.-equal
density/hazard representative. -/
theorem gamma_probability_native_logistic_inverse (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (hpos : ∀ x>0, 0<lifetimeSurvival μ x)
    (h0 : lifetimeSurvival μ 0=1)
    (hv : ∀ u, HasDerivAt (fun v => lifetimeHazard μ (Real.exp v))
      (lifetimeHazard μ (Real.exp u)*(1-lifetimeHazard μ (Real.exp u))) u)
    (hv0 : lifetimeHazard μ 1=1/2) : μ=gammaProbability := by
  have he := logistic_hazard_unique (fun u => lifetimeHazard μ (Real.exp u)) hv
    (by simpa using hv0)
  apply gamma_probability_native_hazard_inverse μ hμ hpos h0
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have h := congrFun he (Real.log x)
  simpa only [Real.exp_log hx,logistic_hazard_coordinate] using h

end
end Sigma
