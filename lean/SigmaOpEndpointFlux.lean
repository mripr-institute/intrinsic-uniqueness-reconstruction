import SigmaOpMaximalDomain
import SigmaOpHeatMarkov

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

/-- An AC function with integrable zero-mean derivative and square-integrable
values has automatic zero limits at both ends of the positive ray. -/
theorem positive_ac_zero_endpoint_limits (Q g : ℝ → ℂ)
    (hQ : PositiveRayLocallyAbsolutelyContinuous Q)
    (hg : IntegrableOn g (Ioi 0) volume)
    (hgd : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), HasDerivAt Q (g t) t)
    (hmean : (∫ t : ℝ in Ioi 0, g t) = 0)
    (hQi : IntegrableOn (fun t => ‖Q t‖^2) (Ioi 0) volume) :
    Tendsto Q (𝓝[>] 0) (𝓝 0) ∧ Tendsto Q atTop (𝓝 0) := by
  let g₀ := (Ioi (0:ℝ)).indicator g
  have hg₀ : Integrable g₀ volume := (integrable_indicator_iff measurableSet_Ioi).mpr hg
  let P : ℝ → ℂ := fun t => ∫ s in (0:ℝ)..t, g₀ s
  let C : ℂ := Q 1-P 1
  have hpoint {t : ℝ} (ht : 0 < t) : Q t = C+P t := by
    have he := hQ.integral_eq_sub hg.locallyIntegrableOn hgd (by norm_num : (0:ℝ)<1) ht
    have hi : (∫ s in (1:ℝ)..t, g s) = ∫ s in (1:ℝ)..t, g₀ s := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact (indicator_of_mem ((lt_min (by norm_num : (0:ℝ)<1) ht).trans_le hs.1) g).symm
    rw [hi,← intervalIntegral.integral_interval_sub_left (a := (0:ℝ)) hg₀.intervalIntegrable hg₀.intervalIntegrable] at he
    dsimp [C,P]
    linear_combination -he
  have hPzero : Tendsto P (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt P 0 := (intervalIntegral.continuous_primitive (fun _ _ => hg₀.intervalIntegrable) (0:ℝ)).continuousAt
    simpa only [P,intervalIntegral.integral_same] using hc.mono_left nhdsWithin_le_nhds
  have hPtop : Tendsto P atTop (𝓝 0) := by
    have hi : (∫ t : ℝ in Ioi 0, g₀ t) = 0 := by
      rw [show (∫ t : ℝ in Ioi 0, g₀ t) = ∫ t : ℝ in Ioi 0, g t from
        setIntegral_congr_fun measurableSet_Ioi (fun _ ht => indicator_of_mem ht g),hmean]
    simpa only [P,hi] using intervalIntegral_tendsto_integral_Ioi (0:ℝ) hg₀.integrableOn tendsto_id
  have hQzero : Tendsto Q (𝓝[>] 0) (𝓝 C) := by
    have he := (tendsto_const_nhds (x := C)).add hPzero
    simp only [add_zero] at he
    apply he.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hpoint ht).symm
  have hQtop : Tendsto Q atTop (𝓝 C) := by
    have he := (tendsto_const_nhds (x := C)).add hPtop
    simp only [add_zero] at he
    apply he.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    exact (hpoint ht).symm
  have hC : ‖C‖^2 = 0 := by
    apply IntegrableAtFilter.eq_zero_of_tendsto
      (show IntegrableAtFilter (fun t => ‖Q t‖^2) atTop volume from ⟨Ioi 0,Ioi_mem_atTop _,hQi⟩)
      _ (hQtop.norm.pow 2)
    intro s hs
    obtain ⟨b,hb⟩ := mem_atTop_sets.mp hs
    rw [← top_le_iff,← Real.volume_Ici (a := b)]
    exact measure_mono hb
  have hC0 : C = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hC)
  simpa only [hC0] using And.intro hQzero hQtop

theorem stein_flux_le_two {t : ℝ} (ht : 0 ≤ t) : steinFlux t ≤ 2 := by
  have he := Real.pow_div_factorial_le_exp t ht 2
  norm_num at he
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-t)).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hm
  dsimp [steinFlux]
  linarith


theorem finite_energy_flux_square_integrable (F : ℝ → ℂ)
    (he : IntegrableOn (fun t => steinFlux t*‖deriv F t‖^2) (Ioi 0) volume) :
    IntegrableOn (fun t => ‖(steinFlux t : ℂ)*deriv F t‖^2) (Ioi 0) volume := by
  apply (he.const_mul 2).mono'
  · exact (((Complex.continuous_ofReal.comp steinFlux_contDiff.continuous).measurable.mul
      (measurable_deriv F)).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hq : 0 ≤ steinFlux t := by dsimp [steinFlux]; positivity
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
    nlinarith [mul_nonneg (sub_nonneg.mpr (stein_flux_le_two ht.le))
      (mul_nonneg hq (sq_nonneg ‖deriv F t‖))]

/-- Automatic endpoint flux limits for every regular representative of every
vector in the actual operator domain. They are conclusions, not domain conditions. -/
theorem laguerre_operator_zero_flux
    (x : (laguerreSpectralOperator id).domain) (F : ℝ → ℂ)
    (hFx : F =ᵐ[gammaProbability] (x.val : ℝ → ℂ))
    (hF : PositiveRayLocallyAbsolutelyContinuous F)
    (he : IntegrableOn (fun t => steinFlux t*‖deriv F t‖^2) (Ioi 0) volume) :
    Tendsto (fun t => (steinFlux t : ℂ)*deriv F t) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun t => (steinFlux t : ℂ)*deriv F t) atTop (𝓝 0) := by
  obtain ⟨hQ,hQd⟩ := laguerre_operator_classical_flux x F hFx hF he
  have hi : IntegrableOn (fun t => -(SigmaPresentations.density t : ℂ)*laguerreSpectralOperator id x t)
      (Ioi 0) volume := by
    simpa only [neg_mul] using
      (gamma_integrable_positive_complex_density _ (laguerre_l2_integrable (laguerreSpectralOperator id x))).neg
  have hm : (∫ t : ℝ in Ioi 0,
      -(SigmaPresentations.density t : ℂ)*laguerreSpectralOperator id x t) = 0 := by
    simp_rw [neg_mul,integral_neg]
    rw [← gamma_probability_complex_integral,← laguerre_coefficient_zero_integral,
      laguerre_spectral_coordinate]
    simp
  exact positive_ac_zero_endpoint_limits _ _ hQ hi hQd hm (finite_energy_flux_square_integrable F he)


/-- The paper's automatic zero-flux clause for any locally AC representative
of an arbitrary vector in the canonical domain. No flux, energy, or endpoint
condition is required as an input. -/
theorem laguerre_canonical_zero_flux
    (x : laguerreCanonicalOperator.domain) (F : ℝ → ℂ)
    (hFx : F =ᵐ[gammaProbability] (x.val : ℝ → ℂ))
    (hF : PositiveRayLocallyAbsolutelyContinuous F) :
    Tendsto (fun t => (steinFlux t : ℂ)*deriv F t) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun t => (steinFlux t : ℂ)*deriv F t) atTop (𝓝 0) := by
  have hx : x.val ∈ (laguerreSpectralOperator id).domain :=
    laguerre_canonical_eq_spectral.le.1 x.property
  obtain ⟨G,hGx,hG,hGe,_⟩ := laguerre_square_root_regular_representative
    ⟨x.val,laguerre_integer_domain_le_square_root hx⟩
  have hFG := hF.eqOn_of_ae hG (hFx.trans hGx.symm)
  have hder {t : ℝ} (ht : 0 < t) : deriv F t=deriv G t := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact hFG hs
  have henergy : IntegrableOn (fun t => steinFlux t*‖deriv F t‖^2) (Ioi 0) volume := by
    apply hGe.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hder ht]
  exact laguerre_operator_zero_flux ⟨x.val,hx⟩ F hFx hF henergy

end
end Sigma
