import SigmaOpACZeroDerivative
import SigmaOpFiniteEnergy

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

theorem PositiveRayLocallyAbsolutelyContinuous.sub
    {F G : ℝ → ℂ} (hF : PositiveRayLocallyAbsolutelyContinuous F)
    (hG : PositiveRayLocallyAbsolutelyContinuous G) :
    PositiveRayLocallyAbsolutelyContinuous (fun t => F t-G t) := by
  intro a b ha ε hε
  have hhalf : ε/2 ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hε,by norm_num⟩
  obtain ⟨δF,hδF,hcF⟩ := hF a b ha (ε/2) hhalf
  obtain ⟨δG,hδG,hcG⟩ := hG a b ha (ε/2) hhalf
  refine ⟨min δF δG,lt_min hδF hδG,?_⟩
  intro n u v huv hdis hlen
  have hf := hcF n u v huv hdis (hlen.trans_le (min_le_left _ _))
  have hg := hcG n u v huv hdis (hlen.trans_le (min_le_right _ _))
  have hb : (∑ i, (‖(F (v i)-G (v i))-(F (u i)-G (u i))‖₊ : ℝ≥0∞)) ≤
      (∑ i, (‖F (v i)-F (u i)‖₊ : ℝ≥0∞)) +
      (∑ i, (‖G (v i)-G (u i)‖₊ : ℝ≥0∞)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have he : (F (v i)-G (v i))-(F (u i)-G (u i)) =
        (F (v i)-F (u i))-(G (v i)-G (u i)) := by abel
    rw [he, ← ENNReal.coe_add, ENNReal.coe_le_coe]
    exact nnnorm_sub_le _ _
  exact hb.trans_lt ((ENNReal.add_lt_add hf hg).trans_eq (ENNReal.add_halves ε))

/-- Fundamental theorem for the literal local AC condition, with a locally
integrable a.e. derivative. The a.e.-zero uniqueness step rules out a singular
part rather than replacing a.e. differentiability by everywhere differentiability. -/
theorem PositiveRayLocallyAbsolutelyContinuous.integral_eq_sub
    {F g : ℝ → ℂ} (hF : PositiveRayLocallyAbsolutelyContinuous F)
    (hg : LocallyIntegrableOn g (Ioi 0) volume)
    (hder : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), HasDerivAt F (g t) t)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in a..b, g t) = F b-F a := by
  let P : ℝ → ℂ := fun t => ∫ s in a..t, g s
  have hP : PositiveRayLocallyAbsolutelyContinuous P := by
    intro l r hl ε hε
    exact positive_primitive_absolute_continuity g hg ha hl ε hε
  have hD : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), HasDerivAt (fun t => F t-P t) 0 t := by
    filter_upwards [hder,positive_primitive_hasDerivAt_ae g hg ha] with t hf hp
    simpa only [sub_self] using hf.sub hp
  have he : F b-P b = F a-P a := by
    rcases lt_trichotomy a b with hab | hab | hab
    · exact (hF.sub hP).eq_of_ae_hasDerivAt_zero hD ha hab
    · subst b
      rfl
    · exact ((hF.sub hP).eq_of_ae_hasDerivAt_zero hD hb hab).symm
  dsimp only [P] at he
  rw [intervalIntegral.integral_same,sub_zero] at he
  linear_combination -he

theorem finite_energy_derivative_representative (F : ℝ → ℂ)
    (hF : IntegrableOn (fun t => steinFlux t * ‖deriv F t‖^2) (Ioi 0) volume) :
    deriv F =ᵐ[volume.restrict (Ioi 0)] weightedDerivativeRepresentative (finiteEnergyGradient F hF) := by
  have hcoe := gamma_ae_iff_positive_volume_ae.mp (finite_energy_gradient_coe F hF)
  filter_upwards [hcoe,ae_restrict_mem measurableSet_Ioi] with t ht htp
  have hs : (Real.sqrt t : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr htp).ne'
  simp only [weightedDerivativeRepresentative,ht,weightedTestDerivative]
  rw [mul_div_cancel_left₀ _ hs]

theorem finite_energy_derivative_locally_integrable (F : ℝ → ℂ)
    (hF : IntegrableOn (fun t => steinFlux t * ‖deriv F t‖^2) (Ioi 0) volume) :
    LocallyIntegrableOn (deriv F) (Ioi 0) volume := by
  intro x hx
  obtain ⟨s,hs,hi⟩ := gamma_l2_div_sqrt_locally_integrable (finiteEnergyGradient F hF) x hx
  refine ⟨s ∩ Ioi 0,inter_mem hs self_mem_nhdsWithin,(hi.mono_set inter_subset_left).congr ?_⟩
  exact ae_restrict_of_ae_restrict_of_subset inter_subset_right
    (finite_energy_derivative_representative F hF).symm

/-- A locally AC finite-energy representative satisfies the actual integral
reconstruction formula on every compact positive interval. -/
theorem finite_energy_ac_integral_deriv {F : ℝ → ℂ}
    (hF : PositiveRayLocallyAbsolutelyContinuous F)
    (henergy : IntegrableOn (fun t => steinFlux t * ‖deriv F t‖^2) (Ioi 0) volume)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in a..b, deriv F t) = F b-F a := by
  apply hF.integral_eq_sub (finite_energy_derivative_locally_integrable F henergy) _ ha hb
  filter_upwards [hF.ae_differentiableAt] with t ht
  exact ht.hasDerivAt

end
end Sigma
