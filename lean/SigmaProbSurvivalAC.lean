import SigmaOperatorPearson
import SigmaProbSurvival
import SigmaProbEquilibrium
import Mathlib.Probability.CDF

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

/-- A continuous right hand side upgrades an a.e. differential equation for
a locally absolutely continuous function to its everywhere classical form. -/
theorem local_ac_continuous_rhs_hasDerivAt (w R : ℝ → ℝ)
    (hw : LocallyIntegralAbsolutelyContinuousPositive w)
    (hR : ContinuousOn R (Ioi 0))
    (hd : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), HasDerivAt w (R t) t)
    (t : ℝ) (ht : 0<t) : HasDerivAt w (R t) t := by
  let a : ℝ := t/2
  let b : ℝ := t+1
  have ha : 0<a := by dsimp [a]; positivity
  have hat : a<t := by dsimp [a]; linarith
  have htb : t<b := by dsimp [b]; linarith
  obtain ⟨g,hg,hgd,hrep⟩ := hw a b ha (hat.trans htb)
  have hRc : ContinuousOn R (Icc a b) := hR.mono (fun s hs => ha.trans_le hs.1)
  have hdg := (ae_restrict_iff' measurableSet_Ioi).mp hd
  have hgg := (ae_restrict_iff' measurableSet_Ioo).mp hgd
  have hgeq : ∀ᵐ s : ℝ ∂volume, s ∈ Icc a b → g s=R s := by
    have hna : ∀ᵐ s : ℝ ∂volume, s ≠ a := by simp [ae_iff]
    have hnb : ∀ᵐ s : ℝ ∂volume, s ≠ b := by simp [ae_iff]
    filter_upwards [hdg,hgg,hna,hnb] with s hds hgs hsa hsb hs
    exact (hgs ⟨lt_of_le_of_ne hs.1 hsa.symm,lt_of_le_of_ne hs.2 hsb⟩).unique
      (hds (ha.trans_le hs.1))
  have hnew : ∀ x ∈ Icc a b, w x=w a+∫ s : ℝ in a..x, R s := by
    intro x hx
    rw [hrep x hx]
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hgeq] with s hgs hs
    rw [uIoc_of_le hx.1] at hs
    exact hgs ⟨hs.1.le,hs.2.trans hx.2⟩
  have hi : IntervalIntegrable R volume a t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hat.le]
    exact hRc.mono (Icc_subset_Icc_right htb.le)
  have hRt := hRc.continuousAt (Icc_mem_nhds hat htb)
  have hRm : StronglyMeasurableAtFilter R (nhds t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hRc.mono Ioo_subset_Icc_self) t ⟨hat,htb⟩
  apply ((intervalIntegral.integral_hasDerivAt_right hi hRm hRt).const_add (w a)).congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hat htb] with x hx
  exact hnew x hx

theorem gamma_hazard_local_ac_derivative (Q : ℝ → ℝ)
    (hQ : LocallyIntegralAbsolutelyContinuousPositive Q)
    (hd : ∀ᵐ x ∂volume.restrict (Ioi (0:ℝ)), HasDerivAt Q (-gammaHazard x*Q x) x) :
    ∀ x>0, HasDerivAt Q (-gammaHazard x*Q x) x := by
  apply local_ac_continuous_rhs_hasDerivAt Q _ hQ
  have hc : ContinuousOn Q (Ioi 0) := fun x hx =>
    (local_integral_ac_continuousAt Q hQ hx).continuousWithinAt
  exact (((continuousOn_id.div (continuousOn_const.add continuousOn_id)
    (fun x hx => by change 0<x at hx; dsimp; linarith)).neg).mul hc)
  exact hd

/-- The survival anchor is used only at the endpoint; no derivative at zero
or everywhere differentiability is assumed. -/
theorem gamma_hazard_unique_local_ac (Q : ℝ → ℝ)
    (hQ : LocallyIntegralAbsolutelyContinuousPositive Q)
    (hc0 : ContinuousWithinAt Q (Ici 0) 0) (h0 : Q 0=1)
    (hd : ∀ᵐ x ∂volume.restrict (Ioi (0:ℝ)), HasDerivAt Q (-gammaHazard x*Q x) x) :
    ∀ x≥0, Q x=gammaSurvival x := by
  have hderiv := gamma_hazard_local_ac_derivative Q hQ hd
  let G : ℝ → ℝ := fun x => Real.exp x*Q x/(1+x)
  have hG : ∀ x>0, HasDerivAt G 0 x := by
    intro x hx
    convert ((Real.hasDerivAt_exp x).mul (hderiv x hx)).div
      ((hasDerivAt_id x).const_add 1) (by linarith : 1+x ≠ 0) using 1
    simp only [gammaHazard]
    field_simp
    ring
  let C := G 1
  have hC : ∀ x>0, G x=C := equal_of_equal_derivatives G (fun _ => C)
    (fun x hx => (hG x hx).differentiableAt) (fun _ _ => differentiableAt_const _)
    (by intro x hx; rw [(hG x hx).deriv]; simp) rfl
  have hGc : ContinuousWithinAt G (Ici 0) 0 :=
    ((Real.continuous_exp.continuousWithinAt.mul hc0).div
      (continuousWithinAt_const.add continuousWithinAt_id) (by norm_num))
  have hGlim : Tendsto G (𝓝[>] (0:ℝ)) (𝓝 (G 0)) := hGc.mono Ioi_subset_Ici_self
  have hconst : Tendsto G (𝓝[>] (0:ℝ)) (𝓝 C) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hC x hx).symm
  have hC1 : C=1 := by
    have hh := tendsto_nhds_unique hconst hGlim
    simpa [G,h0] using hh
  intro x hx
  by_cases hx0 : x=0
  · simp [hx0,h0,gamma_survival_anchor]
  · have hh := hC x (lt_of_le_of_ne hx (Ne.symm hx0))
    rw [hC1] at hh
    dsimp [G] at hh
    have he := (div_eq_one_iff_eq (by linarith : 1+x ≠ 0)).mp hh
    unfold gammaSurvival
    rw [Real.exp_neg]
    apply (eq_mul_inv_iff_mul_eq₀ (Real.exp_ne_zero x)).mpr
    simpa only [mul_comm] using he

/-- Actual probability measures, rather than only candidate scalar tails,
are identified by the local-AC hazard equation and the survival anchor. -/
theorem gamma_probability_local_ac_hazard_inverse (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hQ : LocallyIntegralAbsolutelyContinuousPositive (lifetimeSurvival μ))
    (h0 : lifetimeSurvival μ 0=1)
    (hd : ∀ᵐ x ∂volume.restrict (Ioi (0:ℝ)),
      HasDerivAt (lifetimeSurvival μ) (-gammaHazard x*lifetimeSurvival μ x) x) :
    μ=gammaProbability := by
  have hc : ContinuousWithinAt (lifetimeSurvival μ) (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    exact lifetime_survival_right_continuous μ 0
  have hs := gamma_hazard_unique_local_ac (lifetimeSurvival μ) hQ hc h0 hd
  apply Measure.eq_of_cdf
  ext x
  have he : lifetimeSurvival μ x=lifetimeSurvival gammaProbability x := by
    by_cases hx : 0≤x
    · rw [hs x hx,lifetimeSurvival,gamma_probability_tail x hx,ENNReal.toReal_ofReal]
      exact (gamma_survival_positive hx).le
    · have hμ0 : μ (Ioi 0)=1 := by
        apply (ENNReal.toReal_eq_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mp
        simpa [lifetimeSurvival] using h0
      have hγ0 : gammaProbability (Ioi 0)=1 := by
        simpa [gammaSurvival] using gamma_probability_tail 0 (le_refl 0)
      have hμx : μ (Ioi x)=1 := le_antisymm prob_le_one (by
        rw [← hμ0]; exact measure_mono (Ioi_subset_Ioi (le_of_not_ge hx)))
      have hγx : gammaProbability (Ioi x)=1 := le_antisymm prob_le_one (by
        rw [← hγ0]; exact measure_mono (Ioi_subset_Ioi (le_of_not_ge hx)))
      simp [lifetimeSurvival,hμx,hγx]
  rw [lifetime_survival_eq_one_sub_cdf,lifetime_survival_eq_one_sub_cdf] at he
  linarith

/-- The marked logistic dynamics recovers the hazard in its original lifetime
coordinate; the native probability conclusion uses the preceding a.e. bridge. -/
theorem gamma_probability_local_ac_logistic_inverse (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : ℝ → ℝ) (hv : ∀ u, HasDerivAt v (v u*(1-v u)) u) (hv0 : v 0=1/2)
    (hQ : LocallyIntegralAbsolutelyContinuousPositive (lifetimeSurvival μ))
    (h0 : lifetimeSurvival μ 0=1)
    (hd : ∀ᵐ x ∂volume.restrict (Ioi (0:ℝ)),
      HasDerivAt (lifetimeSurvival μ) (-v (Real.log x)*lifetimeSurvival μ x) x) :
    μ=gammaProbability := by
  have he := logistic_hazard_unique v hv hv0
  apply gamma_probability_local_ac_hazard_inverse μ hQ h0
  filter_upwards [hd,ae_restrict_mem measurableSet_Ioi] with x hx hxp
  simpa only [he,logistic_hazard_coordinate,Real.exp_log hxp] using hx

end
end Sigma
