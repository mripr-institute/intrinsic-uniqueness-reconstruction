import SigmaProbSurvivalAC
import SigmaProbDeficitCDF

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal

def singularSurvival (C : ℝ → ℝ) (x : ℝ) : ℝ :=
  gammaSurvival (max x 0) * Real.exp (-C x)

theorem singular_survival_continuous (C : ℝ → ℝ) (hc : Continuous C) :
    Continuous (singularSurvival C) := by
  have hg : Continuous gammaSurvival := continuous_iff_continuousAt.mpr
    (fun x => (gamma_survival_derivative x).continuousAt)
  exact (hg.comp (continuous_id.max continuous_const)).mul hc.neg.rexp

theorem singular_survival_positive (C : ℝ → ℝ) (x : ℝ) :
    0 < singularSurvival C x :=
  mul_pos (gamma_survival_positive (le_max_right _ _)) (Real.exp_pos _)

theorem gamma_survival_antitone_positive : AntitoneOn gammaSurvival (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact (continuous_iff_continuousAt.mpr
      (fun x => (gamma_survival_derivative x).continuousAt)).continuousOn
  · exact fun x _ => (gamma_survival_derivative x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(gamma_survival_derivative x).deriv]
    have hx0 : 0 ≤ x := interior_subset hx
    unfold SigmaPresentations.density
    exact neg_nonpos.mpr (mul_nonneg hx0 (Real.exp_pos _).le)

theorem singular_survival_antitone (C : ℝ → ℝ) (hm : Monotone C) :
    Antitone (singularSurvival C) := by
  intro x y hxy
  apply mul_le_mul
  · exact gamma_survival_antitone_positive (le_max_right _ _) (le_max_right _ _)
      (max_le_max hxy le_rfl)
  · exact Real.exp_le_exp.mpr (neg_le_neg (hm hxy))
  · exact (Real.exp_pos _).le
  · exact (gamma_survival_positive (le_max_right _ _)).le

theorem singular_survival_left (C : ℝ → ℝ) (hl : ∀ x ≤ 1, C x = 0)
    {x : ℝ} (hx : x ≤ 0) : singularSurvival C x = 1 := by
  simp [singularSurvival, max_eq_right hx, hl x (hx.trans zero_le_one), gamma_survival_anchor]

theorem singular_survival_tendsto (C : ℝ → ℝ) (hr : ∀ x ≥ 2, C x = 1) :
    Tendsto (singularSurvival C) atTop (𝓝 0) := by
  have hlim := gamma_survival_tendsto.mul_const (Real.exp (-1))
  simp only [zero_mul] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  simp [singularSurvival, max_eq_left (show 0 ≤ x by linarith), hr x hx]

def singularSurvivalCDF (C : ℝ → ℝ) (hc : Continuous C) (hm : Monotone C) :
    StieltjesFunction where
  toFun x := 1-singularSurvival C x
  mono' := fun _ _ hxy => sub_le_sub_left (singular_survival_antitone C hm hxy) 1
  right_continuous' _ := ((continuous_const.sub
    (singular_survival_continuous C hc)).continuousAt).continuousWithinAt

theorem singular_survival_cdf_bot (C : ℝ → ℝ) (hc : Continuous C) (hm : Monotone C)
    (hl : ∀ x ≤ 1, C x = 0) :
    Tendsto (singularSurvivalCDF C hc hm) atBot (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
  change 0 = 1-singularSurvival C x
  rw [singular_survival_left C hl hx]
  ring

theorem singular_survival_cdf_top (C : ℝ → ℝ) (hc : Continuous C) (hm : Monotone C)
    (hr : ∀ x ≥ 2, C x = 1) :
    Tendsto (singularSurvivalCDF C hc hm) atTop (𝓝 1) := by
  simpa only [sub_zero] using (singular_survival_tendsto C hr).const_sub 1

theorem singular_survival_probability (C : ℝ → ℝ) (hc : Continuous C) (hm : Monotone C)
    (hl : ∀ x ≤ 1, C x = 0) (hr : ∀ x ≥ 2, C x = 1) :
    IsProbabilityMeasure (singularSurvivalCDF C hc hm).measure :=
  StieltjesFunction.isProbabilityMeasure _ (singular_survival_cdf_bot C hc hm hl)
    (singular_survival_cdf_top C hc hm hr)

theorem singular_survival_actual_tail (C : ℝ → ℝ) (hc : Continuous C) (hm : Monotone C)
    (hl : ∀ x ≤ 1, C x = 0) (hr : ∀ x ≥ 2, C x = 1) (x : ℝ) :
    ((singularSurvivalCDF C hc hm).measure (Ioi x)).toReal = singularSurvival C x := by
  letI := singular_survival_probability C hc hm hl hr
  have hbound : singularSurvival C x ≤ 1 := by
    by_cases hx : x ≤ 0
    · exact (singular_survival_left C hl hx).le
    · have h := singular_survival_antitone C hm (le_of_not_ge hx)
      rwa [singular_survival_left C hl le_rfl] at h
  rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
    StieltjesFunction.measure_Iic _ (singular_survival_cdf_bot C hc hm hl)]
  change (1-ENNReal.ofReal ((1-singularSurvival C x)-0)).toReal = _
  rw [sub_zero, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (sub_nonneg.mpr hbound)]
  simpa using ENNReal.toReal_ofReal (singular_survival_positive C x).le

theorem singular_survival_ae_hazard (C : ℝ → ℝ)
    (hd : ∀ᵐ x ∂volume, HasDerivAt C 0 x) :
    ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      HasDerivAt (singularSurvival C) (-gammaHazard x*singularSurvival C x) x := by
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Ioi] with x hx hx0
  have he := (gamma_survival_derivative x).mul hx.neg.exp
  have hshape : -SigmaPresentations.density x * Real.exp (-C x) +
      gammaSurvival x * (Real.exp (-C x) * -0) =
        -gammaHazard x * singularSurvival C x := by
    have hratio := gamma_hazard_ratio x hx0.le
    have hden := (gamma_survival_positive hx0.le).ne'
    have hp : SigmaPresentations.density x = gammaHazard x * gammaSurvival x :=
      (div_eq_iff hden).mp hratio
    rw [hp]
    simp [singularSurvival, max_eq_left hx0.le]
    ring
  rw [hshape] at he
  apply he.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx0] with y hy
  simp [singularSurvival, max_eq_left hy.le]

theorem singular_survival_ae_log_hazard (C : ℝ → ℝ)
    (hd : ∀ᵐ x ∂volume, HasDerivAt C 0 x) :
    ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      HasDerivAt (fun t => Real.log (singularSurvival C t)) (-gammaHazard x) x := by
  filter_upwards [singular_survival_ae_hazard C hd] with x hx
  have h := hx.log (singular_survival_positive C x).ne'
  simpa only [mul_div_cancel_right₀ _ (singular_survival_positive C x).ne'] using h

theorem singular_survival_strict_antitone (C : ℝ → ℝ) (hm : Monotone C) :
    StrictAntiOn (singularSurvival C) (Ici 0) := by
  have hg : StrictAntiOn gammaSurvival (Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    · exact (continuous_iff_continuousAt.mpr
        (fun x => (gamma_survival_derivative x).continuousAt)).continuousOn
    · intro x hx
      rw [(gamma_survival_derivative x).deriv]
      have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
      exact neg_neg_of_pos (SigmaPresentations.density_pos hx0)
  intro x hx y hy hxy
  simp only [singularSurvival, max_eq_left hx, max_eq_left hy]
  exact mul_lt_mul (hg hx hy hxy) (Real.exp_le_exp.mpr (neg_le_neg (hm hxy.le)))
    (Real.exp_pos _) (gamma_survival_positive hx).le

theorem singular_survival_noncanonical (C : ℝ → ℝ) (hr : ∀ x ≥ 2, C x = 1) :
    singularSurvival C 2 ≠ gammaSurvival 2 := by
  have hp : 0 < gammaSurvival 2 := gamma_survival_positive (by norm_num)
  have he : Real.exp (-1 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hlt : singularSurvival C 2 < gammaSurvival 2 := by
    simpa [singularSurvival, hr 2 le_rfl] using mul_lt_mul_of_pos_left he hp
  exact hlt.ne

theorem singular_survival_not_local_ac (C : ℝ → ℝ) (hc : Continuous C)
    (hl : ∀ x ≤ 1, C x = 0) (hr : ∀ x ≥ 2, C x = 1)
    (hd : ∀ᵐ x ∂volume, HasDerivAt C 0 x) :
    ¬ LocallyIntegralAbsolutelyContinuousPositive (singularSurvival C) := by
  intro hac
  have he := gamma_hazard_unique_local_ac (singularSurvival C) hac
    (singular_survival_continuous C hc).continuousAt.continuousWithinAt
    (singular_survival_left C hl le_rfl) (singular_survival_ae_hazard C hd) 2 (by norm_num)
  exact singular_survival_noncanonical C hr he

/-- The singular perturbation is the actual survival of an atomless probability,
not merely a solution of a scalar differential equation. -/
theorem singular_survival_native_counterexample (C : ℝ → ℝ)
    (hc : Continuous C) (hm : Monotone C)
    (hl : ∀ x ≤ 1, C x = 0) (hr : ∀ x ≥ 2, C x = 1)
    (hd : ∀ᵐ x ∂volume, HasDerivAt C 0 x) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ NoAtoms μ ∧
      (∀ᵐ t ∂μ, 0 < t) ∧ Continuous (lifetimeSurvival μ) ∧
      Antitone (lifetimeSurvival μ) ∧
      StrictAntiOn (lifetimeSurvival μ) (Ici 0) ∧
      (∀ x : ℝ, 0 < lifetimeSurvival μ x) ∧ lifetimeSurvival μ 0 = 1 ∧
      Tendsto (lifetimeSurvival μ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
        HasDerivAt (lifetimeSurvival μ) (-gammaHazard x*lifetimeSurvival μ x) x) ∧
      (∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
        HasDerivAt (fun t => Real.log (lifetimeSurvival μ t)) (-gammaHazard x) x) ∧
      μ ≠ gammaProbability ∧
      ¬ LocallyIntegralAbsolutelyContinuousPositive (lifetimeSurvival μ) := by
  let μ := (singularSurvivalCDF C hc hm).measure
  haveI : IsProbabilityMeasure μ := singular_survival_probability C hc hm hl hr
  have htail : lifetimeSurvival μ = singularSurvival C := by
    funext x
    exact singular_survival_actual_tail C hc hm hl hr x
  have hno : NoAtoms μ := by
    constructor
    intro x
    change (singularSurvivalCDF C hc hm).measure {x} = 0
    rw [StieltjesFunction.measure_singleton,
      (singularSurvivalCDF C hc hm).mono.continuousWithinAt_Iio_iff_leftLim_eq.mp
        ((continuous_const.sub (singular_survival_continuous C hc)).continuousAt.continuousWithinAt)]
    simp
  have hpos : ∀ᵐ t ∂μ, 0 < t := by
    rw [ae_iff]
    simp only [not_lt]
    change μ (Iic 0) = 0
    rw [StieltjesFunction.measure_Iic _ (singular_survival_cdf_bot C hc hm hl)]
    change ENNReal.ofReal ((1-singularSurvival C 0)-0) = 0
    rw [singular_survival_left C hl le_rfl]
    norm_num
  refine ⟨μ, inferInstance, hno, hpos, ?_⟩
  rw [htail]
  refine ⟨singular_survival_continuous C hc, singular_survival_antitone C hm,
    singular_survival_strict_antitone C hm,
    singular_survival_positive C, singular_survival_left C hl le_rfl,
    singular_survival_tendsto C hr, singular_survival_ae_hazard C hd,
    singular_survival_ae_log_hazard C hd, ?_,
    singular_survival_not_local_ac C hc hl hr hd⟩
  intro he
  have ht := congrFun htail 2
  rw [he] at ht
  change (gammaProbability (Ioi 2)).toReal = singularSurvival C 2 at ht
  rw [gamma_probability_tail 2 (by norm_num),
    ENNReal.toReal_ofReal (gamma_survival_positive (by norm_num : (0 : ℝ) ≤ 2)).le] at ht
  exact singular_survival_noncanonical C hr ht.symm

end
end Sigma
