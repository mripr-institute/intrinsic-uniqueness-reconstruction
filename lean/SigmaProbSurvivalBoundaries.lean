import SigmaProbSurvival
import SigmaProbDeficitCDF
import SigmaProbCanonicalPair
import SigmaProbHaar

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The positive-argument survival and density of the atom-at-zero mixture. -/
def mixedGammaSurvival (r x : ℝ) : ℝ := (1-r) * gammaSurvival x
def mixedGammaDensity (r x : ℝ) : ℝ := (1-r) * SigmaPresentations.density x

theorem mixed_gamma_survival_anchor (r : ℝ) :
    mixedGammaSurvival r 0 = 1-r := by
  simp [mixedGammaSurvival, gamma_survival_anchor]

theorem mixed_gamma_survival_positive (r : ℝ) (hr1 : r < 1)
    {x : ℝ} (hx : 0 ≤ x) : 0 < mixedGammaSurvival r x := by
  unfold mixedGammaSurvival
  have hsub : 0 < 1-r := by nlinarith
  exact mul_pos hsub (gamma_survival_positive hx)

theorem mixed_gamma_hazard (r : ℝ) (hr1 : r < 1)
    {x : ℝ} (hx : 0 ≤ x) :
    mixedGammaDensity r x / mixedGammaSurvival r x = gammaHazard x := by
  unfold mixedGammaDensity mixedGammaSurvival
  have hsub : 0 < 1-r := by nlinarith
  rw [mul_div_mul_left _ _ (ne_of_gt hsub)]
  exact gamma_hazard_ratio x hx

theorem logarithmic_gamma_hazard (u : ℝ) :
    Real.exp u * gammaHazard (Real.exp u) =
      Real.exp (2*u) / (1 + Real.exp u) := by
  unfold gammaHazard
  field_simp
  rw [← Real.exp_add]
  congr 1
  ring

/-- The actual atom-at-zero mixture used in the survival-anchor boundary. -/
def atomGammaMixture (r : ℝ) : Measure ℝ :=
  ENNReal.ofReal r • Measure.dirac 0 + ENNReal.ofReal (1-r) • gammaProbability

theorem atom_gamma_mixture_probability (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    IsProbabilityMeasure (atomGammaMixture r) := by
  constructor
  have he : ENNReal.ofReal r + ENNReal.ofReal (1-r) = 1 := by
    rw [← ENNReal.ofReal_add hr0 (by linarith)]
    norm_num
  simpa [atomGammaMixture] using he

theorem atom_gamma_mixture_nonnegative (r : ℝ) :
    ∀ᵐ t ∂atomGammaMixture r, 0 ≤ t := by
  rw [ae_iff]
  simp only [not_le]
  change atomGammaMixture r (Iio 0) = 0
  simp [atomGammaMixture, gamma_probability_negative_ray]

theorem atom_gamma_mixture_atom (r : ℝ) :
    atomGammaMixture r {0} = ENNReal.ofReal r := by
  simp [atomGammaMixture, gamma_probability_no_atom]

theorem atom_gamma_mixture_tail (r x : ℝ) (hr : r ≤ 1) (hx : 0 ≤ x) :
    atomGammaMixture r (Ioi x) = ENNReal.ofReal (mixedGammaSurvival r x) := by
  simp only [atomGammaMixture, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ measurableSet_Ioi, mem_Ioi, not_lt.mpr hx,
    indicator_of_not_mem (show (0:ℝ) ∉ Ioi x from not_lt.mpr hx),
    if_false, mul_zero, zero_add, gamma_probability_tail x hx]
  exact (ENNReal.ofReal_mul (by linarith : 0 ≤ 1-r)).symm

theorem atom_gamma_mixture_tail_real (r x : ℝ) (hr : r ≤ 1) (hx : 0 ≤ x) :
    (atomGammaMixture r (Ioi x)).toReal = mixedGammaSurvival r x := by
  rw [atom_gamma_mixture_tail r x hr hx, ENNReal.toReal_ofReal]
  exact mul_nonneg (by linarith) (gamma_survival_positive hx).le

/-- On the open positive ray the mixture has precisely the scaled Gamma density. -/
theorem atom_gamma_mixture_positive_density (r : ℝ) (hr : r ≤ 1) :
    (atomGammaMixture r).restrict (Ioi 0) =
      (volume.restrict (Ioi 0)).withDensity
        (fun t => ENNReal.ofReal (mixedGammaDensity r t)) := by
  have hg : gammaProbability.restrict (Ioi 0) = gammaProbability := by
    apply Measure.restrict_eq_self_of_ae_mem
    exact operator_integer_samples_ae_pos gammaProbability operator_gamma_probability_integer_samples
  have hd : (Measure.dirac (0:ℝ)).restrict (Ioi 0) = 0 := by simp
  rw [atomGammaMixture, Measure.restrict_add, Measure.restrict_smul,
    Measure.restrict_smul, hd, hg, smul_zero, zero_add,
    ← canonical_linked_density_measure, ← withDensity_smul]
  · apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Pi.smul_apply, smul_eq_mul, Function.comp_def, intrinsic_linked_density t ht,
      mixedGammaDensity]
    exact (ENNReal.ofReal_mul (by linarith : 0 ≤ 1-r)).symm
  · exact deficit_weight_measurable.comp intrinsic_potential_measurable

theorem mixed_gamma_survival_derivative (r x : ℝ) :
    HasDerivAt (mixedGammaSurvival r) (-mixedGammaDensity r x) x := by
  simpa only [mixedGammaSurvival, mixedGammaDensity, mul_neg] using
    (gamma_survival_derivative x).const_mul (1-r)

theorem atom_gamma_mixture_tail_derivative (r x : ℝ) (hr : r < 1) (hx : 0 < x) :
    HasDerivAt (fun t => (atomGammaMixture r (Ioi t)).toReal)
      (-mixedGammaDensity r x) x := by
  apply (mixed_gamma_survival_derivative r x).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with t ht
  exact atom_gamma_mixture_tail_real r t hr.le ht.le

/-- This uses the actual tail of a probability, with its density verified above. -/
theorem gamma_hazard_anchor_counterexample (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    IsProbabilityMeasure (atomGammaMixture r) ∧
    (∀ᵐ t ∂atomGammaMixture r, 0 ≤ t) ∧
    atomGammaMixture r ≠ gammaProbability ∧
    (atomGammaMixture r (Ioi 0)).toReal = 1-r ∧
    (atomGammaMixture r (Ioi 0)).toReal ≠ 1 ∧
    (∀ x > 0, 0 < (atomGammaMixture r (Ioi x)).toReal ∧
      HasDerivAt (fun t => (atomGammaMixture r (Ioi t)).toReal)
        (-gammaHazard x * (atomGammaMixture r (Ioi x)).toReal) x) := by
  refine ⟨atom_gamma_mixture_probability r hr0.le hr1.le,
    atom_gamma_mixture_nonnegative r, ?_, ?_, ?_, ?_⟩
  · intro he
    have hz := congrArg (fun μ : Measure ℝ => μ {0}) he
    dsimp only at hz
    rw [atom_gamma_mixture_atom, gamma_probability_no_atom] at hz
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr hr0)) hz
  · rw [atom_gamma_mixture_tail_real r 0 hr1.le le_rfl, mixed_gamma_survival_anchor]
  · rw [atom_gamma_mixture_tail_real r 0 hr1.le le_rfl, mixed_gamma_survival_anchor]
    linarith
  · intro x hx
    have hp := mixed_gamma_survival_positive r hr1 hx.le
    refine ⟨by rwa [atom_gamma_mixture_tail_real r x hr1.le hx.le], ?_⟩
    have he := (div_eq_iff hp.ne').mp (mixed_gamma_hazard r hr1 hx.le)
    convert atom_gamma_mixture_tail_derivative r x hr1 hx using 1
    rw [atom_gamma_mixture_tail_real r x hr1.le hx.le, he, neg_mul]

/-- The logarithm of an actual Gamma random variable. -/
def logGammaProbability : Measure ℝ := Measure.map Real.log gammaProbability
def logGammaDensity (u : ℝ) : ℝ := Real.exp u * SigmaPresentations.density (Real.exp u)

instance log_gamma_probability : IsProbabilityMeasure logGammaProbability :=
  isProbabilityMeasure_map Real.measurable_log.aemeasurable

theorem log_gamma_probability_density :
    logGammaProbability = volume.withDensity (fun u => ENNReal.ofReal (logGammaDensity u)) := by
  have hm : Measurable (fun u => ENNReal.ofReal (logGammaDensity u)) := by
    unfold logGammaDensity SigmaPresentations.density
    fun_prop
  have hg : gammaProbability = positiveHaar.withDensity
      ((fun u => ENNReal.ofReal (logGammaDensity u)) ∘ Real.log) := by
    rw [← positive_haar_recovers_gamma]
    unfold sizeBiasWeight
    rw [← withDensity_mul _
      (show Measurable (fun t => ENNReal.ofReal (SigmaPresentations.density t)) from by
        unfold SigmaPresentations.density; fun_prop)
      (show Measurable (fun t : ℝ => ENNReal.ofReal t) from measurable_id.ennreal_ofReal)]
    apply withDensity_congr_ae
    filter_upwards [positive_haar_positive] with t ht
    simp only [Pi.mul_apply, Function.comp_def, logGammaDensity, Real.exp_log ht, sizeBiasWeight]
    rw [ENNReal.ofReal_mul ht.le, mul_comm]
  rw [logGammaProbability, hg, ← map_with_linked_density _ _ Real.measurable_log _ hm,
    positive_haar_log]

theorem log_gamma_tail (u : ℝ) :
    logGammaProbability (Ioi u) = ENNReal.ofReal (gammaSurvival (Real.exp u)) := by
  rw [logGammaProbability, Measure.map_apply Real.measurable_log measurableSet_Ioi]
  have hp := operator_integer_samples_ae_pos gammaProbability operator_gamma_probability_integer_samples
  have he : Real.log ⁻¹' Ioi u =ᵐ[gammaProbability] Ioi (Real.exp u) := by
    filter_upwards [hp] with t ht
    exact propext (Real.lt_log_iff_exp_lt ht)
  rw [measure_congr he, gamma_probability_tail _ (Real.exp_pos _).le]

theorem log_gamma_tail_real (u : ℝ) :
    (logGammaProbability (Ioi u)).toReal = gammaSurvival (Real.exp u) := by
  rw [log_gamma_tail, ENNReal.toReal_ofReal (gamma_survival_positive (Real.exp_pos _).le).le]

theorem log_gamma_tail_derivative (u : ℝ) :
    HasDerivAt (fun x => (logGammaProbability (Ioi x)).toReal) (-logGammaDensity u) u := by
  simp only [log_gamma_tail_real]
  convert (gamma_survival_derivative (Real.exp u)).comp u (Real.hasDerivAt_exp u) using 1
  simp only [logGammaDensity]
  ring

theorem log_gamma_actual_hazard (u : ℝ) :
    logGammaDensity u / (logGammaProbability (Ioi u)).toReal =
      Real.exp (2*u) / (1 + Real.exp u) := by
  rw [log_gamma_tail_real, logGammaDensity, mul_div_assoc,
    gamma_hazard_ratio _ (Real.exp_pos _).le, logarithmic_gamma_hazard]

theorem log_gamma_hazard_ne_composition (u : ℝ) (hu : u ≠ 0) :
    logGammaDensity u / (logGammaProbability (Ioi u)).toReal ≠ logisticHazard u := by
  rw [log_gamma_tail_real, logGammaDensity, mul_div_assoc,
    gamma_hazard_ratio _ (Real.exp_pos _).le, ← logistic_hazard_coordinate]
  have hp : 0 < logisticHazard u := div_pos (Real.exp_pos _) (by positivity)
  intro he
  have he' : Real.exp u = 1 := mul_right_cancel₀ hp.ne' (by simpa using he)
  exact hu (Real.exp_injective (he'.trans Real.exp_zero.symm))

end
end Sigma
