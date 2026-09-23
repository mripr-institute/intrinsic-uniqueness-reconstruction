import SigmaOpMixing
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.MeasureCompProd

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal ProbabilityTheory

def refreshWeight (t : ℝ≥0) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(t : ℝ)))
def refreshComplement (t : ℝ≥0) : ℝ≥0∞ := ENNReal.ofReal (1 - Real.exp (-(t : ℝ)))

theorem refresh_exp_le_one (t : ℝ≥0) : Real.exp (-(t : ℝ)) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr t.property

theorem refresh_weights_sum (t : ℝ≥0) : refreshWeight t + refreshComplement t = 1 := by
  rw [refreshWeight, refreshComplement, ← ENNReal.ofReal_add (Real.exp_pos _).le
    (sub_nonneg.mpr (refresh_exp_le_one t))]
  simp

theorem refresh_weight_add (s t : ℝ≥0) :
    refreshWeight (s+t) = refreshWeight s * refreshWeight t := by
  simp only [refreshWeight, NNReal.coe_add, neg_add_rev, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [mul_comm]

theorem refresh_complement_add (s t : ℝ≥0) :
    refreshComplement (s+t) = refreshWeight s * refreshComplement t + refreshComplement s := by
  rw [refreshComplement, refreshWeight, refreshComplement, refreshComplement,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (refresh_exp_le_one t)))
      (sub_nonneg.mpr (refresh_exp_le_one s))]
  congr 1
  rw [NNReal.coe_add, neg_add, Real.exp_add]
  ring

/-- A native conservative refresh kernel: retain the current state or redraw
from Gamma. The time parameter is nonnegative; no process or semigroup law is
assumed in the definition. -/
def gammaRefreshKernel (t : ℝ≥0) : Kernel ℝ ℝ where
  toFun x := refreshWeight t • Measure.dirac x + refreshComplement t • gammaProbability
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro E hE
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact (measurable_const.mul ((Measure.measurable_coe hE).comp Measure.measurable_dirac)).add measurable_const

theorem gamma_refresh_apply (t : ℝ≥0) (x : ℝ) (E : Set ℝ) :
    gammaRefreshKernel t x E = refreshWeight t * Measure.dirac x E +
      refreshComplement t * gammaProbability E := by
  simp [gammaRefreshKernel, Measure.smul_apply, smul_eq_mul]

instance gamma_refresh_markov (t : ℝ≥0) : IsMarkovKernel (gammaRefreshKernel t) where
  isProbabilityMeasure x := ⟨by simp [gamma_refresh_apply, refresh_weights_sum]⟩

theorem gamma_refresh_zero : gammaRefreshKernel 0 = Kernel.id := by
  ext x E hE
  simp [gamma_refresh_apply, refreshWeight, refreshComplement, Kernel.id_apply]

theorem gamma_refresh_integral (t : ℝ≥0) (E : Set ℝ) (hE : MeasurableSet E) :
    (∫⁻ x, gammaRefreshKernel t x E ∂gammaProbability) = gammaProbability E := by
  simp only [gamma_refresh_apply]
  have hdmeas : Measurable (fun x : ℝ => Measure.dirac x E) :=
    (Measure.measurable_coe hE).comp Measure.measurable_dirac
  have hmeas : Measurable (fun x : ℝ => refreshWeight t * Measure.dirac x E) :=
    measurable_const.mul hdmeas
  rw [lintegral_add_left hmeas,
    lintegral_const_mul _ hdmeas,
    lintegral_const, measure_univ, mul_one]
  have hd : (∫⁻ x, Measure.dirac x E ∂gammaProbability) = gammaProbability E := by
    simp_rw [Measure.dirac_apply' _ hE]
    exact lintegral_indicator_one hE
  rw [hd, ← add_mul, refresh_weights_sum, one_mul]

theorem gamma_refresh_invariant (t : ℝ≥0) :
    (gammaRefreshKernel t).Invariant gammaProbability := by
  apply Measure.ext
  intro E hE
  rw [Measure.bind_apply hE (Kernel.measurable _)]
  exact gamma_refresh_integral t E hE

theorem gamma_refresh_semigroup (s t : ℝ≥0) :
    gammaRefreshKernel t ∘ₖ gammaRefreshKernel s = gammaRefreshKernel (s+t) := by
  ext x E hE
  rw [Kernel.comp_apply' _ _ _ hE]
  change (∫⁻ y, gammaRefreshKernel t y E ∂(refreshWeight s • Measure.dirac x +
    refreshComplement s • gammaProbability)) = _
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac' _ (Kernel.measurable_coe _ hE), gamma_refresh_integral t E hE,
    gamma_refresh_apply, gamma_refresh_apply, refresh_weight_add, refresh_complement_add]
  ring

theorem gamma_refresh_joint (t : ℝ≥0) :
    gammaProbability ⊗ₘ gammaRefreshKernel t =
      refreshWeight t • gammaProbability.map (fun x : ℝ => (x,x)) +
      refreshComplement t • gammaProbability.prod gammaProbability := by
  ext E hE
  have hdiag : Measurable (fun x : ℝ => (x,x)) := measurable_id.prod_mk measurable_id
  rw [Measure.compProd_apply hE, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply hdiag hE, Measure.prod_apply hE]
  let D : Set ℝ := (fun x : ℝ => (x,x)) ⁻¹' E
  have hD : MeasurableSet D := hE.preimage (measurable_id.prod_mk measurable_id)
  have hd : ∀ x : ℝ, Measure.dirac x ((Prod.mk x) ⁻¹' E) = D.indicator (fun _ => 1) x := by
    intro x
    rw [Measure.dirac_apply' _ (hE.preimage measurable_prod_mk_left)]
    rfl
  simp only [gamma_refresh_apply, hd, smul_eq_mul]
  have hi : Measurable (fun x : ℝ => refreshWeight t * D.indicator (fun _ => (1 : ℝ≥0∞)) x) :=
    measurable_const.mul (measurable_const.indicator hD)
  have hdi : (∫⁻ x : ℝ, D.indicator (fun _ => (1 : ℝ≥0∞)) x ∂gammaProbability) = gammaProbability D := by
    simpa using (lintegral_indicator_one (μ := gammaProbability) hD)
  have hsec : Measurable (fun x : ℝ => gammaProbability ((Prod.mk x) ⁻¹' E)) :=
    measurable_measure_prod_mk_left hE
  rw [lintegral_add_left hi, lintegral_const_mul _ (measurable_const.indicator hD),
    hdi, lintegral_const_mul _ hsec]

/-- Detailed balance is equality of actual joint measures under swapping the
two states, not just a scalar invariant-integral equation. -/
theorem gamma_refresh_detailed_balance (t : ℝ≥0) :
    (gammaProbability ⊗ₘ gammaRefreshKernel t).map Prod.swap =
      gammaProbability ⊗ₘ gammaRefreshKernel t := by
  have hdiag : Measurable (fun x : ℝ => (x,x)) := measurable_id.prod_mk measurable_id
  rw [gamma_refresh_joint, Measure.map_add _ _ measurable_swap, Measure.map_smul,
    Measure.map_smul, Measure.map_map measurable_swap hdiag,
    Measure.prod_swap]
  rfl

theorem gamma_refresh_preserves_positive_ray (t : ℝ≥0) (x : ℝ) (hx : 0 < x) :
    gammaRefreshKernel t x (Ioi 0) = 1 := by
  have hγ : gammaProbability (Ioi 0) = 1 := by
    have hae := operator_integer_samples_ae_pos gammaProbability operator_gamma_probability_integer_samples
    exact (measure_congr (hae.mono fun _ ht => propext (iff_true_intro ht))).trans measure_univ
  rw [gamma_refresh_apply, hγ, Measure.dirac_apply_of_mem (show x ∈ Ioi 0 from hx)]
  simpa using refresh_weights_sum t

theorem gamma_refresh_singleton_time_injective (x : ℝ) :
    Function.Injective (fun t => gammaRefreshKernel t x {x}) := by
  intro s t h
  simp [gamma_refresh_apply, gamma_probability_no_atom, Measure.dirac_apply'] at h
  have he := congrArg ENNReal.toReal h
  simp only [refreshWeight, ENNReal.toReal_ofReal (Real.exp_pos _).le] at he
  exact NNReal.coe_injective (neg_injective (Real.exp_injective he))

theorem gamma_refresh_time_injective : Function.Injective gammaRefreshKernel := by
  intro s t h
  exact gamma_refresh_singleton_time_injective 1
    (congrArg (fun κ : Kernel ℝ ℝ => κ 1 {1}) h)

def gammaRefreshDynamics (c t : ℝ≥0) : Kernel ℝ ℝ := gammaRefreshKernel (c*t)

theorem gamma_refresh_dynamics_time_rescaling (c t : ℝ≥0) :
    gammaRefreshDynamics c t = gammaRefreshDynamics 1 (c*t) := by simp [gammaRefreshDynamics]

theorem gamma_refresh_dynamics_semigroup (c s t : ℝ≥0) :
    gammaRefreshDynamics c t ∘ₖ gammaRefreshDynamics c s = gammaRefreshDynamics c (s+t) := by
  simpa only [gammaRefreshDynamics, mul_add] using gamma_refresh_semigroup (c*s) (c*t)

theorem gamma_refresh_different_rates (c d : ℝ≥0) (hcd : c ≠ d) :
    gammaRefreshDynamics c 1 ≠ gammaRefreshDynamics d 1 := by
  simpa only [gammaRefreshDynamics, mul_one] using gamma_refresh_time_injective.ne hcd

/-- Different rates are distinguishable at every state, in particular at
every positive state of the paper's state space, not only at a null extension. -/
theorem gamma_refresh_different_rates_at_state (c d : ℝ≥0) (hcd : c ≠ d) (x : ℝ) :
    gammaRefreshDynamics c 1 x {x} ≠ gammaRefreshDynamics d 1 x {x} := by
  simpa only [gammaRefreshDynamics, mul_one] using
    (gamma_refresh_singleton_time_injective x).ne hcd

/-- The usual conservative reversible kernel-semigroup properties, with actual
Gamma invariance, actual joint-measure detailed balance and positive-ray
preservation. No pathwise or strong-operator continuity assertion is included. -/
structure IsGammaReversibleKernelSemigroup (K : ℝ≥0 → Kernel ℝ ℝ) : Prop where
  markov : ∀ t, IsMarkovKernel (K t)
  at_zero : K 0 = Kernel.id
  compose : ∀ s t, K t ∘ₖ K s = K (s+t)
  invariant : ∀ t, (K t).Invariant gammaProbability
  detailed_balance : ∀ t, (gammaProbability ⊗ₘ K t).map Prod.swap = gammaProbability ⊗ₘ K t
  positive_ray : ∀ t x, 0 < x → K t x (Ioi 0) = 1

theorem gamma_refresh_reversible_semigroup (c : ℝ≥0) :
    IsGammaReversibleKernelSemigroup (gammaRefreshDynamics c) where
  markov t := gamma_refresh_markov (c*t)
  at_zero := by simpa [gammaRefreshDynamics] using gamma_refresh_zero
  compose := gamma_refresh_dynamics_semigroup c
  invariant t := gamma_refresh_invariant (c*t)
  detailed_balance t := gamma_refresh_detailed_balance (c*t)
  positive_ray t x hx := gamma_refresh_preserves_positive_ray (c*t) x hx

/-- The same actual invariant law admits genuinely different reversible
conservative dynamics, and a change of time scale is explicitly witnessed. -/
theorem gamma_invariant_does_not_identify_reversible_dynamics :
    ∃ K L : ℝ≥0 → Kernel ℝ ℝ,
      IsGammaReversibleKernelSemigroup K ∧ IsGammaReversibleKernelSemigroup L ∧
      K 1 ≠ L 1 ∧ (∀ x : ℝ, 0 < x → K 1 x {x} ≠ L 1 x {x}) ∧
      ∀ t, L t = K (2*t) := by
  refine ⟨gammaRefreshDynamics 1, gammaRefreshDynamics 2,
    gamma_refresh_reversible_semigroup 1, gamma_refresh_reversible_semigroup 2,
    gamma_refresh_different_rates 1 2 (by norm_num), ?_, ?_⟩
  · intro x _
    exact gamma_refresh_different_rates_at_state 1 2 (by norm_num) x
  intro t
  exact gamma_refresh_dynamics_time_rescaling 2 t

end
end Sigma
