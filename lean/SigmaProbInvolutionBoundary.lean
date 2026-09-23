import SigmaProbDeficitSmooth
import SigmaProbDeficitCDF
import SigmaProbEntropyCounterexample

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

def involutionBalanceDenominator : ℝ :=
  ∫ v : ℝ, 1-Real.exp (-v) ∂gammaDeficitProbability

def involutionBalanceNumerator : ℝ :=
  ∫ v : ℝ, Real.exp (-v)*(1-Real.exp (-v)) ∂gammaDeficitProbability

def involutionBalance : ℝ := involutionBalanceNumerator/involutionBalanceDenominator

theorem deficit_positive_ae : ∀ᵐ v ∂gammaDeficitProbability, 0 < v := by
  simpa only [ae_iff, not_lt, ← Set.mem_Iic, Set.setOf_mem_eq] using gamma_deficit_cdf_zero_at_zero

theorem deficit_exp_neg_integrable : Integrable (fun v : ℝ => Real.exp (-v)) gammaDeficitProbability := by
  simpa only [neg_one_mul] using gamma_deficit_exponential_integrable (-1) (by norm_num)

theorem deficit_exp_neg_square_integrable :
    Integrable (fun v : ℝ => (Real.exp (-v))^2) gammaDeficitProbability := by
  have he : (fun v : ℝ => (Real.exp (-v))^2) = fun v => Real.exp (-2*v) := by
    funext v
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  exact gamma_deficit_exponential_integrable (-2) (by norm_num)

theorem involution_balance_denominator_integrable :
    Integrable (fun v : ℝ => 1-Real.exp (-v)) gammaDeficitProbability :=
  (integrable_const 1).sub deficit_exp_neg_integrable

theorem involution_balance_numerator_integrable :
    Integrable (fun v : ℝ => Real.exp (-v)*(1-Real.exp (-v))) gammaDeficitProbability := by
  convert deficit_exp_neg_integrable.sub deficit_exp_neg_square_integrable using 1
  funext v
  dsimp only [Pi.sub_apply]
  ring

theorem probability_integral_pos_of_ae_pos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf : Integrable f μ) (hp : ∀ᵐ t ∂μ, 0 < f t) : 0 < ∫ t, f t ∂μ := by
  have hn : 0 ≤ᵐ[μ] f := hp.mono (fun _ h => h.le)
  apply lt_of_le_of_ne (integral_nonneg_of_ae hn)
  intro he
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn hf).mp he.symm
  obtain ⟨t,ht,ht0⟩ := (hp.and hz).exists
  exact ht.ne' ht0

theorem involution_balance_denominator_pos : 0 < involutionBalanceDenominator := by
  apply probability_integral_pos_of_ae_pos _ involution_balance_denominator_integrable
  filter_upwards [deficit_positive_ae] with v hv
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hv))

theorem involution_balance_numerator_pos : 0 < involutionBalanceNumerator := by
  apply probability_integral_pos_of_ae_pos _ involution_balance_numerator_integrable
  filter_upwards [deficit_positive_ae] with v hv
  exact mul_pos (Real.exp_pos _) (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hv)))

theorem involution_balance_numerator_lt : involutionBalanceNumerator < involutionBalanceDenominator := by
  have hi := involution_balance_denominator_integrable.sub involution_balance_numerator_integrable
  have hp : 0 < ∫ v : ℝ, (1-Real.exp (-v))-Real.exp (-v)*(1-Real.exp (-v)) ∂gammaDeficitProbability := by
    apply probability_integral_pos_of_ae_pos _ hi
    filter_upwards [deficit_positive_ae] with v hv
    change 0 < (1-Real.exp (-v))-Real.exp (-v)*(1-Real.exp (-v))
    have hz : 0 < 1-Real.exp (-v) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hv))
    nlinarith [sq_pos_of_pos hz]
  rw [integral_sub involution_balance_denominator_integrable involution_balance_numerator_integrable] at hp
  exact sub_pos.mp hp

theorem involution_balance_bounds : 0 < involutionBalance ∧ involutionBalance < 1 := by
  exact ⟨div_pos involution_balance_numerator_pos involution_balance_denominator_pos,
    (div_lt_one involution_balance_denominator_pos).mpr involution_balance_numerator_lt⟩

def involutionLevelPerturbation (v : ℝ) : ℝ :=
  (1-Real.exp (-v))*(Real.exp (-v)-involutionBalance)

theorem involution_level_perturbation_integrable : Integrable involutionLevelPerturbation gammaDeficitProbability := by
  convert involution_balance_numerator_integrable.sub
    (involution_balance_denominator_integrable.const_mul involutionBalance) using 1
  funext v
  dsimp only [involutionLevelPerturbation, Pi.sub_apply]
  ring

theorem involution_level_perturbation_mean_zero :
    (∫ v, involutionLevelPerturbation v ∂gammaDeficitProbability) = 0 := by
  have he : involutionLevelPerturbation = fun v => Real.exp (-v)*(1-Real.exp (-v))-
      involutionBalance*(1-Real.exp (-v)) := by
    funext v
    unfold involutionLevelPerturbation
    ring
  rw [he, integral_sub involution_balance_numerator_integrable
    (involution_balance_denominator_integrable.const_mul involutionBalance), integral_mul_left]
  change involutionBalanceNumerator-involutionBalance*involutionBalanceDenominator = 0
  rw [involutionBalance, div_mul_cancel₀ _ involution_balance_denominator_pos.ne', sub_self]

def involutionLevelWeight (v : ℝ) : ℝ := 1 + involutionLevelPerturbation v / 10

def involutionLevelMap (v : ℝ) : ℝ := v - Real.log (involutionLevelWeight v)

theorem involution_level_perturbation_bound {v : ℝ} (hv : 0 ≤ v) :
    |involutionLevelPerturbation v| ≤ 1 := by
  have hz := Real.exp_pos (-v)
  have hz1 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hv)
  have hc := involution_balance_bounds
  unfold involutionLevelPerturbation
  rw [abs_mul]
  have h1 : |1-Real.exp (-v)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have h2 : |Real.exp (-v)-involutionBalance| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  exact (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)).trans (by norm_num)

theorem involution_level_weight_bounds {v : ℝ} (hv : 0 ≤ v) :
    9/10 ≤ involutionLevelWeight v ∧ involutionLevelWeight v ≤ 11/10 := by
  have hb := abs_le.mp (involution_level_perturbation_bound hv)
  unfold involutionLevelWeight
  constructor <;> linarith

theorem involution_level_weight_pos {v : ℝ} (hv : 0 ≤ v) :
    0 < involutionLevelWeight v := lt_of_lt_of_le (by norm_num) (involution_level_weight_bounds hv).1

theorem involution_level_perturbation_continuous : Continuous involutionLevelPerturbation := by
  unfold involutionLevelPerturbation
  fun_prop

theorem involution_level_weight_continuous : Continuous involutionLevelWeight := by
  exact continuous_const.add (involution_level_perturbation_continuous.div_const 10)

theorem involution_level_perturbation_derivative (v : ℝ) :
    HasDerivAt involutionLevelPerturbation
      (2 * Real.exp (-v)^2 - (1+involutionBalance)*Real.exp (-v)) v := by
  have hz : HasDerivAt (fun v : ℝ => Real.exp (-v)) (-Real.exp (-v)) v := by
    convert (hasDerivAt_neg v).exp using 1
    simp
  convert (hz.const_sub 1).mul (hz.sub_const involutionBalance) using 1
  dsimp only [involutionLevelPerturbation]
  ring

theorem involution_level_map_derivative {v : ℝ} (hv : 0 ≤ v) :
    HasDerivAt involutionLevelMap
      (1 - ((2 * Real.exp (-v)^2 - (1+involutionBalance)*Real.exp (-v))/10) /
        involutionLevelWeight v) v := by
  exact (hasDerivAt_id v).sub
    (((involution_level_perturbation_derivative v).div_const 10).const_add 1 |>.log
      (involution_level_weight_pos hv).ne')

theorem involution_level_map_derivative_pos {v : ℝ} (hv : 0 ≤ v) :
    0 < 1 - ((2 * Real.exp (-v)^2 - (1+involutionBalance)*Real.exp (-v))/10) /
        involutionLevelWeight v := by
  have hz := Real.exp_pos (-v)
  have hz1 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hv)
  have hc := involution_balance_bounds
  have hw := involution_level_weight_bounds hv
  have hd : 2 * Real.exp (-v)^2 - (1+involutionBalance)*Real.exp (-v) ≤ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1+involutionBalance) hz.le,
      mul_nonneg hz.le (sub_nonneg.mpr hz1)]
  exact sub_pos.mpr ((div_lt_one (involution_level_weight_pos hv)).mpr (by linarith))

theorem involution_level_map_strict : StrictMonoOn involutionLevelMap (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro v hv
    exact (involution_level_map_derivative hv).continuousAt.continuousWithinAt
  · intro v hv
    have hv0 : 0 ≤ v := (interior_subset hv)
    rw [(involution_level_map_derivative hv0).deriv]
    exact involution_level_map_derivative_pos hv0

theorem involution_level_map_zero : involutionLevelMap 0 = 0 := by
  simp [involutionLevelMap, involutionLevelWeight, involutionLevelPerturbation]

theorem involution_level_map_measurable : Measurable involutionLevelMap := by
  exact measurable_id.sub (Real.measurable_log.comp involution_level_weight_continuous.measurable)

theorem involution_level_map_atTop : Tendsto involutionLevelMap atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (max 0 (b+1))] with v hv
  have hv0 : 0 ≤ v := le_trans (le_max_left _ _) hv
  have hw := involution_level_weight_bounds hv0
  have hl := Real.log_le_sub_one_of_pos (involution_level_weight_pos hv0)
  have hb : b+1 ≤ v := le_trans (le_max_right _ _) hv
  unfold involutionLevelMap
  linarith

def involutionCounterpotential (t : ℝ) : ℝ := involutionLevelMap (SigmaBase.potential t)

theorem involution_counterpotential_two_branch : TwoBranchPotential involutionCounterpotential := by
  have hI := intrinsic_potential_two_branch
  refine ⟨involution_level_map_measurable.comp hI.measurable, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hh : ContinuousOn involutionLevelMap (Ici 0) :=
      fun v hv => (involution_level_map_derivative hv).continuousAt.continuousWithinAt
    exact hh.comp hI.continuous (fun t ht => hI.nonnegative ht)
  · simp only [involutionCounterpotential, hI.anchor, involution_level_map_zero]
  · intro x hx y hy hxy
    exact involution_level_map_strict (hI.nonnegative hy.1) (hI.nonnegative hx.1)
      (hI.left_strict hx hy hxy)
  · intro x hx y hy hxy
    change 1 ≤ x at hx
    change 1 ≤ y at hy
    exact involution_level_map_strict (hI.nonnegative (by linarith : 0 < x))
      (hI.nonnegative (by linarith : 0 < y)) (hI.right_strict hx hy hxy)
  · exact involution_level_map_atTop.comp hI.left_limit
  · exact involution_level_map_atTop.comp hI.right_limit

theorem involution_counterpotential_equal_level (t : ℝ) (ht : 0 < t) :
    involutionCounterpotential (canonicalDeficitInvolution t) = involutionCounterpotential t := by
  unfold involutionCounterpotential
  rw [(canonical_deficit_involution_positive_level t ht).2]

theorem involution_level_map_nontrivial : ∃ v, 0 < v ∧ involutionLevelMap v ≠ v := by
  have hc := involution_balance_bounds
  let v := -Real.log (involutionBalance/2)
  have hp : 0 < involutionBalance/2 := by linarith
  have hlt : involutionBalance/2 < 1 := by linarith
  have hv : 0 < v := neg_pos.mpr (Real.log_neg hp hlt)
  have hz : Real.exp (-v) = involutionBalance/2 := by simp [v, Real.exp_log hp]
  refine ⟨v,hv,?_⟩
  intro he
  have hl : Real.log (involutionLevelWeight v) = 0 := by
    unfold involutionLevelMap at he
    linarith
  have hw : involutionLevelWeight v = 1 := by
    have hh := congrArg Real.exp hl
    rwa [Real.exp_log (involution_level_weight_pos hv.le), Real.exp_zero] at hh
  have hk : involutionLevelPerturbation v = 0 := by
    unfold involutionLevelWeight at hw
    linarith
  have hkneg : involutionLevelPerturbation v < 0 := by
    unfold involutionLevelPerturbation
    rw [hz]
    exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  linarith

theorem involution_counterpotential_noncanonical :
    ∃ t, 0 < t ∧ involutionCounterpotential t ≠ SigmaBase.potential t := by
  obtain ⟨v,hv,hne⟩ := involution_level_map_nontrivial
  obtain ⟨a,b,ha,_,_,hav,_⟩ := intrinsic_potential_two_branch.roots v hv.le
  exact ⟨a,ha,by simpa only [involutionCounterpotential,hav] using hne⟩

theorem involution_counterpotential_density {t : ℝ} (ht : 0 < t) :
    Real.exp (-1-involutionCounterpotential t) =
      SigmaPresentations.density t * involutionLevelWeight (SigmaBase.potential t) := by
  rw [SigmaPresentations.density_eq_exp_potential ht]
  unfold involutionCounterpotential involutionLevelMap
  rw [show -1-(SigmaBase.potential t-Real.log (involutionLevelWeight (SigmaBase.potential t))) =
    (-1-SigmaBase.potential t)+Real.log (involutionLevelWeight (SigmaBase.potential t)) by ring,
    Real.exp_add, Real.exp_log (involution_level_weight_pos (intrinsic_potential_two_branch.nonnegative ht))]

theorem involution_level_weight_integrable :
    Integrable involutionLevelWeight gammaDeficitProbability :=
  (integrable_const 1).add (involution_level_perturbation_integrable.div_const 10)

theorem involution_level_weight_mean_one :
    (∫ v, involutionLevelWeight v ∂gammaDeficitProbability) = 1 := by
  change (∫ v, 1 + involutionLevelPerturbation v / 10 ∂gammaDeficitProbability) = 1
  rw [integral_add (integrable_const 1)
    (involution_level_perturbation_integrable.div_const 10), integral_div,
    involution_level_perturbation_mean_zero]
  simp

theorem involution_counterpotential_density_integrable :
    IntegrableOn (fun t => Real.exp (-1-involutionCounterpotential t)) (Ioi 0) := by
  have hi : Integrable (fun t => involutionLevelWeight (SigmaBase.potential t)) gammaProbability :=
    involution_level_weight_integrable.comp_aemeasurable intrinsic_potential_measurable.aemeasurable
  apply ((gamma_density_integrability _).mp hi).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (involution_counterpotential_density ht).symm

theorem involution_counterpotential_density_mass :
    (∫ t : ℝ in Ioi 0, Real.exp (-1-involutionCounterpotential t)) = 1 := by
  calc
    _ = ∫ t : ℝ in Ioi 0, SigmaPresentations.density t *
        involutionLevelWeight (SigmaBase.potential t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact involution_counterpotential_density ht
    _ = ∫ t, involutionLevelWeight (SigmaBase.potential t) ∂gammaProbability :=
      (gamma_probability_integral _).symm
    _ = ∫ v, involutionLevelWeight v ∂gammaDeficitProbability :=
      (integral_map intrinsic_potential_measurable.aemeasurable
        involution_level_weight_continuous.aestronglyMeasurable).symm
    _ = 1 := involution_level_weight_mean_one

def involutionCounterprobability : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (deficitWeight ∘ involutionCounterpotential)

instance involution_counterprobability_is_probability : IsProbabilityMeasure involutionCounterprobability := by
  constructor
  rw [involutionCounterprobability, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-1-involutionCounterpotential t))) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal involution_counterpotential_density_integrable
    (Eventually.of_forall (fun t => (Real.exp_pos _).le)), involution_counterpotential_density_mass,
    ENNReal.ofReal_one]

theorem involution_counterpotential_pair :
    ∀ b ≥ 1, 0 < canonicalDeficitInvolution b ∧ canonicalDeficitInvolution b ≤ 1 ∧
      involutionCounterpotential (canonicalDeficitInvolution b) = involutionCounterpotential b := by
  intro b hb
  have hp := canonical_deficit_involution_pair b hb
  exact ⟨hp.1,hp.2.1,involution_counterpotential_equal_level b (by linarith)⟩

theorem involution_counterpotential_deficit_law_ne :
    Measure.map involutionCounterpotential involutionCounterprobability ≠ gammaDeficitProbability := by
  intro he
  have hu := canonical_deficit_pair_identifies_potential involutionCounterpotential
    involution_counterpotential_two_branch involution_counterpotential_pair he
  obtain ⟨t,ht,hne⟩ := involution_counterpotential_noncanonical
  exact hne (hu t ht)

/-- A normalized, genuinely noncanonical member of the paper's two-branch class
with the exact canonical equal-level involution. Normalization is derived from
a zero-mean perturbation of the actual deficit law, without shifting the anchor. -/
theorem canonical_involution_does_not_identify_linked_density :
    ∃ J : ℝ → ℝ, TwoBranchPotential J ∧
      IsProbabilityMeasure ((volume.restrict (Ioi 0)).withDensity (deficitWeight ∘ J)) ∧
      (∫ t : ℝ in Ioi 0, Real.exp (-1-J t)) = 1 ∧
      (∀ t > 0, J (canonicalDeficitInvolution t) = J t) ∧
      (∃ t > 0, J t ≠ SigmaBase.potential t) ∧
      Measure.map J ((volume.restrict (Ioi 0)).withDensity (deficitWeight ∘ J)) ≠ gammaDeficitProbability :=
  ⟨involutionCounterpotential, involution_counterpotential_two_branch,
    involution_counterprobability_is_probability, involution_counterpotential_density_mass,
    involution_counterpotential_equal_level, involution_counterpotential_noncanonical,
    involution_counterpotential_deficit_law_ne⟩

end
end Sigma
