import SigmaProbDeficitCDF

namespace Sigma
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

def canonicalDeficitRoots (v : ℝ) : ℝ×ℝ :=
  if hv : 0 ≤ v then
    let hr := intrinsic_potential_two_branch.roots v hv
    (Classical.choose hr, Classical.choose (Classical.choose_spec hr))
  else (1,1)

theorem canonical_deficit_roots_spec (v : ℝ) (hv : 0 ≤ v) :
    0 < (canonicalDeficitRoots v).1 ∧ (canonicalDeficitRoots v).1 ≤ 1 ∧
    1 ≤ (canonicalDeficitRoots v).2 ∧
    SigmaBase.potential (canonicalDeficitRoots v).1 = v ∧
    SigmaBase.potential (canonicalDeficitRoots v).2 = v := by
  simp only [canonicalDeficitRoots, dif_pos hv]
  exact Classical.choose_spec (Classical.choose_spec (intrinsic_potential_two_branch.roots v hv))

theorem canonical_deficit_lower_inverse (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    (canonicalDeficitRoots (SigmaBase.potential t)).1 = t := by
  have hs := canonical_deficit_roots_spec _ (intrinsic_potential_two_branch.nonnegative ht)
  exact intrinsic_potential_two_branch.left_strict.injOn ⟨hs.1,hs.2.1⟩ ⟨ht,ht1⟩ hs.2.2.2.1

theorem canonical_deficit_upper_inverse (t : ℝ) (ht : 1 ≤ t) :
    (canonicalDeficitRoots (SigmaBase.potential t)).2 = t := by
  have hs := canonical_deficit_roots_spec _
    (intrinsic_potential_two_branch.nonnegative (by linarith : 0 < t))
  exact intrinsic_potential_two_branch.right_strict.injOn hs.2.2.1 ht hs.2.2.2.2

theorem canonical_deficit_roots_zero : canonicalDeficitRoots 0 = (1,1) := by
  have hl := canonical_deficit_lower_inverse 1 (by norm_num) le_rfl
  have hr := canonical_deficit_upper_inverse 1 le_rfl
  simp only [SigmaBase.potential, Real.log_one] at hl hr
  norm_num at hl hr
  exact Prod.ext hl hr

def canonicalDeficitInvolution (t : ℝ) : ℝ :=
  if 0 < t then
    if t < 1 then (canonicalDeficitRoots (SigmaBase.potential t)).2
    else (canonicalDeficitRoots (SigmaBase.potential t)).1
  else 0

theorem canonical_deficit_involution_anchor : canonicalDeficitInvolution 1 = 1 := by
  simp [canonicalDeficitInvolution, SigmaBase.potential, canonical_deficit_roots_zero]

theorem canonical_deficit_involution_pair (b : ℝ) (hb : 1 ≤ b) :
    0 < canonicalDeficitInvolution b ∧ canonicalDeficitInvolution b ≤ 1 ∧
    SigmaBase.potential (canonicalDeficitInvolution b) = SigmaBase.potential b := by
  have hb0 : 0 < b := by linarith
  have hs := canonical_deficit_roots_spec _ (intrinsic_potential_two_branch.nonnegative hb0)
  simp only [canonicalDeficitInvolution, if_pos hb0, if_neg (not_lt_of_ge hb)]
  exact ⟨hs.1,hs.2.1,hs.2.2.2.1⟩

theorem canonical_deficit_cdf (v : ℝ) (hv : 0 ≤ v) :
    gammaDeficitProbability (Iic v) = ENNReal.ofReal
      (gammaSurvival (canonicalDeficitRoots v).1-gammaSurvival (canonicalDeficitRoots v).2) := by
  have hs := canonical_deficit_roots_spec v hv
  exact gamma_deficit_cdf_from_roots v _ _ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2

theorem intrinsic_linked_density (t : ℝ) (ht : 0 < t) :
    deficitWeight (SigmaBase.potential t) = ENNReal.ofReal (SigmaPresentations.density t) := by
  unfold deficitWeight SigmaBase.potential SigmaPresentations.density
  have he : -1-(t-1-Real.log t) = Real.log t+(-t) := by ring
  rw [he, Real.exp_add, Real.exp_log ht]

theorem canonical_linked_density_measure :
    (volume.restrict (Ioi (0 : ℝ))).withDensity
      (deficitWeight ∘ SigmaBase.potential) = gammaProbability := by
  ext A hA
  have hconull : gammaProbability (Ioi (0 : ℝ))ᶜ = 0 := by
    change gammaProbability {t : ℝ | ¬ 0 < t} = 0
    exact ae_iff.mp (operator_integer_samples_ae_pos gammaProbability
      operator_gamma_probability_integer_samples)
  rw [← measure_inter_conull hconull,
    gamma_probability_measure_positive_set _ (hA.inter measurableSet_Ioi) inter_subset_right,
    withDensity_apply _ hA, Measure.restrict_restrict hA]
  have he : (∫⁻ t in A ∩ Ioi 0, (deficitWeight ∘ SigmaBase.potential) t) =
      ∫⁻ t in A ∩ Ioi 0, ENNReal.ofReal (SigmaPresentations.density t) := by
    apply setLIntegral_congr_fun (hA.inter measurableSet_Ioi)
    filter_upwards with t ht
    exact intrinsic_linked_density t ht.2
  rw [he, ← ofReal_integral_eq_lintegral_ofReal
    (intrinsic_density_integrable.mono_set inter_subset_right)]
  filter_upwards [ae_restrict_mem (hA.inter measurableSet_Ioi)] with t ht
  exact (SigmaPresentations.density_pos ht.2).le

/-- An actual canonical pair, with no external target pairing or monotonicity
premise, identifies every potential in the marked candidate class. -/
theorem canonical_deficit_pair_identifies_potential (J : ℝ → ℝ)
    (hJ : TwoBranchPotential J)
    (hpair : ∀ b ≥ 1, 0 < canonicalDeficitInvolution b ∧ canonicalDeficitInvolution b ≤ 1 ∧
      J (canonicalDeficitInvolution b) = J b)
    (hlaw : Measure.map J ((volume.restrict (Ioi 0)).withDensity (deficitWeight ∘ J)) =
      gammaDeficitProbability) :
    ∀ t > 0, J t = SigmaBase.potential t := by
  apply canonical_linked_deficit_identifies_I J hJ canonicalDeficitInvolution
    (intrinsic_potential_two_branch.pair_strictAnti _ canonical_deficit_involution_pair)
    hpair canonical_deficit_involution_pair
  rw [canonical_linked_density_measure]
  exact hlaw

theorem canonical_deficit_involution_lower (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    1 < canonicalDeficitInvolution t ∧
    SigmaBase.potential (canonicalDeficitInvolution t) = SigmaBase.potential t := by
  have hs := canonical_deficit_roots_spec _ (intrinsic_potential_two_branch.nonnegative ht)
  have hv : 0 < SigmaBase.potential t := by
    have hh := intrinsic_potential_two_branch.left_strict ⟨ht,ht1.le⟩
      (show (1 : ℝ) ∈ Ioc 0 1 by norm_num) ht1
    simpa [SigmaBase.potential] using hh
  have hb : 1 < (canonicalDeficitRoots (SigmaBase.potential t)).2 := by
    by_contra hn
    have he := le_antisymm (le_of_not_gt hn) hs.2.2.1
    have hh := hs.2.2.2.2
    rw [he] at hh
    simp [SigmaBase.potential] at hh
    unfold SigmaBase.potential at hv
    linarith
  simp only [canonicalDeficitInvolution, if_pos ht, if_pos ht1]
  exact ⟨hb,hs.2.2.2.2⟩

theorem canonical_deficit_involution_involutive (t : ℝ) (ht : 0 < t) :
    canonicalDeficitInvolution (canonicalDeficitInvolution t) = t := by
  rcases lt_trichotomy t 1 with ht1 | rfl | h1t
  · have hp := canonical_deficit_involution_lower t ht ht1
    rw [canonicalDeficitInvolution, if_pos (by linarith : 0 < canonicalDeficitInvolution t),
      if_neg (not_lt_of_ge hp.1.le), hp.2,
      canonical_deficit_lower_inverse t ht ht1.le]
  · simp [canonical_deficit_involution_anchor]
  · have hp := canonical_deficit_involution_pair t h1t.le
    have hj : canonicalDeficitInvolution t < 1 := by
      by_contra hn
      have he := le_antisymm hp.2.1 (le_of_not_gt hn)
      have hh := intrinsic_potential_two_branch.right_strict
        (show (1 : ℝ) ∈ Ici 1 by simp) h1t.le h1t
      rw [← hp.2.2, he] at hh
      exact lt_irrefl _ hh
    rw [canonicalDeficitInvolution, if_pos hp.1, if_pos hj, hp.2.2,
      canonical_deficit_upper_inverse t h1t.le]

theorem canonical_deficit_involution_fixed_point (t : ℝ) (ht : 0 < t) :
    canonicalDeficitInvolution t = t ↔ t = 1 := by
  constructor
  · intro he
    rcases lt_trichotomy t 1 with ht1 | he1 | h1t
    · have hh := (canonical_deficit_involution_lower t ht ht1).1
      rw [he] at hh
      linarith
    · exact he1
    · have hh := (canonical_deficit_involution_pair t h1t.le).2.1
      rw [he] at hh
      linarith
  · rintro rfl
    exact canonical_deficit_involution_anchor

/-- Literal ray-only interface for the concrete canonical linked pair. -/
theorem canonical_deficit_pair_identifies_on_positive_ray (J : ℝ → ℝ)
    (hJ : RayPotential J)
    (hpair : ∀ b ≥ 1, 0 < canonicalDeficitInvolution b ∧ canonicalDeficitInvolution b ≤ 1 ∧
      J (canonicalDeficitInvolution b) = J b)
    (hlaw : Measure.map (positiveRayExtension J)
      ((volume.restrict (Ioi 0)).withDensity (deficitWeight ∘ positiveRayExtension J)) =
      gammaDeficitProbability) :
    ∀ t > 0, J t = SigmaBase.potential t ∧ Real.exp (-1-J t) = SigmaPresentations.density t := by
  have hp : ∀ b ≥ 1, 0 < canonicalDeficitInvolution b ∧ canonicalDeficitInvolution b ≤ 1 ∧
      positiveRayExtension J (canonicalDeficitInvolution b) = positiveRayExtension J b := by
    intro b hb
    rcases hpair b hb with ⟨hj0,hj1,he⟩
    refine ⟨hj0,hj1,?_⟩
    rw [positive_ray_extension_eq J hj0, positive_ray_extension_eq J (by linarith : 0 < b),he]
  have he := canonical_deficit_pair_identifies_potential _ hJ.extension hp hlaw
  intro t ht
  have htJ : J t = SigmaBase.potential t := by
    simpa only [positive_ray_extension_eq J ht] using he t ht
  refine ⟨htJ,?_⟩
  rw [htJ]
  unfold SigmaBase.potential SigmaPresentations.density
  have hex : -1-(t-1-Real.log t) = Real.log t+(-t) := by ring
  rw [hex,Real.exp_add,Real.exp_log ht]

theorem canonical_deficit_involution_positive_level (t : ℝ) (ht : 0 < t) :
    0 < canonicalDeficitInvolution t ∧
    SigmaBase.potential (canonicalDeficitInvolution t) = SigmaBase.potential t := by
  rcases lt_or_ge t 1 with h | h
  · have hh := canonical_deficit_involution_lower t ht h
    exact ⟨by linarith [hh.1],hh.2⟩
  · have hh := canonical_deficit_involution_pair t h
    exact ⟨hh.1,hh.2.2⟩

theorem canonical_deficit_involution_strictAnti :
    StrictAntiOn canonicalDeficitInvolution (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  rcases lt_or_ge x 1 with hx1 | hx1
  · rcases lt_or_ge y 1 with hy1 | hy1
    · have hpx := canonical_deficit_involution_lower x hx hx1
      have hpy := canonical_deficit_involution_lower y hy hy1
      have hI := intrinsic_potential_two_branch.left_strict ⟨hx,hx1.le⟩ ⟨hy,hy1.le⟩ hxy
      by_contra hn
      have hle := intrinsic_potential_two_branch.right_strict.monotoneOn hpx.1.le hpy.1.le
        (le_of_not_gt hn)
      rw [hpx.2,hpy.2] at hle
      exact not_lt_of_ge hle hI
    · have hpx := (canonical_deficit_involution_lower x hx hx1).1
      have hpy := (canonical_deficit_involution_pair y hy1).2.1
      linarith
  · exact (intrinsic_potential_two_branch.pair_strictAnti _ canonical_deficit_involution_pair)
      hx1 (hx1.trans hxy.le) hxy

theorem canonical_deficit_involution_preserves_density (t : ℝ) (ht : 0 < t) :
    SigmaPresentations.density (canonicalDeficitInvolution t) = SigmaPresentations.density t := by
  have hh := canonical_deficit_involution_positive_level t ht
  have he := congrArg deficitWeight hh.2
  rw [intrinsic_linked_density _ hh.1,intrinsic_linked_density t ht] at he
  have hr := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (SigmaPresentations.density_pos hh.1).le,
    ENNReal.toReal_ofReal (SigmaPresentations.density_pos ht).le] using hr

end
end Sigma
