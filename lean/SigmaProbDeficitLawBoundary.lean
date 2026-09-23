import SigmaProbDeficitLawShift
import SigmaProbDeficitWidth
import SigmaProbDeficitTransform

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

theorem shifted_deficit_linked_law (ε : ℝ) (e : ℝ ≃o ℝ)
    (he : ∀ t : ℝ, e t = t+ε*deficitLevelShift t) :
    Measure.map (SigmaBase.potential ∘ e.symm)
      ((volume.restrict (Ioi 0)).withDensity
        (deficitWeight ∘ (SigmaBase.potential ∘ e.symm))) = gammaDeficitProbability := by
  have hh := equal_widths_linked_deficit_law
    (shifted_deficit_potential_two_branch ε e he) intrinsic_potential_two_branch ?_
  · simpa only [canonical_linked_density_measure, gammaDeficitProbability] using hh
  · intro v hv
    have hc := canonical_deficit_roots_spec v hv
    have hs := shifted_deficit_roots_and_width ε e he v hv
    exact ⟨e (canonicalDeficitRoots v).1, e (canonicalDeficitRoots v).2,
      (canonicalDeficitRoots v).1, (canonicalDeficitRoots v).2,
      ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩, hc, hs.2.2.2.2.2⟩

theorem linked_probability_real_normalization (J : ℝ → ℝ) (hJ : Measurable J)
    [IsProbabilityMeasure ((volume.restrict (Ioi (0 : ℝ))).withDensity (deficitWeight ∘ J))] :
    IntegrableOn (fun t => Real.exp (-1-J t)) (Ioi 0) volume ∧
      (∫ t : ℝ in Ioi 0, Real.exp (-1-J t)) = 1 := by
  have hm : (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-1-J t))) = 1 := by
    have h := measure_univ (μ := (volume.restrict (Ioi (0 : ℝ))).withDensity (deficitWeight ∘ J))
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      Function.comp_apply, deficitWeight] using h
  have hmeas : Measurable (fun t => Real.exp (-1-J t)) := (measurable_const.sub hJ).exp
  have hnonneg : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0 ≤ Real.exp (-1-J t) :=
    Eventually.of_forall (fun t => (Real.exp_pos _).le)
  have hi : IntegrableOn (fun t => Real.exp (-1-J t)) (Ioi 0) volume := by
    refine ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnonneg).mpr ?_⟩
    rw [hm]
    exact ENNReal.one_lt_top
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hmeas.aestronglyMeasurable, hm]
  simp

theorem linked_deficit_noncanonical_pairing_boundary (J : ℝ → ℝ)
    (hJ : TwoBranchPotential J)
    (hlaw : Measure.map J ((volume.restrict (Ioi 0)).withDensity (deficitWeight ∘ J)) =
      gammaDeficitProbability)
    (hne : ∃ t > 0, J t ≠ SigmaBase.potential t) :
    ∃ b ≥ 1, J (canonicalDeficitInvolution b) ≠ J b := by
  by_contra hn
  push_neg at hn
  have hpair : ∀ b ≥ 1, 0 < canonicalDeficitInvolution b ∧
      canonicalDeficitInvolution b ≤ 1 ∧ J (canonicalDeficitInvolution b) = J b := by
    intro b hb
    exact ⟨(canonical_deficit_involution_pair b hb).1,
      (canonical_deficit_involution_pair b hb).2.1, hn b hb⟩
  have he := canonical_deficit_pair_identifies_potential J hJ hpair hlaw
  obtain ⟨t, ht, hnt⟩ := hne
  exact hnt (he t ht)

/-- A noncanonical potential in the exact normalized candidate class has
the complete canonical linked deficit probability law. The law equality and
normalization are derived from actual pushforward measures, not assumed. -/
theorem canonical_deficit_law_does_not_identify_potential :
    ∃ J : ℝ → ℝ, TwoBranchPotential J ∧
      IsProbabilityMeasure ((volume.restrict (Ioi (0 : ℝ))).withDensity (deficitWeight ∘ J)) ∧
      IntegrableOn (fun t => Real.exp (-1-J t)) (Ioi 0) volume ∧
      (∫ t : ℝ in Ioi 0, Real.exp (-1-J t)) = 1 ∧
      Measure.map J ((volume.restrict (Ioi 0)).withDensity (deficitWeight ∘ J)) =
        gammaDeficitProbability ∧
      (∃ t > 1, J t ≠ SigmaBase.potential t) ∧
      (∃ b ≥ 1, J (canonicalDeficitInvolution b) ≠ J b) := by
  obtain ⟨ε, hε, e, he⟩ := deficit_level_shift_orderIso
  let J := SigmaBase.potential ∘ e.symm
  have hJ : TwoBranchPotential J := shifted_deficit_potential_two_branch ε e he
  have hlaw := shifted_deficit_linked_law ε e he
  haveI : IsProbabilityMeasure
      ((volume.restrict (Ioi (0 : ℝ))).withDensity (deficitWeight ∘ J)) := by
    apply probability_of_map_eq_probability hJ.measurable intrinsic_potential_measurable
      (ν := gammaProbability)
    exact hlaw
  obtain ⟨hi, hm⟩ := linked_probability_real_normalization J hJ.measurable
  have hne := shifted_deficit_potential_noncanonical ε hε e he
  refine ⟨J, hJ, inferInstance, hi, hm, hlaw, hne,
    linked_deficit_noncanonical_pairing_boundary J hJ hlaw ?_⟩
  obtain ⟨t, ht, hnt⟩ := hne
  exact ⟨t, lt_trans (by norm_num : (0 : ℝ) < 1) ht, hnt⟩

end
end Sigma
