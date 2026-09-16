import SigmaPlacementPackage
import SigmaProbCanonicalPair

namespace Sigma
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology

/-- The actual placed density measure on its whole analytic domain. -/
def placedDensityMeasure (μ a : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (-a / μ))).withDensity
    (fun r => ENNReal.ofReal (Real.exp (placed μ a r)))

theorem affine_map_volume (μ a : ℝ) (hμ : 0 < μ) :
    Measure.map (fun r : ℝ => μ*r+a) volume =
      ENNReal.ofReal μ⁻¹ • volume := by
  have he : (fun r : ℝ => μ*r+a) = (fun t => t+a) ∘ (fun r => μ*r) := rfl
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop),
    Real.map_volume_mul_left hμ.ne', Measure.map_smul,
    map_add_right_eq_self, abs_of_pos (inv_pos.mpr hμ)]

theorem affine_map_domain_volume (μ a : ℝ) (hμ : 0 < μ) :
    Measure.map (fun r : ℝ => μ*r+a) (volume.restrict (Ioi (-a/μ))) =
      ENNReal.ofReal μ⁻¹ • volume.restrict (Ioi 0) := by
  have hp : (fun r : ℝ => μ*r+a) ⁻¹' Ioi 0 = Ioi (-a/μ) := by
    ext r
    exact (placed_coordinate_positive hμ).symm
  rw [← hp, ← Measure.restrict_map (by fun_prop) measurableSet_Ioi,
    affine_map_volume μ a hμ, Measure.restrict_smul]

/-- Change of variables for the full placed density, as equality of measures. -/
theorem placed_density_affine_pushforward (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    Measure.map (fun r : ℝ => μ*r+a) (placedDensityMeasure μ a) =
      ENNReal.ofReal (Real.exp a/(1+a)) • gammaProbability := by
  let c : ℝ := Real.exp a/(1+a)
  have hc : 0 ≤ c := (div_pos (Real.exp_pos _) (by linarith)).le
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (μ*c) * deficitWeight (I t)
  have hw : Measurable w := measurable_const.mul
    (deficit_weight_measurable.comp intrinsic_potential_measurable)
  have hd : placedDensityMeasure μ a =
      (volume.restrict (Ioi (-a/μ))).withDensity (w ∘ (fun r => μ*r+a)) := by
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have ht := (placed_coordinate_positive hμ).mp hr
    change ENNReal.ofReal (Real.exp (placed μ a r)) =
      ENNReal.ofReal (μ*c) * deficitWeight (I (μ*r+a))
    rw [intrinsic_linked_density _ ht, ← ENNReal.ofReal_mul (mul_nonneg hμ.le hc),
      placed_density_identity hμ ha ht]
    congr 1
    dsimp [c]
    ring
  rw [hd, ← map_with_linked_density _ _ (by fun_prop) w hw,
    affine_map_domain_volume μ a hμ, withDensity_smul_measure]
  have hw' : (volume.restrict (Ioi (0:ℝ))).withDensity w =
      ENNReal.ofReal (μ*c) • gammaProbability := by
    change (volume.restrict (Ioi (0:ℝ))).withDensity
      (ENNReal.ofReal (μ*c) • (deficitWeight ∘ I)) = _
    rw [withDensity_smul _ (deficit_weight_measurable.comp intrinsic_potential_measurable),
      canonical_linked_density_measure]
  rw [hw', smul_smul, ← ENNReal.ofReal_mul (inv_nonneg.mpr hμ.le)]
  congr 2
  change μ⁻¹*(μ*c) = c
  rw [← mul_assoc, inv_mul_cancel₀ hμ.ne', one_mul]

/-- The inverse affine map recovers the placed density measure exactly. -/
theorem placed_density_affine_pullback (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    Measure.map (fun t : ℝ => (t-a)/μ)
      (ENNReal.ofReal (Real.exp a/(1+a)) • gammaProbability) =
      placedDensityMeasure μ a := by
  rw [← placed_density_affine_pushforward μ a hμ ha,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun t : ℝ => (t-a)/μ) ∘ (fun r => μ*r+a) = id := by
    funext r
    dsimp
    field_simp
  rw [he, Measure.map_id]

/-- Restriction to nonnegative placed coordinates corresponds to truncation at a. -/
theorem placed_density_nonnegative_pushforward (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    Measure.map (fun r : ℝ => μ*r+a)
      ((placedDensityMeasure μ a).restrict (Ici 0)) =
      ENNReal.ofReal (Real.exp a/(1+a)) • gammaProbability.restrict (Ici a) := by
  have hp : (fun r : ℝ => μ*r+a) ⁻¹' Ici a = Ici 0 := by
    ext r
    change a ≤ μ*r+a ↔ 0 ≤ r
    constructor <;> intro hr
    · nlinarith
    · nlinarith
  rw [← hp, ← Measure.restrict_map (by fun_prop) measurableSet_Ici,
    placed_density_affine_pushforward μ a hμ ha, Measure.restrict_smul]

theorem placed_density_full_mass (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    placedDensityMeasure μ a univ = ENNReal.ofReal (Real.exp a/(1+a)) := by
  have he := congrArg (fun ν : Measure ℝ => ν univ)
    (placed_density_affine_pushforward μ a hμ ha)
  simpa only [Measure.map_apply (by fun_prop : Measurable (fun r : ℝ => μ*r+a))
    MeasurableSet.univ, preimage_univ, Measure.smul_apply,
    gamma_probability_normalized, smul_eq_mul, mul_one] using he

theorem placed_density_nonnegative_mass (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    placedDensityMeasure μ a (Ici 0) = 1 := by
  have he := congrArg (fun ν : Measure ℝ => ν univ)
    (placed_density_nonnegative_pushforward μ a hμ ha)
  simp only [Measure.map_apply (by fun_prop : Measurable (fun r : ℝ => μ*r+a))
    MeasurableSet.univ, preimage_univ, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Measure.smul_apply, smul_eq_mul] at he
  rw [he, ← measure_congr (Ioi_ae_eq_Ici' (gamma_probability_no_atom a)),
    gamma_probability_tail a ha.le,
    ← ENNReal.ofReal_mul (div_pos (Real.exp_pos _) (by linarith)).le]
  have hp : Real.exp a/(1+a)*gammaSurvival a = 1 := by
    unfold gammaSurvival
    have hn : 1+a ≠ 0 := by linarith
    calc
      _ = Real.exp a * Real.exp (-a) := by field_simp; ring
      _ = 1 := by rw [← Real.exp_add]; simp
  rw [hp, ENNReal.ofReal_one]

/-- The original placed expression, restricted to its stated domain, gives
the same density measure as the intrinsic-coordinate formula. -/
theorem placed_original_density_measure (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    (volume.restrict (Ioi (-a/μ))).withDensity
      (fun r => ENNReal.ofReal (Real.exp (placedOriginal μ (μ/a) r))) =
      placedDensityMeasure μ a := by
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [placed_original_identity hμ ha ((placed_coordinate_positive hμ).mp hr)]

/-- The intrinsic function is extracted by removing the recovered placement
and its value at the closure point. -/
theorem placed_recover_intrinsic (μ a t : ℝ) (hμ : 0 < μ) :
    placed μ a ((t-a)/μ) - placed μ a ((1-a)/μ) = H t := by
  simp only [placed, placed_coordinate_inverse hμ, H, SigmaPresentations.H, Real.log_one]
  ring

theorem placed_recover_offset (μ a : ℝ) (hμ : 0 < μ) : μ/(μ/a) = a := by
  field_simp

namespace PlacedParameters

def positivePresentation (P : PlacedParameters) : Ioi (0:ℝ) → ℝ :=
  fun r => P.presentation r

theorem positivePresentation_injective : Function.Injective positivePresentation := by
  intro P Q he
  have hp := placed_parameters_unique P.hμ P.ha Q.hμ Q.ha
    (fun r hr => congrFun he ⟨r,hr⟩)
  cases P
  cases Q
  simp_all

/-- Exact admissibility from Definition C0, retaining its upper offset bound. -/
abbrev Admissible := {P : PlacedParameters // P.a < 1}

def admissiblePresentation (P : Admissible) : Ioi (0:ℝ) → ℝ :=
  P.val.positivePresentation

theorem admissiblePresentation_injective : Function.Injective admissiblePresentation := by
  intro P Q he
  apply Subtype.ext
  exact positivePresentation_injective he

/-- The placed family and its admissible parameter class are exactly equivalent. -/
def presentationEquiv : Admissible ≃ Set.range admissiblePresentation :=
  Equiv.ofInjective admissiblePresentation admissiblePresentation_injective

theorem presentationEquiv_forward (P : Admissible) :
    (presentationEquiv P).val = admissiblePresentation P := rfl

theorem presentationEquiv_roundtrip (F : Set.range admissiblePresentation) :
    admissiblePresentation (presentationEquiv.symm F) = F.val := by
  exact congrArg Subtype.val (presentationEquiv.apply_symm_apply F)

end PlacedParameters

end
end Sigma
