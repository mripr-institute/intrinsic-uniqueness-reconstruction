import SigmaRealRadialBoundary
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace Sigma
noncomputable section
open MeasureTheory Measure Set Metric
open scoped ENNReal NNReal

abbrev RadialFourSphere := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

def radialFourSurface : Measure RadialFourSphere :=
  (volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere

def radialFourPolarLift (p : RadialFourSphere × Ioi (0 : ℝ)) :
    EuclideanSpace ℝ (Fin 4) := p.2.val • p.1.val

theorem radial_four_polar_lift_measurable : Measurable radialFourPolarLift := by
  unfold radialFourPolarLift
  fun_prop

theorem radial_four_polar_lift_norm (p : RadialFourSphere × Ioi (0 : ℝ)) :
    ‖radialFourPolarLift p‖ = p.2.val := by
  rw [radialFourPolarLift, norm_smul, Real.norm_eq_abs, abs_of_pos p.2.property,
    mem_sphere_zero_iff_norm.mp p.1.property, mul_one]

/-- Literal polar-coordinate disintegration of Euclidean Lebesgue measure,
including the measure-zero removal of the origin. -/
theorem radial_four_polar_lift_volume :
    (radialFourSurface.prod (Measure.volumeIoiPow 3)).map radialFourPolarLift =
      (volume : Measure (EuclideanSpace ℝ (Fin 4))) := by
  let e := homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 4))
  have hp := (volume : Measure (EuclideanSpace ℝ (Fin 4))).measurePreserving_homeomorphUnitSphereProd
  have hi := hp.symm e.toMeasurableEquiv
  have he : (Measure.comap (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 4))) → _) volume).map
      Subtype.val = (volume : Measure (EuclideanSpace ℝ (Fin 4))) := by
    rw [map_comap_subtype_coe (measurableSet_singleton _).compl, restrict_compl_singleton]
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) - 1 = 3 := by simp
  rw [hn] at hi
  change ((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere.prod
      (Measure.volumeIoiPow 3)).map (Subtype.val ∘ e.symm) = _
  have himap : ((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere.prod
      (Measure.volumeIoiPow 3)).map e.symm = Measure.comap Subtype.val volume := hi.map_eq
  rw [← Measure.map_map measurable_subtype_coe e.symm.measurable, himap, he]

theorem radial_four_surface_mass_ne_zero : radialFourSurface univ ≠ 0 := by
  rw [radialFourSurface, Measure.toSphere_apply_univ]
  apply mul_ne_zero
  · simp
  · exact ne_of_gt (measure_ball_pos _ _ (by norm_num))

instance radial_four_surface_finite : IsFiniteMeasure radialFourSurface := by
  unfold radialFourSurface
  infer_instance

def radialFourUniformSphere : Measure RadialFourSphere :=
  (radialFourSurface univ)⁻¹ • radialFourSurface

instance radial_four_uniform_sphere_probability : IsProbabilityMeasure radialFourUniformSphere := by
  constructor
  rw [radialFourUniformSphere, Measure.smul_apply, smul_eq_mul,
    ENNReal.inv_mul_cancel radial_four_surface_mass_ne_zero (measure_ne_top _ _)]

/-- Pulling a density back along a measurable map commutes with pushforward. -/
theorem radial_map_with_density_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (hf : Measurable f)
    (g : β → ℝ≥0∞) (hg : Measurable g) :
    (μ.withDensity (fun x => g (f x))).map f = (μ.map f).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
    setLIntegral_map hs hg hf]

/-- The full vector density obtained by weighting the genuine polar product. -/
theorem radial_four_polar_density (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ((radialFourSurface.prod (Measure.volumeIoiPow 3)).withDensity
      (fun p => f p.2.val)).map radialFourPolarLift =
      volume.withDensity (fun z : EuclideanSpace ℝ (Fin 4) => f ‖z‖) := by
  have h := radial_map_with_density_comp
    (radialFourSurface.prod (Measure.volumeIoiPow 3)) radialFourPolarLift
    radial_four_polar_lift_measurable (fun z => f ‖z‖) (hf.comp measurable_norm)
  simpa only [radial_four_polar_lift_norm, radial_four_polar_lift_volume] using h

theorem radial_product_density_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν]
    (f : β → ℝ≥0∞) (hf : Measurable f) (hft : ∀ x, f x ≠ ∞) :
    μ.prod (ν.withDensity f) = (μ.prod ν).withDensity (fun p => f p.2) := by
  letI := SigmaFinite.withDensity_of_ne_top' (μ := ν) hft
  apply Measure.prod_eq
  intro s t hs ht
  rw [withDensity_apply _ (hs.prod ht), ← prod_restrict,
    lintegral_prod _ (show Measurable (fun p : α × β => f p.2) from
      hf.comp measurable_snd).aemeasurable]
  simp only [Prod.snd]
  rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, withDensity_apply _ ht, mul_comm]

def radialFourRadiusMeasure (f : ℝ → ℝ≥0∞) : Measure (Ioi (0 : ℝ)) :=
  (radialFourSurface univ) •
    ((Measure.volumeIoiPow 3).withDensity (fun r => f r.val))

/-- Normalize the angular factor of a radial density, putting its total area
into the radial factor. This retains the genuine uniform surface probability. -/
theorem radial_four_normalized_polar_product (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (hft : ∀ x, f x ≠ ∞) :
    radialFourUniformSphere.prod (radialFourRadiusMeasure f) =
      (radialFourSurface.prod (Measure.volumeIoiPow 3)).withDensity (fun p => f p.2.val) := by
  rw [← radial_product_density_right radialFourSurface (Measure.volumeIoiPow 3)
    (fun r : Ioi (0 : ℝ) => f r.val) (hf.comp measurable_subtype_coe) (fun r => hft r.val)]
  letI := SigmaFinite.withDensity_of_ne_top' (μ := Measure.volumeIoiPow 3) (fun r => hft r.val)
  letI : SFinite (radialFourRadiusMeasure f) := by
    unfold radialFourRadiusMeasure
    infer_instance
  apply Eq.symm
  apply Measure.prod_eq
  intro s t hs ht
  rw [Measure.prod_prod, radialFourUniformSphere, radialFourRadiusMeasure,
    Measure.smul_apply, Measure.smul_apply]
  simp only [smul_eq_mul]
  calc
    _ = ((radialFourSurface univ)⁻¹ * radialFourSurface univ) *
        (radialFourSurface s * ((Measure.volumeIoiPow 3).withDensity (fun r => f r.val)) t) := by
      ring
    _ = _ := by rw [ENNReal.inv_mul_cancel radial_four_surface_mass_ne_zero
      (measure_ne_top _ _), one_mul]

theorem radial_four_normalized_density (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (hft : ∀ x, f x ≠ ∞) :
    (radialFourUniformSphere.prod (radialFourRadiusMeasure f)).map radialFourPolarLift =
      volume.withDensity (fun z : EuclideanSpace ℝ (Fin 4) => f ‖z‖) := by
  rw [radial_four_normalized_polar_product f hf hft, radial_four_polar_density f hf]

end
end Sigma
