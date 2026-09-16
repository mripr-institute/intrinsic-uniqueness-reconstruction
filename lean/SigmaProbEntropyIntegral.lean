import SigmaProbEntropy
import SigmaProbDeficitDomain

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

structure CalibratedGammaDensity (f : ℝ → ℝ) (ell : ℝ) : Prop where
  measurable : Measurable f
  nonnegative : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ f t
  mass : (∫ t : ℝ in Ioi 0, f t) = 1
  firstMoment : (∫ t : ℝ in Ioi 0, t*f t) = 2
  logIntegrable : IntegrableOn (fun t : ℝ => f t*Real.log t) (Ioi 0)
  logMoment : (∫ t : ℝ in Ioi 0, f t*Real.log t) = ell

theorem gamma_log_density (t : ℝ) (ht : 0 < t) :
    Real.log (SigmaPresentations.density t) = Real.log t-t := by
  rw [SigmaPresentations.density, Real.log_mul ht.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem CalibratedGammaDensity.integrable {f : ℝ → ℝ} {ell : ℝ}
    (h : CalibratedGammaDensity f ell) : IntegrableOn f (Ioi (0 : ℝ)) :=
  Integrable.of_integral_ne_zero (h.mass.trans_ne one_ne_zero)

theorem CalibratedGammaDensity.first_integrable {f : ℝ → ℝ} {ell : ℝ}
    (h : CalibratedGammaDensity f ell) :
    IntegrableOn (fun t : ℝ => t*f t) (Ioi (0 : ℝ)) :=
  Integrable.of_integral_ne_zero (h.firstMoment.trans_ne (by norm_num))

theorem CalibratedGammaDensity.cross_integrable {f : ℝ → ℝ} {ell : ℝ}
    (h : CalibratedGammaDensity f ell) :
    IntegrableOn (fun t : ℝ => f t*Real.log (SigmaPresentations.density t)) (Ioi (0 : ℝ)) := by
  apply (h.logIntegrable.sub h.first_integrable).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [gamma_log_density t ht]
  dsimp only [Pi.sub_apply]
  ring

theorem CalibratedGammaDensity.cross_entropy {f : ℝ → ℝ} {ell : ℝ}
    (h : CalibratedGammaDensity f ell) :
    (∫ t : ℝ in Ioi 0, f t*Real.log (SigmaPresentations.density t)) = ell-2 := by
  have he : (fun t : ℝ => f t*Real.log (SigmaPresentations.density t)) =ᵐ[
      volume.restrict (Ioi 0)] (fun t : ℝ => f t*Real.log t-t*f t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [gamma_log_density t ht]
    ring
  rw [integral_congr_ae he, integral_sub h.logIntegrable h.first_integrable,
    h.logMoment, h.firstMoment]

theorem gamma_entropy_defect_identity {p f : ℝ} (hp : 0 < p) (hf : 0 ≤ f) :
    p*entropyDefect (f/p) = f*Real.log f-f*Real.log p-f+p := by
  rcases hf.eq_or_lt with rfl | hf
  · simp [entropyDefect]
  · rw [entropyDefect, Real.log_div hf.ne' hp.ne']
    field_simp
    ring

theorem CalibratedGammaDensity.defect_integrable {f : ℝ → ℝ} {ell : ℝ}
    (h : CalibratedGammaDensity f ell)
    (hi : IntegrableOn (fun t : ℝ => f t*Real.log (f t)) (Ioi 0)) :
    IntegrableOn (fun t => SigmaPresentations.density t*entropyDefect (f t/SigmaPresentations.density t))
      (Ioi (0 : ℝ)) := by
  apply (((hi.sub h.cross_integrable).sub h.integrable).add intrinsic_density_integrable).congr
  filter_upwards [h.nonnegative, ae_restrict_mem measurableSet_Ioi] with t ht ht0
  exact (gamma_entropy_defect_identity (SigmaPresentations.density_pos ht0) ht).symm

theorem CalibratedGammaDensity.defect_integral {f : ℝ → ℝ} {ell : ℝ}
    (h : CalibratedGammaDensity f ell)
    (hi : IntegrableOn (fun t : ℝ => f t*Real.log (f t)) (Ioi 0)) :
    (∫ t : ℝ in Ioi 0, SigmaPresentations.density t*entropyDefect (f t/SigmaPresentations.density t)) =
      (∫ t : ℝ in Ioi 0, f t*Real.log (f t))+2-ell := by
  have he : (fun t => SigmaPresentations.density t*entropyDefect (f t/SigmaPresentations.density t)) =ᵐ[
      volume.restrict (Ioi 0)] (fun t => f t*Real.log (f t)-
      f t*Real.log (SigmaPresentations.density t)-f t+SigmaPresentations.density t) := by
    filter_upwards [h.nonnegative, ae_restrict_mem measurableSet_Ioi] with t ht ht0
    exact gamma_entropy_defect_identity (SigmaPresentations.density_pos ht0) ht
  have hsub : IntegrableOn (fun t => f t*Real.log (f t)-
      f t*Real.log (SigmaPresentations.density t)) (Ioi (0 : ℝ)) := hi.sub h.cross_integrable
  have hsub2 : IntegrableOn (fun t => f t*Real.log (f t)-
      f t*Real.log (SigmaPresentations.density t)-f t) (Ioi (0 : ℝ)) := hsub.sub h.integrable
  rw [integral_congr_ae he,
    integral_add hsub2 intrinsic_density_integrable,
    integral_sub hsub h.integrable,
    integral_sub hi h.cross_integrable, h.cross_entropy, h.mass, intrinsic_density_integral_one]
  ring

theorem CalibratedGammaDensity.finite_entropy_formula {f : ℝ → ℝ} {ell : ℝ}
    (h : CalibratedGammaDensity f ell)
    (hi : IntegrableOn (fun t : ℝ => f t*Real.log (f t)) (Ioi 0)) :
    calibratedExtendedEntropy (2-ell) f =
      ((-(∫ t : ℝ in Ioi 0, f t*Real.log (f t)) : ℝ) : EReal) := by
  have hpos : ∀ᵐ t ∂volume.restrict (Ioi 0),
      0 ≤ SigmaPresentations.density t*entropyDefect (f t/SigmaPresentations.density t) := by
    filter_upwards [h.nonnegative, ae_restrict_mem measurableSet_Ioi] with t ht ht0
    exact mul_nonneg (SigmaPresentations.density_pos ht0).le
      (entropy_defect_nonneg (div_nonneg ht (SigmaPresentations.density_pos ht0).le))
  have hd : gammaDensityDivergence f = ENNReal.ofReal
      ((∫ t : ℝ in Ioi 0, f t*Real.log (f t))+2-ell) := by
    rw [gammaDensityDivergence, ← ofReal_integral_eq_lintegral_ofReal
      (h.defect_integrable hi) hpos, h.defect_integral hi]
  have hv : 0 ≤ (∫ t : ℝ in Ioi 0, f t*Real.log (f t))+2-ell := by
    rw [← h.defect_integral hi]
    exact integral_nonneg_of_ae hpos
  rw [calibratedExtendedEntropy, hd, EReal.coe_ennreal_ofReal,
    max_eq_left (by exact_mod_cast hv), ← EReal.coe_sub]
  congr 1
  ring

end
end Sigma
