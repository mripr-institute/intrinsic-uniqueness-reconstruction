import SigmaOperatorPearson

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

/-- Pearson in the standard locally absolutely continuous flux-representative
category. Coefficients are allowed to be arbitrary representatives of their a.e.
classes: the raw product `a * w` need not itself be continuous or differentiable.
Neither the canonical coefficients nor the target weight occur in this category
definition. -/
def HasLocalACPearsonFlux (a b w : ℝ → ℝ) : Prop :=
  ∃ F : ℝ → ℝ, LocallyIntegralAbsolutelyContinuousPositive F ∧
    (∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), F t = a t*w t) ∧
    ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), HasDerivAt F (b t*w t) t

/-- The continuous flux representative is determined pointwise by its a.e.
class after coefficient reconstruction. No derivative of the raw `a * w` is
assumed, even at almost every point. -/
theorem local_ac_pearson_representative_canonical (a b w : ℝ → ℝ)
    (hw : LocallyIntegralAbsolutelyContinuousPositive w)
    (hab : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), a t = t ∧ b t = 2-t)
    (hP : HasLocalACPearsonFlux a b w) :
    ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      HasDerivAt (fun s => s*w s) ((2-t)*w t) t := by
  obtain ⟨F, hF, hFe, hFd⟩ := hP
  have he : F =ᵐ[volume.restrict (Ioi (0:ℝ))] (fun t => t*w t) := by
    filter_upwards [hFe, hab] with t ht hc
    simpa only [hc.1] using ht
  have hcF : ContinuousOn F (Ioi (0:ℝ)) := fun t ht =>
    (local_integral_ac_continuousAt F hF ht).continuousWithinAt
  have hcw : ContinuousOn w (Ioi (0:ℝ)) := fun t ht =>
    (local_integral_ac_continuousAt w hw ht).continuousWithinAt
  have heq := Measure.eqOn_open_of_ae_eq he isOpen_Ioi hcF (continuousOn_id.mul hcw)
  filter_upwards [hFd, hab, ae_restrict_mem measurableSet_Ioi] with t hd hc ht
  have hevent : (fun s => s*w s) =ᶠ[nhds t] F := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (heq hs).symm
  simpa only [hc.2] using hd.congr_of_eventuallyEq hevent

/-- Exact a.e.-coefficient two-probe reconstruction for a locally AC weight
and a locally AC Pearson flux representative. The conclusion includes the
actual normalized measure, not just a scalar solution of the ODE. -/
theorem operator_two_probe_pearson_representative_inverse_ae (a b w : ℝ → ℝ)
    (hw : LocallyIntegralAbsolutelyContinuousPositive w)
    (hmass : (∫ t : ℝ in Ioi 0, w t) = 1)
    (hl : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), opExpression a b opLinearProbe t = 2-t)
    (hq : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), opExpression a b opQuadraticProbe t = t^2-6*t+6)
    (hP : HasLocalACPearsonFlux a b w) :
    (∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), a t = t ∧ b t = 2-t) ∧
      (∀ t > 0, w t = SigmaPresentations.density t) ∧
      volume.withDensity ((Ioi (0:ℝ)).indicator (fun t => ENNReal.ofReal (w t))) = gammaProbability := by
  have hc := (operator_two_probe_ae_iff (volume.restrict (Ioi (0:ℝ))) a b).mp ⟨hl, hq⟩
  have hp := local_ac_pearson_representative_canonical a b w hw hc hP
  exact ⟨hc, local_ac_pearson_density_unique w hw hp hmass,
    local_ac_pearson_weight_measure w hw hp hmass⟩

theorem operator_two_probe_pearson_representative_inverse (a b w : ℝ → ℝ)
    (hw : LocallyIntegralAbsolutelyContinuousPositive w)
    (hmass : (∫ t : ℝ in Ioi 0, w t) = 1)
    (hl : ∀ t > 0, opExpression a b opLinearProbe t = 2-t)
    (hq : ∀ t > 0, opExpression a b opQuadraticProbe t = t^2-6*t+6)
    (hP : HasLocalACPearsonFlux a b w) :
    (∀ t > 0, a t = t ∧ b t = 2-t) ∧
      (∀ t > 0, w t = SigmaPresentations.density t) ∧
      volume.withDensity ((Ioi (0:ℝ)).indicator (fun t => ENNReal.ofReal (w t))) = gammaProbability := by
  have hc := (operator_two_probe_iff a b).mp ⟨hl, hq⟩
  have hcae : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), a t = t ∧ b t = 2-t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hc t ht
  have hp := local_ac_pearson_representative_canonical a b w hw hcae hP
  exact ⟨hc, local_ac_pearson_density_unique w hw hp hmass,
    local_ac_pearson_weight_measure w hw hp hmass⟩

/-- The canonical smooth flux belongs to the representative category. -/
theorem canonical_density_has_local_ac_pearson_flux :
    HasLocalACPearsonFlux id (fun t => 2-t) SigmaPresentations.density := by
  let F : ℝ → ℝ := fun t => t*SigmaPresentations.density t
  let g : ℝ → ℝ := fun t => (2-t)*SigmaPresentations.density t
  have hd (t : ℝ) : HasDerivAt F (g t) t := operator_pearson_flux_derivative t
  have hg : Continuous g := by
    dsimp [g, SigmaPresentations.density]
    fun_prop
  refine ⟨F, ?_, Eventually.of_forall (fun _ => rfl), Eventually.of_forall hd⟩
  intro a b _ _
  refine ⟨g, hg.integrableOn_Icc, Eventually.of_forall hd, ?_⟩
  intro t _
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hd x) (hg.intervalIntegrable a t)
  linarith

end
end Sigma
