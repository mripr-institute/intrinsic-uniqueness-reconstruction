import SigmaStein

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The literal weak derivative equation on the positive ray, tested by C_c^infinity. -/
def WeakDerivativePositive (u v : ℝ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ Ioi 0 →
    (∫ t : ℝ in Ioi 0, u t * deriv f t) = -(∫ t : ℝ in Ioi 0, v t * f t)

def WeakSteinKernel (τ : ℝ → ℝ) : Prop :=
  WeakDerivativePositive (fun t => τ t * SigmaPresentations.density t)
    (fun t => (2-t)*SigmaPresentations.density t)

theorem stein_kernel_family_locally_integrable (C : ℝ) :
    LocallyIntegrableOn (fun t => steinKernelFamily C t * SigmaPresentations.density t) (Ioi 0) volume := by
  have hc : ContinuousOn (fun t => steinKernelFamily C t * SigmaPresentations.density t) (Ioi 0) := by
    apply (steinFlux_contDiff.continuous.add (continuous_const (y := C))).continuousOn.congr
    intro t ht
    exact steinKernelFamily_flux C ht
  exact hc.locallyIntegrableOn measurableSet_Ioi

theorem stein_kernel_family_weak (C : ℝ) : WeakSteinKernel (steinKernelFamily C) := by
  intro f hf hs hpos
  have h0 : f 0 = 0 := by
    apply image_eq_zero_of_nmem_tsupport
    intro hh
    have hn : (0 : ℝ) < 0 := hpos hh
    linarith
  have hfc : ContDiff ℝ 1 (fun t => (steinFlux t+C)*f t) :=
    ((steinFlux_contDiff.add contDiff_const).mul hf).of_le (by simp)
  have hh := HasCompactSupport.integral_Ioi_deriv_eq hfc hs.mul_left (0 : ℝ)
  have hd : (fun t => deriv (fun t => (steinFlux t+C)*f t) t) =
      (fun t => (steinFlux t+C)*deriv f t + ((2-t)*SigmaPresentations.density t)*f t) := by
    funext t
    rw [(((steinFlux_hasDerivAt t).add_const C).mul ((hf.differentiable (by simp) t).hasDerivAt)).deriv]
    ring
  rw [hd] at hh
  have hi1 : IntegrableOn (fun t => (steinFlux t+C)*deriv f t) (Ioi 0) :=
    ((steinFlux_contDiff.continuous.add continuous_const).mul (hf.continuous_deriv (by simp))).integrable_of_hasCompactSupport
      hs.deriv.mul_left |>.integrableOn
  have hi2 : IntegrableOn (fun t => ((2-t)*SigmaPresentations.density t)*f t) (Ioi 0) := by
    apply Continuous.integrable_of_hasCompactSupport _ hs.mul_left |>.integrableOn
    exact ((continuous_const.sub continuous_id).mul
      (continuous_id.mul continuous_id.neg.rexp)).mul hf.continuous
  rw [integral_add hi1 hi2, h0, mul_zero, neg_zero] at hh
  have he : (∫ t : ℝ in Ioi 0, steinKernelFamily C t * SigmaPresentations.density t * deriv f t) =
      ∫ t : ℝ in Ioi 0, (steinFlux t+C)*deriv f t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [steinKernelFamily_flux C ht]
  rw [he]
  linarith

theorem stein_kernel_flux_endpoints (C : ℝ) :
    Tendsto (fun t => steinFlux t+C) (𝓝[>] 0) (𝓝 C) ∧
      Tendsto (fun t => steinFlux t+C) atTop (𝓝 C) := by
  constructor
  · simpa using steinFlux_tendsto_zero_at_zero.add_const C
  · simpa using steinFlux_tendsto_zero_atTop.add_const C

theorem stein_kernel_flux_integrable_iff (C : ℝ) :
    IntegrableOn (fun t => steinFlux t+C) (Ioi 0) ↔ C = 0 := by
  constructor
  · intro hi
    have hconst : IntegrableOn (fun _ : ℝ => C) (Ioi 0) := by
      have hh : Integrable (fun t => (steinFlux t+C)-steinFlux t) (volume.restrict (Ioi 0)) :=
        hi.sub steinFlux_integrable
      simpa only [add_sub_cancel_left] using hh
    simpa [IntegrableOn, integrable_const_iff, Measure.restrict_apply_univ, Real.volume_Ioi] using hconst
  · rintro rfl
    simpa using steinFlux_integrable

theorem stein_kernel_family_weighted_integrable_iff (C : ℝ) :
    IntegrableOn (fun t => steinKernelFamily C t * SigmaPresentations.density t) (Ioi 0) ↔ C = 0 := by
  rw [← stein_kernel_flux_integrable_iff C]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact steinKernelFamily_flux C ht

end
end Sigma
