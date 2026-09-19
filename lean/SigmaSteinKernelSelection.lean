import SigmaSteinKernelInverse
import SigmaProbDeficitDomain

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem gamma_integrable_weak_stein_kernel_unique (τ : ℝ → ℝ)
    (hi : LocallyIntegrableOn (fun t => τ t*SigmaPresentations.density t) (Ioi 0) volume)
    (hw : WeakSteinKernel τ) (hL1 : Integrable τ gammaProbability) :
    ∀ᵐ t : ℝ, t ∈ Ioi 0 → τ t = t := by
  apply integrable_weak_stein_kernel_unique τ hi hw
  simpa only [mul_comm] using (gamma_density_integrability τ).mp hL1

theorem centered_integral_weak_stein_kernel_unique (τ : ℝ → ℝ)
    (hi : LocallyIntegrableOn (fun t => τ t*SigmaPresentations.density t) (Ioi 0) volume)
    (hw : WeakSteinKernel τ)
    (hc : (∫ t : ℝ in Ioi 0, τ t*SigmaPresentations.density t) = 2) :
    ∀ᵐ t : ℝ, t ∈ Ioi 0 → τ t = t := by
  apply integrable_weak_stein_kernel_unique τ hi hw
  by_contra hn
  rw [integral_undef hn] at hc
  norm_num at hc

theorem stein_kernel_flux_nonnegative_iff (C : ℝ) :
    (∀ᵐ t : ℝ, t ∈ Ioi 0 → 0 ≤ steinFlux t+C) ↔ 0 ≤ C := by
  constructor
  · intro hae
    have ha : (fun t => |steinFlux t+C|) =ᵐ[volume.restrict (Ioi 0)] (fun t => steinFlux t+C) := by
      filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mpr hae] with t ht
      exact abs_of_nonneg ht
    have hc : Continuous (fun t => steinFlux t+C) := steinFlux_contDiff.continuous.add continuous_const
    have he := Measure.eqOn_open_of_ae_eq ha isOpen_Ioi hc.abs.continuousOn hc.continuousOn
    apply ge_of_tendsto (stein_kernel_flux_endpoints C).2
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (abs_eq_self.mp (he ht))
  · intro hc
    filter_upwards with t
    intro ht
    exact add_nonneg (mul_nonneg (sq_nonneg t) (Real.exp_pos _).le) hc

theorem stein_kernel_family_nonnegative_iff (C : ℝ) :
    (∀ᵐ t : ℝ, t ∈ Ioi 0 → 0 ≤ steinKernelFamily C t) ↔ 0 ≤ C := by
  rw [← stein_kernel_flux_nonnegative_iff C]
  constructor
  · intro hh
    filter_upwards [hh] with t ht
    intro hp
    rw [← steinKernelFamily_flux C hp]
    exact mul_nonneg (ht hp) (mul_pos hp (Real.exp_pos _)).le
  · intro hh
    filter_upwards [hh] with t ht
    intro hp
    have hflux := ht hp
    rw [← steinKernelFamily_flux C hp] at hflux
    exact (mul_nonneg_iff_of_pos_right (mul_pos hp (Real.exp_pos _))).mp hflux

theorem stein_kernel_zero_flux_atTop_iff (C : ℝ) :
    Tendsto (fun t => steinFlux t+C) atTop (𝓝 0) ↔ C = 0 := by
  constructor
  · intro hh
    exact tendsto_nhds_unique (stein_kernel_flux_endpoints C).2 hh
  · rintro rfl
    simpa using steinFlux_tendsto_zero_atTop

theorem stein_kernel_zero_flux_at_zero_iff (C : ℝ) :
    Tendsto (fun t => steinFlux t+C) (𝓝[>] 0) (𝓝 0) ↔ C = 0 := by
  constructor
  · intro hh
    exact tendsto_nhds_unique (stein_kernel_flux_endpoints C).1 hh
  · rintro rfl
    simpa using steinFlux_tendsto_zero_at_zero

/-- The representative is globally smooth and satisfies the actual integral fundamental theorem
on every compact interval, in particular on every compact positive interval. -/
theorem stein_kernel_flux_representative_integral (C a b : ℝ) :
    IntervalIntegrable (fun t => (2-t)*SigmaPresentations.density t) volume a b ∧
      (steinFlux b+C)-(steinFlux a+C) = ∫ t : ℝ in a..b, (2-t)*SigmaPresentations.density t := by
  have hc : Continuous (fun t => (2-t)*SigmaPresentations.density t) :=
    (continuous_const.sub continuous_id).mul (continuous_id.mul continuous_id.neg.rexp)
  refine ⟨hc.intervalIntegrable a b, ?_⟩
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => (steinFlux_hasDerivAt t).add_const C) (hc.intervalIntegrable a b)

end
end Sigma
