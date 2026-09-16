import SigmaSteinWeakZero
import SigmaSteinKernelForward

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem stein_derivative_test_pair_integral (u f : ℝ → ℝ)
    (hp : tsupport f ⊆ Ioi 0) :
    (∫ t : ℝ in Ioi 0, u t*deriv f t) = ∫ t : ℝ, u t*deriv f t := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have hz : deriv f t = 0 := by
    by_contra hn
    exact ht (hp (support_deriv_subset (show t ∈ Function.support (deriv f) from hn)))
  rw [hz,mul_zero]

theorem steinFlux_weak_derivative :
    WeakDerivativePositive steinFlux (fun t => (2-t)*SigmaPresentations.density t) := by
  have hh := stein_kernel_family_weak 0
  have he : (fun t => steinKernelFamily 0 t * SigmaPresentations.density t) = steinFlux := by
    funext t
    simp only [steinKernelFamily, zero_mul, zero_div, add_zero, SigmaPresentations.density, steinFlux]
    ring
  change WeakDerivativePositive (fun t => steinKernelFamily 0 t * SigmaPresentations.density t) _ at hh
  rwa [he] at hh

/-- Exact weak O1-kernel family, with local integrability only; no density regularity is assumed. -/
theorem weak_stein_kernel_identifies_family (τ : ℝ → ℝ)
    (hi : LocallyIntegrableOn (fun t => τ t*SigmaPresentations.density t) (Ioi 0) volume)
    (hw : WeakSteinKernel τ) :
    ∃ C : ℝ, ∀ᵐ t : ℝ, t ∈ Ioi 0 → τ t = steinKernelFamily C t := by
  let u : ℝ → ℝ := fun t => τ t*SigmaPresentations.density t-steinFlux t
  have hu : LocallyIntegrableOn u (Ioi 0) volume :=
    hi.sub (steinFlux_contDiff.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
  obtain ⟨C,hC⟩ := stein_zero_weak_derivative_constant u hu (by
    intro f hf hs hp
    have hfd : tsupport (deriv f) ⊆ Ioi 0 :=
      (closure_minimal support_deriv_subset (isClosed_tsupport f)).trans hp
    have hiτ := stein_local_test_product_integrable (fun t => τ t*SigmaPresentations.density t)
      (deriv f) hi (hf.continuous_deriv (by simp)) hs.deriv hfd
    have hiq := stein_local_test_product_integrable steinFlux (deriv f)
      (steinFlux_contDiff.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
      (hf.continuous_deriv (by simp)) hs.deriv hfd
    have hh := hw f hf hs hp
    have hq := steinFlux_weak_derivative f hf hs hp
    rw [stein_derivative_test_pair_integral _ f hp] at hh hq
    have he : (fun t => u t*deriv f t) =
        (fun t => (τ t*SigmaPresentations.density t)*deriv f t-steinFlux t*deriv f t) := by
      funext t
      dsimp [u]
      ring
    rw [he,integral_sub hiτ hiq,hh,hq,sub_self])
  refine ⟨C,?_⟩
  filter_upwards [hC] with t ht
  intro hp
  have ht0 : 0 < t := hp
  have hd : 0 < SigmaPresentations.density t := mul_pos ht0 (Real.exp_pos _)
  have he := ht hp
  dsimp [u] at he
  apply (mul_left_inj' (ne_of_gt hd)).mp
  rw [steinKernelFamily_flux C ht0]
  linarith

theorem weak_stein_kernel_of_family_ae (τ : ℝ → ℝ) (C : ℝ)
    (hτ : ∀ᵐ t : ℝ, t ∈ Ioi 0 → τ t = steinKernelFamily C t) : WeakSteinKernel τ := by
  intro f hf hs hp
  have hh := stein_kernel_family_weak C f hf hs hp
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mpr hτ] with t ht
  rw [ht]

theorem weak_stein_kernel_iff_family (τ : ℝ → ℝ)
    (hi : LocallyIntegrableOn (fun t => τ t*SigmaPresentations.density t) (Ioi 0) volume) :
    WeakSteinKernel τ ↔ ∃ C : ℝ, ∀ᵐ t : ℝ, t ∈ Ioi 0 → τ t = steinKernelFamily C t := by
  constructor
  · exact weak_stein_kernel_identifies_family τ hi
  · rintro ⟨C,hC⟩
    exact weak_stein_kernel_of_family_ae τ C hC

theorem integrable_weak_stein_kernel_unique (τ : ℝ → ℝ)
    (hi : LocallyIntegrableOn (fun t => τ t*SigmaPresentations.density t) (Ioi 0) volume)
    (hw : WeakSteinKernel τ)
    (hL1 : IntegrableOn (fun t => τ t*SigmaPresentations.density t) (Ioi 0)) :
    ∀ᵐ t : ℝ, t ∈ Ioi 0 → τ t = t := by
  obtain ⟨C,hC⟩ := weak_stein_kernel_identifies_family τ hi hw
  have hfamily : IntegrableOn (fun t => steinKernelFamily C t*SigmaPresentations.density t) (Ioi 0) := by
    apply hL1.congr
    filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mpr hC] with t ht
    rw [ht]
  have hc0 := (stein_kernel_family_weighted_integrable_iff C).mp hfamily
  subst C
  filter_upwards [hC] with t ht
  intro hp
  simpa [steinKernelFamily] using ht hp

end
end Sigma
