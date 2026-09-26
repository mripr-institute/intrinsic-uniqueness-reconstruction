import SigmaOpACIntegrationByParts
import SigmaSteinWeakZero

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

set_option maxHeartbeats 800000 in
/-- The complex-valued distributional constant theorem on the positive ray. -/
theorem complex_zero_weak_derivative_constant (u : ℝ → ℂ)
    (hu : LocallyIntegrableOn u (Ioi 0) volume)
    (hw : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ Ioi 0 →
      (∫ t : ℝ, u t * ((deriv f t : ℝ) : ℂ)) = 0) :
    ∃ C : ℂ, u =ᵐ[volume.restrict (Ioi 0)] (fun _ => C) := by
  have hr : LocallyIntegrableOn (fun t => (u t).re) (Ioi 0) volume := by
    intro t ht
    obtain ⟨s,hs,hi⟩ := hu t ht
    exact ⟨s,hs,Complex.reCLM.integrable_comp hi⟩
  have hi : LocallyIntegrableOn (fun t => (u t).im) (Ioi 0) volume := by
    intro t ht
    obtain ⟨s,hs,hi⟩ := hu t ht
    exact ⟨s,hs,Complex.imCLM.integrable_comp hi⟩
  have hpair (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
      (hp : tsupport f ⊆ Ioi 0) : Integrable (fun t => u t*((deriv f t : ℝ) : ℂ)) := by
    have hd : Continuous (fun t => ((deriv f t : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (contDiff_infty_iff_deriv.mp hf).2.continuous
    have hc : HasCompactSupport (fun t => ((deriv f t : ℝ) : ℂ)) := hs.deriv.comp_left (show (Complex.ofReal : ℝ → ℂ) 0 = 0 from Complex.ofReal_zero)
    have ht : tsupport (fun t => ((deriv f t : ℝ) : ℂ)) ⊆ Ioi 0 := by
      apply (closure_minimal ?_ isClosed_closure).trans hp
      intro t ht
      exact support_deriv_subset (fun h => ht (by simp [h]))
    exact complex_local_test_product_integrable u _ hu hd hc ht
  obtain ⟨a,ha⟩ := stein_zero_weak_derivative_constant (fun t => (u t).re) hr (by
    intro f hf hs hp
    have he := Complex.reCLM.integral_comp_comm (hpair f hf hs hp)
    simpa only [Complex.reCLM_apply,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,sub_zero,hw f hf hs hp,Complex.zero_re] using he)
  obtain ⟨b,hb⟩ := stein_zero_weak_derivative_constant (fun t => (u t).im) hi (by
    intro f hf hs hp
    have he := Complex.imCLM.integral_comp_comm (hpair f hf hs hp)
    simpa only [Complex.imCLM_apply,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,zero_add,hw f hf hs hp,Complex.zero_im] using he)
  refine ⟨⟨a,b⟩,?_⟩
  change ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), u t = ⟨a,b⟩
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [ha,hb] with t hr hi ht
  exact Complex.ext (hr ht) (hi ht)


/-- A locally integrable complex function with locally integrable weak
first derivative has a genuine locally AC representative of its class. -/
theorem complex_weak_derivative_regular_representative (u g : ℝ → ℂ)
    (hu : LocallyIntegrableOn u (Ioi 0) volume)
    (hg : LocallyIntegrableOn g (Ioi 0) volume)
    (hw : ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ Ioi 0 →
      (∫ t : ℝ, u t * deriv f t) + (∫ t : ℝ, g t*f t) = 0) :
    ∃ U : ℝ → ℂ, U =ᵐ[volume.restrict (Ioi 0)] u ∧
      PositiveRayLocallyAbsolutelyContinuous U ∧
      ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), HasDerivAt U (g t) t := by
  let P : ℝ → ℂ := fun t => ∫ s in (1:ℝ)..t, g s
  have hP : PositiveRayLocallyAbsolutelyContinuous P := by
    intro l r hl ε hε
    exact positive_primitive_absolute_continuity g hg (by norm_num) hl ε hε
  have hPl : LocallyIntegrableOn P (Ioi 0) volume :=
    hP.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hPd : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), HasDerivAt P (g t) t :=
    positive_primitive_hasDerivAt_ae g hg (by norm_num)
  obtain ⟨C,hC⟩ := complex_zero_weak_derivative_constant (fun t => u t-P t) (hu.sub hPl) (by
    intro f hf hs hp
    let w : ℝ → ℂ := fun t => (f t : ℂ)
    have hwc : ContDiff ℝ ∞ w := Complex.ofRealCLM.contDiff.comp hf
    have hws : HasCompactSupport w := hs.comp_left (show (Complex.ofReal : ℝ → ℂ) 0=0 from rfl)
    have hwp : tsupport w ⊆ Ioi 0 := by
      apply (closure_minimal ?_ isClosed_closure).trans hp
      intro t ht
      apply subset_closure
      exact fun hz => ht (by simp [w,hz])
    have hwd (t : ℝ) : deriv w t = ((deriv f t : ℝ) : ℂ) :=
      (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t ((hf.differentiable (by simp) t).hasDerivAt)).deriv
    have heP := hP.compact_integration_by_parts hg hPd w hwc hws hwp
    have heU := hw w hwc hws hwp
    have hds : tsupport (deriv w) ⊆ Ioi 0 :=
      (closure_minimal support_deriv_subset isClosed_closure).trans hwp
    have hui := complex_local_test_product_integrable u (deriv w) hu
      (contDiff_infty_iff_deriv.mp hwc).2.continuous hws.deriv hds
    have hPi := complex_local_test_product_integrable P (deriv w) hPl
      (contDiff_infty_iff_deriv.mp hwc).2.continuous hws.deriv hds
    have hd : (fun t => (u t-P t)*((deriv f t : ℝ) : ℂ)) =
        (fun t => u t*deriv w t-P t*deriv w t) := by
      funext t
      rw [hwd]
      ring
    rw [hd,integral_sub hui hPi]
    linear_combination heU-heP)
  refine ⟨fun t => C+P t,?_,hP.const_add C,?_⟩
  · filter_upwards [hC] with t ht
    change u t-P t=C at ht
    linear_combination -ht
  · filter_upwards [hPd] with t ht
    exact ht.const_add C

end
end Sigma
