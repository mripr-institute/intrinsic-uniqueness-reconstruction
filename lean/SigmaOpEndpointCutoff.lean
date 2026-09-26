import SigmaOpZeroEnergy

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- Cutting the second zero-energy solution with a smooth function whose
transition is in a compact interior set yields a maximal-domain representative
whenever the resulting function is L2. -/
theorem laguerre_zero_solution_cutoff_maximal
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport (deriv χ)) (hp : tsupport (deriv χ) ⊆ Ioi 0)
    (hi : Memℒp (fun t => χ t*laguerreSecondZeroSolution t) 2 gammaProbability) :
    ∃ x : laguerreCanonicalOperator.domain,
      (fun t => χ t*laguerreSecondZeroSolution t) =ᵐ[gammaProbability] (x.val : ℝ → ℂ) := by
  let U := laguerreSecondZeroSolution
  let F : ℝ → ℂ := fun t => χ t*U t
  let Q : ℝ → ℂ := fun t => ((steinFlux t : ℂ)*deriv χ t)*U t+χ t
  have hχd : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  have hqχ : ContDiff ℝ ∞ (fun t => (steinFlux t : ℂ)*deriv χ t) :=
    (Complex.ofRealCLM.contDiff.comp steinFlux_contDiff).mul hχd
  have hF : PositiveRayLocallyAbsolutelyContinuous F :=
    (smooth_positive_locally_ac hχ).mul laguerre_second_zero_locally_ac
  have hQ : PositiveRayLocallyAbsolutelyContinuous Q := by
    have hleft := (smooth_positive_locally_ac hqχ).mul laguerre_second_zero_locally_ac
    have hright := smooth_positive_locally_ac hχ
    have hneg : PositiveRayLocallyAbsolutelyContinuous (fun t => -χ t) := by
      exact smooth_positive_locally_ac hχ.neg
    apply (hleft.sub hneg).congr
    intro t _
    simp only [Q,sub_neg_eq_add]
  have hflux : EqOn (fun t => (steinFlux t : ℂ)*deriv F t) Q (Ioi 0) := by
    intro t ht
    have hd := ((hχ.differentiable (by simp) t).hasDerivAt).mul (laguerre_second_zero_hasDerivAt ht)
    dsimp only [F,U] at hd ⊢
    rw [hd.deriv]
    dsimp only [Q,U]
    field_simp [stein_flux_ne_zero ht]
    ring
  let H : ℝ → ℂ := fun t => opComplexLaguerreExpression χ t*U t-
    2*(SigmaPresentations.density t : ℂ)⁻¹*deriv χ t
  have hpcont : ContinuousOn (fun t => (SigmaPresentations.density t : ℂ)⁻¹) (Ioi 0) := by
    apply (Complex.continuous_ofReal.comp (continuous_id.mul continuous_id.neg.rexp)).continuousOn.inv₀
    intro t ht
    have hh : 0 < SigmaPresentations.density t := mul_pos ht (Real.exp_pos _)
    change (SigmaPresentations.density t : ℂ) ≠ 0
    exact_mod_cast hh.ne'
  have hHcont : ContinuousOn H (Ioi 0) :=
    ((op_complex_laguerre_expression_contDiff χ hχ).continuous.continuousOn.mul
      laguerre_second_zero_locally_ac.continuousOn).sub
      ((continuousOn_const.mul hpcont).mul hχd.continuous.continuousOn)
  have hHsupport : Function.support H ⊆ tsupport (deriv χ) := by
    intro t ht
    by_contra hn
    have hd : deriv χ t = 0 := image_eq_zero_of_nmem_tsupport hn
    have hdd : deriv (deriv χ) t = 0 := not_not.mp (fun h => hn (support_deriv_subset h))
    exact ht (by simp [H,opComplexLaguerreExpression,hd,hdd])
  obtain ⟨B,hB⟩ := hs.bddAbove_image ((hHcont.mono hp).norm)
  have hHbound (t : ℝ) : ‖H t‖ ≤ max B 0 := by
    by_cases ht : t ∈ tsupport (deriv χ)
    · exact (hB (mem_image_of_mem _ ht)).trans (le_max_left _ _)
    · have hz : H t=0 := not_not.mp (fun h => ht (hHsupport h))
      rw [hz,norm_zero]
      exact le_max_right _ _
  have hdiv {t : ℝ} (ht : 0 < t) : laguerreDivergenceExpression F t=H t := by
    have he : (fun t => (steinFlux t : ℂ)*deriv F t) =ᶠ[𝓝 t] Q := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      exact hflux hs
    have hd1 := (hqχ.differentiable (by simp) t).hasDerivAt
    rw [complex_flux_test_derivative χ hχ] at hd1
    have hd := (hd1.mul (laguerre_second_zero_hasDerivAt ht)).add
      ((hχ.differentiable (by simp) t).hasDerivAt)
    change HasDerivAt Q _ t at hd
    have hpd : (SigmaPresentations.density t : ℂ) ≠ 0 := by
      have hh : 0 < SigmaPresentations.density t := mul_pos ht (Real.exp_pos _)
      exact_mod_cast hh.ne'
    simp only [laguerreDivergenceExpression,he.deriv_eq,hd.deriv,H,U]
    field_simp [hpd,stein_flux_ne_zero ht]
    ring
  have hdivm : Memℒp (laguerreDivergenceExpression F) 2 gammaProbability := by
    refine Memℒp.of_bound ?_ (max B 0) ?_
    · exact (((Complex.continuous_ofReal.comp (continuous_id.mul continuous_id.neg.rexp)).measurable.inv.neg).mul
        (measurable_deriv (fun t => (steinFlux t : ℂ)*deriv F t))).aestronglyMeasurable
    · apply gamma_ae_iff_positive_volume_ae.mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [hdiv ht]
      exact hHbound t
  let x : LaguerreWeightedHilbert := hi.toLp F
  have hFx : F =ᵐ[gammaProbability] (x : ℝ → ℂ) := (Memℒp.coeFn_toLp hi).symm
  have hx : x ∈ laguerreCanonicalOperator.domain :=
    (laguerre_canonical_domain_iff_maximal x).mpr ⟨F,hFx,hF,hQ.congr hflux,hdivm⟩
  exact ⟨⟨x,hx⟩,hFx⟩

end
end Sigma
