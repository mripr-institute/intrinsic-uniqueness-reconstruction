import SigmaSteinMomentLimits
import SigmaSteinKernelSelection

namespace Sigma
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem weak_stein_density (μ : Measure ℝ) [IsProbabilityMeasure μ] (hw : WeakGammaStein μ) :
    μ = volume.withDensity ((Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal (SigmaPresentations.density t))) := by
  rw [(weak_stein_characterization μ).mp hw]
  unfold gammaProbability gammaMeasure
  congr 1
  funext t
  rw [gammaPDF,gamma_pdf_intrinsic]
  by_cases ht : 0 < t
  · simp [ht,ht.le]
  · by_cases he : t=0
    · subst t
      simp [SigmaPresentations.density]
    · have hn : ¬0 ≤ t := by intro hh; exact he (le_antisymm (le_of_not_gt ht) hh)
      simp [ht,hn]

theorem weak_stein_absolutely_continuous (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hw : WeakGammaStein μ) : μ ≪ volume := by
  rw [weak_stein_density μ hw]
  exact withDensity_absolutelyContinuous _ _

theorem weak_stein_positive_support (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hw : WeakGammaStein μ) : μ (Iic 0) = 0 := by
  rw [(weak_stein_characterization μ).mp hw,← Iio_union_right (a := (0 : ℝ)),
    measure_union (disjoint_singleton_right.mpr (by simp)) (measurableSet_singleton _),
    gamma_probability_negative_ray,gamma_probability_no_atom]
  simp

theorem weak_stein_no_atoms (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hw : WeakGammaStein μ) (t : ℝ) : μ {t} = 0 := by
  rw [(weak_stein_characterization μ).mp hw]
  exact gamma_probability_no_atom t

/-- The regular representative has the finite-interval epsilon-delta absolute-continuity
property. The stronger estimate allows overlapping intervals as well. -/
theorem stein_flux_representative_absolute_continuity (C a b : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ n : ℕ, ∀ l r : Fin n → ℝ,
      (∀ i, l i ∈ Icc a b ∧ r i ∈ Icc a b) →
      (∑ i, |r i-l i|) < δ →
      (∑ i, |(steinFlux (r i)+C)-(steinFlux (l i)+C)|) < ε := by
  have hc : Continuous (fun t => ‖(2-t)*SigmaPresentations.density t‖) :=
    ((continuous_const.sub continuous_id).mul (continuous_id.mul continuous_id.neg.exp)).norm
  obtain ⟨B,hB⟩ := (isCompact_Icc.image hc).bddAbove
  let K := |B|+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hbound : ∀ t ∈ Icc a b, ‖(2-t)*SigmaPresentations.density t‖ ≤ K := by
    intro t ht
    exact le_trans (hB (mem_image_of_mem _ ht)) (by dsimp [K]; linarith [le_abs_self B])
  intro ε hε
  refine ⟨ε/K,div_pos hε hK,?_⟩
  intro n l r hmem hsum
  calc
    (∑ i, |(steinFlux (r i)+C)-(steinFlux (l i)+C)|) ≤ ∑ i, K*|r i-l i| := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.norm_eq_abs] using
        (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
          (fun t _ => ((steinFlux_hasDerivAt t).add_const C).hasDerivWithinAt)
          hbound (hmem i).1 (hmem i).2
    _ = K*(∑ i, |r i-l i|) := (Finset.mul_sum _ _ _).symm
    _ < ε := by nlinarith [(lt_div_iff₀ hK).mp hsum]

theorem weak_stein_kernel_smooth_flux_representative (τ : ℝ → ℝ)
    (hi : LocallyIntegrableOn (fun t => τ t*SigmaPresentations.density t) (Ioi 0) volume)
    (hw : WeakSteinKernel τ) :
    ∃ C : ℝ,
      (∀ᵐ t : ℝ, t ∈ Ioi 0 → τ t*SigmaPresentations.density t = steinFlux t+C) ∧
      ContDiff ℝ ∞ (fun t => steinFlux t+C) ∧
      (∀ t, HasDerivAt (fun t => steinFlux t+C) ((2-t)*SigmaPresentations.density t) t) ∧
      Tendsto (fun t => steinFlux t+C) (𝓝[>] 0) (𝓝 C) ∧
      Tendsto (fun t => steinFlux t+C) atTop (𝓝 C) := by
  obtain ⟨C,hC⟩ := weak_stein_kernel_identifies_family τ hi hw
  refine ⟨C,?_,steinFlux_contDiff.add contDiff_const,
    fun t => (steinFlux_hasDerivAt t).add_const C,(stein_kernel_flux_endpoints C).1,
    (stein_kernel_flux_endpoints C).2⟩
  filter_upwards [hC] with t ht
  intro hp
  rw [ht hp,steinKernelFamily_flux C hp]

/-- Finite signed Lebesgue expectation uses its genuine finiteness predicate, not the
always-real value of a totalized integral. -/
theorem finite_expectation_weak_stein_kernel_unique (τ : ℝ → ℝ) (hm : Measurable τ)
    (hi : LocallyIntegrableOn (fun t => τ t*SigmaPresentations.density t) (Ioi 0) volume)
    (hw : WeakSteinKernel τ) (hfinite : HasFiniteIntegral τ gammaProbability) :
    ∀ᵐ t : ℝ, t ∈ Ioi 0 → τ t=t :=
  gamma_integrable_weak_stein_kernel_unique τ hi hw ⟨hm.aestronglyMeasurable,hfinite⟩

theorem weak_stein_kernel_continuous_representative_unique (τ v : ℝ → ℝ) (C : ℝ)
    (hC : ∀ᵐ t : ℝ, t ∈ Ioi 0 → τ t=steinKernelFamily C t)
    (hv : ContinuousOn v (Ioi 0))
    (ha : ∀ᵐ t : ℝ, t ∈ Ioi 0 → v t=τ t*SigmaPresentations.density t) :
    EqOn v (fun t => steinFlux t+C) (Ioi 0) := by
  apply Measure.eqOn_open_of_ae_eq (μ := volume) _ isOpen_Ioi hv
    (steinFlux_contDiff.continuous.add continuous_const).continuousOn
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards [hC,ha] with t hct hat
  intro ht
  rw [hat ht,hct ht,steinKernelFamily_flux C ht]

theorem zero_endpoint_weak_stein_kernel_unique (τ v : ℝ → ℝ)
    (hi : LocallyIntegrableOn (fun t => τ t*SigmaPresentations.density t) (Ioi 0) volume)
    (hw : WeakSteinKernel τ) (hv : ContinuousOn v (Ioi 0))
    (ha : ∀ᵐ t : ℝ, t ∈ Ioi 0 → v t=τ t*SigmaPresentations.density t)
    (hz : Tendsto v (𝓝[>] 0) (𝓝 0) ∨ Tendsto v atTop (𝓝 0)) :
    ∀ᵐ t : ℝ, t ∈ Ioi 0 → τ t=t := by
  obtain ⟨C,hC⟩ := weak_stein_kernel_identifies_family τ hi hw
  have he := weak_stein_kernel_continuous_representative_unique τ v C hC hv ha
  have hc0 : C=0 := by
    rcases hz with hz | hz
    · apply (stein_kernel_zero_flux_at_zero_iff C).mp
      apply hz.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact he ht
    · apply (stein_kernel_zero_flux_atTop_iff C).mp
      apply hz.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact he ht
  subst C
  filter_upwards [hC] with t ht
  intro hp
  simpa [steinKernelFamily] using ht hp

theorem weak_stein_kernel_integrable_iff_canonical (τ : ℝ → ℝ)
    (hi : LocallyIntegrableOn (fun t => τ t*SigmaPresentations.density t) (Ioi 0) volume)
    (hw : WeakSteinKernel τ) :
    Integrable τ gammaProbability ↔ ∀ᵐ t : ℝ, t ∈ Ioi 0 → τ t=t := by
  constructor
  · exact gamma_integrable_weak_stein_kernel_unique τ hi hw
  · intro hh
    apply (gamma_density_integrability τ).mpr
    apply steinFlux_integrable.congr
    filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mpr hh] with t ht
    simp only [ht,SigmaPresentations.density,steinFlux]
    ring

end
end Sigma
