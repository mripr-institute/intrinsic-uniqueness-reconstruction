import SigmaProbPoissonClock
import SigmaProbCompletion
import Mathlib.Probability.CDF

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

/-- Lower quantile of the actual cumulative distribution function. -/
def gammaProcessQuantile (μ : Measure ℝ) (u : ℝ) : ℝ := sInf {x | u ≤ cdf μ x}

theorem gamma_process_quantile_set_nonempty (μ : Measure ℝ) {u : ℝ} (hu : u < 1) :
    ({x | u ≤ cdf μ x} : Set ℝ).Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds hu)).exists
  exact ⟨x, hx.le⟩

theorem gamma_process_quantile_set_bddBelow (μ : Measure ℝ) {u : ℝ} (hu : 0 < u) :
    BddBelow ({x | u ≤ cdf μ x} : Set ℝ) := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually (gt_mem_nhds hu)).exists
  refine ⟨a, ?_⟩
  intro x hx
  by_contra hn
  have hh := monotone_cdf μ (le_of_lt (lt_of_not_ge hn))
  exact (not_le_of_gt ha) (hx.trans hh)

theorem gamma_process_quantile_le_iff (μ : Measure ℝ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (a : ℝ) : gammaProcessQuantile μ u ≤ a ↔ u ≤ cdf μ a := by
  have hb := gamma_process_quantile_set_bddBelow μ hu.1
  have hn := gamma_process_quantile_set_nonempty μ hu.2
  constructor
  · intro hqa
    by_contra hlt
    have hh : cdf μ a < u := lt_of_not_ge hlt
    have ht : Tendsto (cdf μ) (𝓝[>] a) (𝓝 (cdf μ a)) :=
      ((cdf μ).right_continuous a).mono Ioi_subset_Ici_self
    have hnb : (𝓝[Ioi a] a).NeBot := nhdsWithin_Ioi_neBot (le_refl a)
    have hmem : ∀ᶠ b in 𝓝[Ioi a] a, b ∈ Ioi a := self_mem_nhdsWithin
    have hev : ∀ᶠ b in 𝓝[Ioi a] a, b ∈ Ioi a ∧ cdf μ b < u :=
      hmem.and (ht.eventually (gt_mem_nhds hh))
    obtain ⟨b, hab, hbu⟩ := @Filter.Eventually.exists _ _ _ hnb hev
    have hbq : b ≤ gammaProcessQuantile μ u := by
      apply le_csInf hn
      intro x hx
      by_contra hxb
      have hx' := monotone_cdf μ (le_of_lt (lt_of_not_ge hxb))
      exact (not_le_of_gt hbu) (hx.trans hx')
    exact (not_le_of_gt hab) (hbq.trans hqa)
  · exact fun ha => csInf_le hb ha

/-- Endpoint values are harmless garbage values; all interior uniform inputs
use the genuine lower quantile. -/
def gammaProcessRealSampler (μ : Measure ℝ) (u : ℝ) : ℝ :=
  if u ∈ Ioo (0 : ℝ) 1 then gammaProcessQuantile μ u else 0

theorem gamma_process_real_sampler_measurable (μ : Measure ℝ) :
    Measurable (gammaProcessRealSampler μ) := by
  apply measurable_of_Iic
  intro a
  have he : gammaProcessRealSampler μ ⁻¹' Iic a =
      (Ioo (0 : ℝ) 1 ∩ Iic (cdf μ a)) ∪ (if 0 ≤ a then (Ioo (0 : ℝ) 1)ᶜ else ∅) := by
    ext u
    by_cases hu : u ∈ Ioo (0 : ℝ) 1
    · simp [gammaProcessRealSampler, hu, gamma_process_quantile_le_iff μ hu a]
    · simp [gammaProcessRealSampler, hu]
  rw [he]
  exact (measurableSet_Ioo.inter measurableSet_Iic).union
    (by split_ifs <;> measurability)

/-- Exact inverse-CDF sampling for every real probability measure, using one
uniform input. No density, continuity, or strict positivity is assumed. -/
theorem gamma_process_real_sampler_map (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (volume.restrict (Ioc (0 : ℝ) 1)).map (gammaProcessRealSampler μ) = μ := by
  apply Measure.ext_of_Iic
  intro a
  rw [Measure.map_apply (gamma_process_real_sampler_measurable μ) measurableSet_Iic]
  have he : (gammaProcessRealSampler μ ⁻¹' Iic a) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      Iic (cdf μ a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (show ∀ᵐ u : ℝ ∂volume, u ≠ 1 from ae_iff.mpr (by simp))] with u hu hu1
    have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, lt_of_le_of_ne hu.2 hu1⟩
    change (gammaProcessRealSampler μ u ≤ a) = (u ≤ cdf μ a)
    simp only [gammaProcessRealSampler, if_pos hu']
    exact propext (gamma_process_quantile_le_iff μ hu' a)
  rw [measure_congr he, Measure.restrict_apply measurableSet_Iic]
  have hs : Iic (cdf μ a) ∩ Ioc (0 : ℝ) 1 = Ioc 0 (cdf μ a) := by
    ext u
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨h, hu, _⟩
      exact ⟨hu, h⟩
    · rintro ⟨hu, h⟩
      exact ⟨h, hu, h.trans (cdf_le_one μ a)⟩
  rw [hs, Real.volume_Ioc, sub_zero, ofReal_cdf]

def gammaProcessCircleSampler (μ : Measure ℝ) (z : AddCircle (1 : ℝ)) : ℝ :=
  gammaProcessRealSampler μ (poissonCircleUniform z)

theorem gamma_process_circle_sampler_measurable (μ : Measure ℝ) :
    Measurable (gammaProcessCircleSampler μ) :=
  (gamma_process_real_sampler_measurable μ).comp poissonCircleUniform_measurable

theorem gamma_process_circle_sampler_map (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (volume : Measure (AddCircle (1 : ℝ))).map (gammaProcessCircleSampler μ) = μ := by
  change (volume : Measure (AddCircle (1 : ℝ))).map
    (gammaProcessRealSampler μ ∘ poissonCircleUniform) = μ
  rw [← Measure.map_map (gamma_process_real_sampler_measurable μ)
    poissonCircleUniform_measurable, poissonCircleUniform_map, gamma_process_real_sampler_map]

/-- Countably many independent prescribed real laws on the existing compact
Haar probability space. -/
def gammaProcessIndependentSamples (μ : ℕ → Measure ℝ) (n : ℕ) (ω : PoissonClockSpace) : ℝ :=
  gammaProcessCircleSampler (μ n) (ω n)

theorem gamma_process_samples_measurable (μ : ℕ → Measure ℝ) (n : ℕ) :
    Measurable (gammaProcessIndependentSamples μ n) :=
  (gamma_process_circle_sampler_measurable (μ n)).comp (measurable_pi_apply n)

theorem gamma_process_samples_independent (μ : ℕ → Measure ℝ) :
    iIndepFun (fun _ : ℕ => inferInstance) (gammaProcessIndependentSamples μ) poissonClockProbability :=
  poissonClockCoordinates_independent.comp (fun n => gammaProcessCircleSampler (μ n))
    (fun n => gamma_process_circle_sampler_measurable (μ n))

theorem gamma_process_samples_law (μ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (μ n)] (n : ℕ) :
    poissonClockProbability.map (gammaProcessIndependentSamples μ n) = μ n := by
  change poissonClockProbability.map (gammaProcessCircleSampler (μ n) ∘ (fun ω => ω n)) = μ n
  rw [← Measure.map_map (gamma_process_circle_sampler_measurable (μ n))
    (measurable_pi_apply n), poissonClockCoordinate_map, gamma_process_circle_sampler_map]

end
end Sigma
