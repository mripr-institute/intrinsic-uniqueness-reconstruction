import SigmaProbGammaProcessSampler
import SigmaProbGammaProcessGroups

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal

/-- Arbitrarily indexed real laws sampled from distinct coordinates of the
concrete countable Haar probability space. -/
def gammaProcessEmbeddedSamples {ι : Type*} (μ : ι → Measure ℝ) (e : ι ↪ ℕ)
    (i : ι) (ω : PoissonClockSpace) : ℝ := gammaProcessCircleSampler (μ i) (ω (e i))

theorem gamma_process_embedded_samples_measurable {ι : Type*} (μ : ι → Measure ℝ)
    (e : ι ↪ ℕ) (i : ι) : Measurable (gammaProcessEmbeddedSamples μ e i) :=
  (gamma_process_circle_sampler_measurable (μ i)).comp (measurable_pi_apply (e i))

theorem gamma_process_embedded_samples_law {ι : Type*} (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (e : ι ↪ ℕ) (i : ι) :
    poissonClockProbability.map (gammaProcessEmbeddedSamples μ e i) = μ i := by
  change poissonClockProbability.map (gammaProcessCircleSampler (μ i) ∘ (fun ω => ω (e i))) = μ i
  rw [← Measure.map_map (gamma_process_circle_sampler_measurable (μ i))
    (measurable_pi_apply (e i)), poissonClockCoordinate_map, gamma_process_circle_sampler_map]

theorem gamma_process_embedded_samples_independent {ι : Type*} (μ : ι → Measure ℝ)
    (e : ι ↪ ℕ) : iIndepFun (fun _ : ι => inferInstance)
      (gammaProcessEmbeddedSamples μ e) poissonClockProbability := by
  classical
  have hi := poissonClockCoordinates_independent.comp (fun _ => poissonCircleUniform)
    (fun _ => poissonCircleUniform_measurable)
  have hs : Pairwise (fun i j : ι => Disjoint ({e i} : Finset ℕ) {e j}) := by
    intro i j hij
    simpa only [Finset.disjoint_singleton] using (fun he => hij (e.injective he))
  exact gamma_process_independent_finite_groups poissonClockProbability
    (fun n ω => poissonCircleUniform (ω n))
    (fun n => poissonCircleUniform_measurable.comp (measurable_pi_apply n)) hi
    (fun i => {e i}) hs
    (fun i z => gammaProcessRealSampler (μ i) (z ⟨e i, Finset.mem_singleton_self _⟩))
    (fun i => (gamma_process_real_sampler_measurable (μ i)).comp (measurable_pi_apply _))

/-- An actual independent family of Gamma increments of any assigned durations
at every label embedded into the natural-number source. -/
theorem gamma_process_independent_gamma_array {ι : Type*} (d : ι → ℝ≥0) (e : ι ↪ ℕ) :
    ∃ X : ι → PoissonClockSpace → ℝ,
      (∀ i, Measurable (X i)) ∧
      iIndepFun (fun _ => inferInstance) X poissonClockProbability ∧
      (∀ i, poissonClockProbability.map (X i) = gammaCompletion (d i)) := by
  exact ⟨gammaProcessEmbeddedSamples (fun i => gammaCompletion (d i)) e,
    gamma_process_embedded_samples_measurable _ e,
    gamma_process_embedded_samples_independent _ e,
    gamma_process_embedded_samples_law _ e⟩

end
end Sigma
