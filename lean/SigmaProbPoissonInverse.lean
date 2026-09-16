import SigmaProbMGFUnique
import SigmaProbPoisson

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

/-- Taking logarithms does not weaken identification when actual exponential
moments are finite: their positivity follows from the probability law. -/
theorem probability_local_cgf_unique (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (a : ℝ) (ha : 0 < a)
    (hμ : ∀ s : ℝ, |s| < a → Integrable (fun t : ℝ => Real.exp (s*t)) μ)
    (hν : ∀ s : ℝ, |s| < a → Integrable (fun t : ℝ => Real.exp (s*t)) ν)
    (hm : ∀ s : ℝ, |s| < a → Real.log (∫ t : ℝ, Real.exp (s*t) ∂μ) =
      Real.log (∫ t : ℝ, Real.exp (s*t) ∂ν)) : μ = ν := by
  apply finite_measure_local_mgf_unique μ ν a ha hμ hν
  intro s hs
  have he := congrArg Real.exp (hm s hs)
  simpa only [Real.exp_log (integral_exp_pos (hμ s hs)),
    Real.exp_log (integral_exp_pos (hν s hs))] using he

def poissonRealProbability : Measure ℝ :=
  Measure.map (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure 1)

def centeredPoissonRealProbability : Measure ℝ :=
  Measure.map (fun n : ℕ => (n : ℝ)-1) (ProbabilityTheory.poissonMeasure 1)

instance poissonRealProbability_is_probability : IsProbabilityMeasure poissonRealProbability :=
  MeasureTheory.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

instance centeredPoissonRealProbability_is_probability :
    IsProbabilityMeasure centeredPoissonRealProbability :=
  MeasureTheory.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem poisson_real_exponential_integrable (u : ℝ) :
    Integrable (fun t : ℝ => Real.exp (u*t)) poissonRealProbability := by
  have hm : Measurable (fun t : ℝ => Real.exp (u*t)) := by fun_prop
  rw [poissonRealProbability, integrable_map_measure
    hm.aestronglyMeasurable
    (measurable_of_countable _).aemeasurable]
  simpa only [Function.comp_def, mul_comm] using poisson_exponential_integrable u

theorem poisson_real_cgf (u : ℝ) :
    Real.log (∫ t : ℝ, Real.exp (u*t) ∂poissonRealProbability) = Real.exp u-1 := by
  have hm : Measurable (fun t : ℝ => Real.exp (u*t)) := by fun_prop
  rw [poissonRealProbability, integral_map (measurable_of_countable _).aemeasurable
    hm.aestronglyMeasurable]
  simpa only [mul_comm] using poisson_probability_cgf u

theorem centered_poisson_real_exponential_integrable (u : ℝ) :
    Integrable (fun t : ℝ => Real.exp (u*t)) centeredPoissonRealProbability := by
  have hm : Measurable (fun t : ℝ => Real.exp (u*t)) := by fun_prop
  rw [centeredPoissonRealProbability, integrable_map_measure
    hm.aestronglyMeasurable
    (measurable_of_countable _).aemeasurable]
  convert (poisson_exponential_integrable u).const_mul (Real.exp (-u)) using 1
  funext n
  simp only [Function.comp_def]
  rw [← Real.exp_add]
  congr 1
  ring

theorem centered_poisson_real_cgf (u : ℝ) :
    Real.log (∫ t : ℝ, Real.exp (u*t) ∂centeredPoissonRealProbability) =
      SigmaPresentations.centeredCGF u := by
  have hm : Measurable (fun t : ℝ => Real.exp (u*t)) := by fun_prop
  rw [centeredPoissonRealProbability, integral_map (measurable_of_countable _).aemeasurable
    hm.aestronglyMeasurable]
  simpa only [mul_comm] using poisson_centered_probability_cgf u

/-- The complete uncentered CGF near zero identifies the Poisson law even among
arbitrary real-line probabilities; integer support is a conclusion. -/
theorem poisson_local_cgf_identifies_real_line_law (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (a : ℝ) (ha : 0 < a)
    (hi : ∀ s : ℝ, |s| < a → Integrable (fun t : ℝ => Real.exp (s*t)) μ)
    (hm : ∀ s : ℝ, |s| < a → Real.log (∫ t : ℝ, Real.exp (s*t) ∂μ) =
      Real.exp s-1) : μ = poissonRealProbability := by
  apply probability_local_cgf_unique μ poissonRealProbability a ha hi
    (fun s _ => poisson_real_exponential_integrable s)
  intro s hs
  rw [hm s hs, poisson_real_cgf]

/-- This identifies the law of the marked variable N-1.  It does not identify an
unmarked source N from the CGF of N-E[N]. -/
theorem marked_centered_poisson_local_cgf_identifies_law (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (a : ℝ) (ha : 0 < a)
    (hi : ∀ s : ℝ, |s| < a → Integrable (fun t : ℝ => Real.exp (s*t)) μ)
    (hm : ∀ s : ℝ, |s| < a → Real.log (∫ t : ℝ, Real.exp (s*t) ∂μ) =
      SigmaPresentations.centeredCGF s) : μ = centeredPoissonRealProbability := by
  apply probability_local_cgf_unique μ centeredPoissonRealProbability a ha hi
    (fun s _ => centered_poisson_real_exponential_integrable s)
  intro s hs
  rw [hm s hs, centered_poisson_real_cgf]

end
end Sigma
