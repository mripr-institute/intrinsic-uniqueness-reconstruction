import SigmaProbGammaProcessExistence
import SigmaProbGammaSubordinatorPaths

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal

theorem native_gamma_subordinator :
    IsProbabilitySubordinator poissonClockProbability nativeGammaProcess :=
  gamma_process_is_subordinator poissonClockProbability nativeGammaProcess
    native_gamma_process_category (native_gamma_process_paths.mono fun _ h => h.2)

/-- Actual drifted paths on the same probability space as the constructed Gamma process. -/
def nativeGammaDriftProcess (d : ℝ) : ℝ≥0 → PoissonClockSpace → ℝ :=
  addProcessDrift d nativeGammaProcess

theorem native_gamma_drift_subordinator (d : ℝ) (hd : 0 ≤ d) :
    IsProbabilitySubordinator poissonClockProbability (nativeGammaDriftProcess d) :=
  native_gamma_subordinator.addDrift d hd

theorem native_gamma_drift_process_marginal (d : ℝ) (hd : 0 ≤ d) (t : ℝ≥0) :
    poissonClockProbability.map (nativeGammaDriftProcess d t) = gammaDriftCompletion d t :=
  (gamma_subordinator_drift_realization poissonClockProbability nativeGammaProcess
    native_gamma_process_category native_gamma_subordinator.paths d hd).2.1 t

/-- Every constructed drifted subordinator has the exact common Gamma Lévy
measure, with killing zero and its stated nonnegative drift. -/
theorem native_gamma_drift_process_levy (d : ℝ) (hd : 0 ≤ d) :
    (gammaDriftBernsteinRepresentation d hd).levy = gammaCompletionLevyMeasure ∧
    (gammaDriftBernsteinRepresentation d hd).killing = 0 ∧
    (gammaDriftBernsteinRepresentation d hd).drift = d ∧
    ∀ t l, 0 ≤ l → realLaplace (poissonClockProbability.map (nativeGammaDriftProcess d t)) l =
      Real.exp (-(t:ℝ)*(gammaDriftBernsteinRepresentation d hd).exponent l) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact (gamma_subordinator_drift_realization poissonClockProbability nativeGammaProcess
    native_gamma_process_category native_gamma_subordinator.paths d hd).2.2

/-- The same Lévy measure genuinely allows distinct subordinator laws. -/
theorem native_gamma_drift_processes_distinct (d e : ℝ) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hne : d ≠ e) :
    poissonClockProbability.map (nativeGammaDriftProcess d 1) ≠
      poissonClockProbability.map (nativeGammaDriftProcess e 1) := by
  rw [native_gamma_drift_process_marginal d hd, native_gamma_drift_process_marginal e he,
    gamma_drift_completion_one, gamma_drift_completion_one]
  exact gamma_drifted_probability_distinct hne

/-- Unconditional realization of every nonnegative drift, including the
canonical zero-drift case, with the usual subordinator path convention. -/
theorem native_gamma_drift_subordinator_exists (d : ℝ) (hd : 0 ≤ d) :
    ∃ X : ℝ≥0 → PoissonClockSpace → ℝ,
      IsProbabilitySubordinator poissonClockProbability X ∧
      (∀ t, poissonClockProbability.map (X t) = gammaDriftCompletion d t) ∧
      (∀ t l, 0 ≤ l → realLaplace (poissonClockProbability.map (X t)) l =
        Real.exp (-(t:ℝ)*(gammaDriftBernsteinRepresentation d hd).exponent l)) :=
  ⟨nativeGammaDriftProcess d, native_gamma_drift_subordinator d hd,
    native_gamma_drift_process_marginal d hd, (native_gamma_drift_process_levy d hd).2.2.2⟩

end
end Sigma
