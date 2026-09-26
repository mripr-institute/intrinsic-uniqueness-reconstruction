import SigmaProbGammaProcessGrid

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

/-- All raw totals and splitting fractions simultaneously have their prescribed
support, on one probability-one event. -/
theorem gamma_dyadic_inputs_support (beta : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (beta n)]
    (hb : ∀ n, ∀ᵐ b ∂beta n, b ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ ω ∂poissonClockProbability,
      (∀ k, 0 ≤ gammaDyadicInputs beta (0,k) ω) ∧
      (∀ n k, gammaDyadicInputs beta (n+1,k) ω ∈ Icc (0 : ℝ) 1) := by
  have hz (k : ℕ) : ∀ᵐ ω ∂poissonClockProbability,
      0 ≤ gammaDyadicInputs beta (0,k) ω := by
    apply (ae_map_iff (gamma_dyadic_inputs_measurable beta (0,k)).aemeasurable
      measurableSet_Ici).mp
    rw [gamma_dyadic_inputs_law]
    exact gamma_completion_nonnegative 1
  have hs (n k : ℕ) : ∀ᵐ ω ∂poissonClockProbability,
      gammaDyadicInputs beta (n+1,k) ω ∈ Icc (0 : ℝ) 1 := by
    apply (ae_map_iff (gamma_dyadic_inputs_measurable beta (n+1,k)).aemeasurable
      measurableSet_Icc).mp
    rw [gamma_dyadic_inputs_law]
    exact hb n
  exact (ae_all_iff.mpr hz).and (ae_all_iff.mpr fun n => ae_all_iff.mpr (hs n))

/-- The actual dyadic array has nonnegative, mutually consistent ordered paths
through every grid level on a single probability-one event. -/
theorem gamma_dyadic_grid_paths (beta : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (beta n)]
    (hb : ∀ n, ∀ᵐ b ∂beta n, b ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ ω ∂poissonClockProbability,
      (∀ p : ℕ × ℕ, 0 ≤ gammaDyadicGrid (gammaDyadicInputs beta) p.1 p.2 ω) ∧
      (∀ p q : ℕ × ℕ, gammaDyadicTime p ≤ gammaDyadicTime q →
        gammaDyadicGrid (gammaDyadicInputs beta) p.1 p.2 ω ≤
          gammaDyadicGrid (gammaDyadicInputs beta) q.1 q.2 ω) := by
  filter_upwards [gamma_dyadic_inputs_support beta hb] with ω hω
  constructor
  · intro p
    exact Finset.sum_nonneg fun k hk =>
      gamma_dyadic_increment_nonnegative _ ω hω.1 hω.2 p.1 k
  · exact gamma_dyadic_grid_time_monotone _ ω hω.1 hω.2

/-- The concrete symmetric Beta laws used at each refinement depth satisfy the
raw-array support requirement. -/
theorem gamma_dyadic_beta_inputs_support :
    ∀ᵐ ω ∂poissonClockProbability,
      (∀ k, 0 ≤ gammaDyadicInputs
        (fun n => gammaProcessBetaProbability (gammaDyadicDuration n)) (0,k) ω) ∧
      (∀ n k, gammaDyadicInputs
        (fun n => gammaProcessBetaProbability (gammaDyadicDuration n)) (n+1,k) ω ∈
          Icc (0 : ℝ) 1) :=
  gamma_dyadic_inputs_support _ (fun n => gamma_process_beta_support (gammaDyadicDuration n))

theorem gamma_dyadic_beta_grid_paths :
    ∀ᵐ ω ∂poissonClockProbability,
      (∀ p : ℕ × ℕ, 0 ≤ gammaDyadicGrid (gammaDyadicInputs
        (fun n => gammaProcessBetaProbability (gammaDyadicDuration n))) p.1 p.2 ω) ∧
      (∀ p q : ℕ × ℕ, gammaDyadicTime p ≤ gammaDyadicTime q →
        gammaDyadicGrid (gammaDyadicInputs
          (fun n => gammaProcessBetaProbability (gammaDyadicDuration n))) p.1 p.2 ω ≤
        gammaDyadicGrid (gammaDyadicInputs
          (fun n => gammaProcessBetaProbability (gammaDyadicDuration n))) q.1 q.2 ω) :=
  gamma_dyadic_grid_paths _ (fun n => gamma_process_beta_support (gammaDyadicDuration n))

/-- Common support event for the named concrete raw array. -/
theorem gamma_dyadic_raw_support :
    ∀ᵐ ω ∂poissonClockProbability,
      (∀ k, 0 ≤ gammaDyadicRaw (0,k) ω) ∧
      (∀ n k, gammaDyadicRaw (n+1,k) ω ∈ Icc (0 : ℝ) 1) :=
  gamma_dyadic_inputs_support gammaDyadicBeta
    (fun n => gamma_process_beta_support (gammaDyadicDuration n))

/-- The path field of the concrete grid realization, on one common full-measure event. -/
theorem gamma_dyadic_process_grid_paths :
    ∀ᵐ ω ∂poissonClockProbability,
      (∀ p, 0 ≤ gammaDyadicProcessGrid p ω) ∧
      (∀ p q, gammaDyadicTime p ≤ gammaDyadicTime q →
        gammaDyadicProcessGrid p ω ≤ gammaDyadicProcessGrid q ω) :=
  gamma_dyadic_grid_paths gammaDyadicBeta
    (fun n => gamma_process_beta_support (gammaDyadicDuration n))

end
end Sigma
