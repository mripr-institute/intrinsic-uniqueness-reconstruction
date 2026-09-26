import SigmaProbGammaCadlagDyadic
import SigmaProbGammaProcessGridIndependence
import SigmaProbGammaProcessSupport

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

/-- The concrete Haar/Beta construction supplies every field of the grid
realization; no stochastic realization is assumed. -/
theorem gamma_dyadic_grid_realization :
    GammaGridRealization poissonClockProbability gammaDyadicTime gammaDyadicProcessGrid where
  cofinal := gamma_dyadic_time_cofinal
  measurable := gamma_dyadic_process_grid_measurable
  paths := gamma_dyadic_process_grid_paths
  marginal := gamma_dyadic_process_grid_law
  increment := gamma_dyadic_process_grid_increment_law
  independent := gamma_dyadic_process_grid_independent

/-- A single actual Gamma process at all nonnegative real times on the
countable Haar probability space. -/
def nativeGammaProcess : ℝ≥0 → PoissonClockSpace → ℝ :=
  gammaGridProcess gammaDyadicTime gammaDyadicProcessGrid

theorem native_gamma_process_category :
    IsGammaTimeOneProcess poissonClockProbability nativeGammaProcess :=
  gamma_grid_process_category poissonClockProbability gamma_dyadic_grid_realization
    gammaDyadicUpperApproximation

theorem native_gamma_process_measurable (t : ℝ≥0) : Measurable (nativeGammaProcess t) :=
  native_gamma_process_category.1 t

/-- Nonnegative, monotone and right-continuous sample paths hold simultaneously
at every real time on one event of probability one. -/
theorem native_gamma_process_paths :
    ∀ᵐ ω ∂poissonClockProbability,
      (∀ t, 0 ≤ nativeGammaProcess t ω) ∧
      Monotone (fun t => nativeGammaProcess t ω) ∧
      (∀ t, ContinuousWithinAt (fun s => nativeGammaProcess s ω) (Ici t) t) :=
  gamma_grid_process_paths poissonClockProbability gamma_dyadic_grid_realization

theorem native_gamma_process_marginal (t : ℝ≥0) :
    poissonClockProbability.map (nativeGammaProcess t) = gammaCompletion t :=
  gamma_grid_process_marginal poissonClockProbability gamma_dyadic_grid_realization
    gammaDyadicUpperApproximation t

theorem native_gamma_process_increment (s t : ℝ≥0) (hst : s ≤ t) :
    poissonClockProbability.map (fun ω => nativeGammaProcess t ω-nativeGammaProcess s ω) =
      gammaCompletion (t-s) :=
  gamma_grid_process_increment poissonClockProbability gamma_dyadic_grid_realization
    gammaDyadicUpperApproximation s t hst

/-- Unconditional existence in the paper's process category, together with its
usual right-continuous increasing path convention. -/
theorem native_gamma_process_exists :
    ∃ X : ℝ≥0 → PoissonClockSpace → ℝ,
      IsGammaTimeOneProcess poissonClockProbability X ∧
      (∀ᵐ ω ∂poissonClockProbability,
        (∀ t, 0 ≤ X t ω) ∧ Monotone (fun t => X t ω) ∧
          ∀ t, ContinuousWithinAt (fun s => X s ω) (Ici t) t) :=
  ⟨nativeGammaProcess, native_gamma_process_category, native_gamma_process_paths⟩

/-- The actual construction realizes the unique finite-dimensional law of any
supplied process in the paper's category, at arbitrary observation times. -/
theorem native_gamma_process_fdd_unique {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : IsGammaTimeOneProcess P X) (n : ℕ) (u : Fin n → ℝ≥0) :
    P.map (fun ω i => X (u i) ω) =
      poissonClockProbability.map (fun ω i => nativeGammaProcess (u i) ω) :=
  gamma_time_one_process_fdd_unique P poissonClockProbability X nativeGammaProcess
    hX native_gamma_process_category n u

end
end Sigma
