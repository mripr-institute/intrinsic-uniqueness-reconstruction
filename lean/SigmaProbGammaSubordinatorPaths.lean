import SigmaProbCompletionSubordinator

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

/-- Increasing right-continuous paths on one common full-measure event. -/
def HasIncreasingRightContinuousPaths {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, Monotone (fun t => X t ω) ∧
    ∀ t, ContinuousWithinAt (fun s => X s ω) (Ici t) t

/-- The native probability-subordinator category, without prescribing a marginal. -/
structure IsProbabilitySubordinator {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Prop where
  measurable : ∀ t, Measurable (X t)
  zero : ∀ᵐ ω ∂P, X 0 ω = 0
  paths : HasIncreasingRightContinuousPaths P X
  independent : HasIndependentNonnegativeTimeIncrements P X
  stationary : ∀ r s, P.map (fun ω => X (r+s) ω-X r ω) = P.map (X s)

theorem IsProbabilitySubordinator.nonnegative {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} (h : IsProbabilitySubordinator P X) :
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ X t ω := by
  filter_upwards [h.zero, h.paths] with ω hz hp
  intro t
  have hh := hp.1 (show (0 : ℝ≥0) ≤ t from zero_le _)
  change X 0 ω ≤ X t ω at hh
  rwa [hz] at hh

theorem gamma_process_is_subordinator {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (h : IsGammaTimeOneProcess P X)
    (hp : HasIncreasingRightContinuousPaths P X) : IsProbabilitySubordinator P X :=
  ⟨h.1, h.2.1, hp, h.2.2.2.1, h.2.2.2.2.1⟩

theorem process_drift_preserves_paths {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (hp : HasIncreasingRightContinuousPaths P X) (d : ℝ) (hd : 0 ≤ d) :
    HasIncreasingRightContinuousPaths P (addProcessDrift d X) := by
  filter_upwards [hp] with ω hω
  constructor
  · intro s t hst
    exact add_le_add (hω.1 hst) (mul_le_mul_of_nonneg_left hst hd)
  · intro t
    exact (hω.2 t).add ((continuous_const.mul NNReal.continuous_coe).continuousWithinAt)

theorem IsProbabilitySubordinator.addDrift {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} (h : IsProbabilitySubordinator P X)
    (d : ℝ) (hd : 0 ≤ d) : IsProbabilitySubordinator P (addProcessDrift d X) := by
  refine ⟨fun t => (h.measurable t).add_const _, ?_,
    process_drift_preserves_paths P X h.paths d hd,
    process_drift_preserves_independence P X h.independent d,
    process_drift_preserves_stationarity P X h.measurable h.stationary d⟩
  filter_upwards [h.zero] with ω hω
  simp [addProcessDrift, hω]

/-- Every nonnegative drift is realized on the SAME actual probability space,
with right-continuous increasing paths and the exact linked Lévy exponent. -/
theorem gamma_subordinator_drift_realization {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : IsGammaTimeOneProcess P X) (hp : HasIncreasingRightContinuousPaths P X)
    (d : ℝ) (hd : 0 ≤ d) :
    IsProbabilitySubordinator P (addProcessDrift d X) ∧
    (∀ r, P.map (addProcessDrift d X r) = gammaDriftCompletion d r) ∧
    (∀ r l, 0 ≤ l → realLaplace (P.map (addProcessDrift d X r)) l =
      Real.exp (-(r:ℝ)*(gammaDriftBernsteinRepresentation d hd).exponent l)) := by
  have hs := (gamma_process_is_subordinator P X hX hp).addDrift d hd
  have hm := (drifted_gamma_process_witness P X hX d hd).2.2.2.2.2
  refine ⟨hs, hm, ?_⟩
  intro r l hl
  rw [hm r]
  exact gamma_drift_completion_levy_representation d hd r l hl

/-- The four tests apply to the native path category with a linked exact
Gamma Lévy measure, without assuming the Gamma time-one law. -/
theorem probability_subordinator_gamma_levy_characterization {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsProbabilitySubordinator P X)
    (B : BernsteinRepresentation) (hL : B.levy = gammaCompletionLevyMeasure)
    (ht : ∀ l : ℝ, 0 ≤ l → realLaplace (P.map (X 1)) l = Real.exp (-B.exponent l)) :
    B.killing = 0 ∧
    (B.drift = 0 ↔ (fun r => P.map (X r)) = gammaCompletion) ∧
    (B.drift = 0 ↔ Tendsto (fun l : ℝ => B.exponent l/l) atTop (𝓝 0)) ∧
    (B.drift = 0 ↔ IsGLB (topologicalMeasureSupport (P.map (X 1))) 0) ∧
    (B.drift = 0 ↔ (∫ ω, X 1 ω ∂P) = 2) :=
  subordinator_gamma_levy_drift_characterization P X hX.measurable hX.zero
    (fun r => hX.nonnegative.mono fun _ hω => hω r)
    hX.independent hX.stationary B hL ht

end
end Sigma
