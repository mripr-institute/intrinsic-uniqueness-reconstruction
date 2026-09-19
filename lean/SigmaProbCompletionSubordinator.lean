import SigmaProbCompletionDrift
import SigmaProbCompletionProcess

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

/-- Stationary independent increments give native convolution of actual
marginal laws on any supplied probability space. -/
theorem stationary_independent_process_convolution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hm : ∀ r, Measurable (X r)) (hz : ∀ᵐ ω ∂P, X 0 ω=0)
    (hi : HasIndependentNonnegativeTimeIncrements P X)
    (hs : ∀ r s, P.map (fun ω => X (r+s) ω-X r ω)=P.map (X s)) (r s : ℝ≥0) :
    (P.map (X r)).conv (P.map (X s))=P.map (X (r+s)) := by
  have hpair := (indepFun_iff_map_prod_eq_prod_map_map (hm r).aemeasurable
    ((hm (r+s)).sub (hm r)).aemeasurable).mp
      (process_independent_present_future P X hm hz hi r s)
  rw [hs r s] at hpair
  rw [Measure.conv, ← hpair,
    Measure.map_map (by fun_prop) ((hm r).prod_mk ((hm (r+s)).sub (hm r)))]
  congr 1
  funext ω
  simp

/-- The drift tests apply to an actual supplied process, not just to an
abstract family. The supplied Lévy representation is linked to its actual
time-one law by the usual Laplace identity; killing is then derived to vanish. -/
theorem subordinator_gamma_levy_drift_characterization {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hm : ∀ r, Measurable (X r)) (hz : ∀ᵐ ω ∂P, X 0 ω=0)
    (hpos : ∀ r, ∀ᵐ ω ∂P, 0 ≤ X r ω)
    (hi : HasIndependentNonnegativeTimeIncrements P X)
    (hs : ∀ r s, P.map (fun ω => X (r+s) ω-X r ω)=P.map (X s))
    (B : BernsteinRepresentation) (hL : B.levy=gammaCompletionLevyMeasure)
    (ht : ∀ l : ℝ, 0 ≤ l → realLaplace (P.map (X 1)) l=Real.exp (-B.exponent l)) :
    B.killing=0 ∧
    (B.drift=0 ↔ (fun r => P.map (X r))=gammaCompletion) ∧
    (B.drift=0 ↔ Tendsto (fun l : ℝ => B.exponent l/l) atTop (𝓝 0)) ∧
    (B.drift=0 ↔ IsGLB (topologicalMeasureSupport (P.map (X 1))) 0) ∧
    (B.drift=0 ↔ (∫ ω, X 1 ω ∂P)=2) := by
  have hp (r : ℝ≥0) : IsProbabilityMeasure (P.map (X r)) :=
    isProbabilityMeasure_map (hm r).aemeasurable
  have hnon (r : ℝ≥0) : ∀ᵐ t ∂P.map (X r), 0 ≤ t :=
    (ae_map_iff (hm r).aemeasurable measurableSet_Ici).mpr (hpos r)
  have hh := gamma_levy_drift_characterization B hL (fun r => P.map (X r)) hp hnon
    (stationary_independent_process_convolution P X hm hz hi hs) ht
  dsimp only at hh
  rw [integral_map (hm 1).aemeasurable
    (show AEStronglyMeasurable (fun t : ℝ => t) _ from measurable_id.aestronglyMeasurable)] at hh
  exact hh

def addProcessDrift {Ω : Type*} (d : ℝ) (X : ℝ≥0 → Ω → ℝ)
    (r : ℝ≥0) (ω : Ω) : ℝ := X r ω+d*r

theorem process_drift_preserves_independence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (hi : HasIndependentNonnegativeTimeIncrements P X) (d : ℝ) :
    HasIndependentNonnegativeTimeIncrements P (addProcessDrift d X) := by
  intro n t ht ht0
  have hh := (hi n t ht ht0).comp
    (fun i : Fin n => fun z : ℝ => z+d*((t (i.val+1):ℝ)-(t i.val:ℝ)))
    (fun _ => measurable_id.add_const _)
  convert hh using 1
  funext i ω
  dsimp [addProcessDrift]
  ring

theorem process_drift_preserves_stationarity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (hm : ∀ r, Measurable (X r))
    (hs : ∀ r s, P.map (fun ω => X (r+s) ω-X r ω)=P.map (X s)) (d : ℝ) (r s : ℝ≥0) :
    P.map (fun ω => addProcessDrift d X (r+s) ω-addProcessDrift d X r ω)=
      P.map (addProcessDrift d X s) := by
  have hh := congrArg (fun μ : Measure ℝ => μ.map (fun z => z+d*(s:ℝ))) (hs r s)
  dsimp only at hh
  have hshift : Measurable (fun z : ℝ => z+d*(s:ℝ)) := by fun_prop
  have hdiff : Measurable (fun ω => X (r+s) ω-X r ω) := (hm _).sub (hm _)
  rw [Measure.map_map hshift hdiff, Measure.map_map hshift (hm s)] at hh
  convert hh using 1
  congr 1
  funext ω
  simp only [addProcessDrift, NNReal.coe_add, Function.comp_def]
  ring

/-- From any supplied canonical process, deterministic drift produces actual
processes with the drifted laws and preserved stationary independent increments.
This theorem does not assert existence of the input process. -/
theorem drifted_gamma_process_witness {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : IsGammaTimeOneProcess P X) (d : ℝ) (hd : 0 ≤ d) :
    (∀ r, Measurable (addProcessDrift d X r)) ∧
    (∀ᵐ ω ∂P, addProcessDrift d X 0 ω=0) ∧
    (∀ r, ∀ᵐ ω ∂P, 0 ≤ addProcessDrift d X r ω) ∧
    HasIndependentNonnegativeTimeIncrements P (addProcessDrift d X) ∧
    (∀ r s, P.map (fun ω => addProcessDrift d X (r+s) ω-addProcessDrift d X r ω)=
      P.map (addProcessDrift d X s)) ∧
    (∀ r, P.map (addProcessDrift d X r)=gammaDriftCompletion d r) := by
  refine ⟨fun r => (hX.1 r).add_const _, ?_, ?_,
    process_drift_preserves_independence P X hX.2.2.2.1 d,
    process_drift_preserves_stationarity P X hX.1 hX.2.2.2.2.1 d, ?_⟩
  · filter_upwards [hX.2.1] with ω hω
    simp [addProcessDrift, hω]
  · intro r
    filter_upwards [hX.2.2.1 r] with ω hω
    exact add_nonneg hω (mul_nonneg hd r.coe_nonneg)
  · intro r
    have hmarg := congrFun (stationary_independent_process_gamma_marginals P X
      hX.1 hX.2.1 hX.2.2.1 hX.2.2.2.1 hX.2.2.2.2.1 hX.2.2.2.2.2) r
    rw [gammaDriftCompletion, ← hmarg,
      Measure.map_map (by fun_prop : Measurable (fun t : ℝ => d*(r:ℝ)+t)) (hX.1 r)]
    congr 1
    funext ω
    simp only [addProcessDrift, Function.comp_def]
    ring

end
end Sigma
