import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.MeasureTheory.Measure.WithDensity

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem statistic_tilt_map {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (μ : Measure Ω) (T : Ω → S) (hT : Measurable T)
    (w : S → ℝ≥0∞) (hw : Measurable w) :
    (μ.withDensity (fun x => w (T x))).map T = (μ.map T).withDensity w := by
  ext s hs
  rw [Measure.map_apply hT hs, withDensity_apply _ (hT hs), withDensity_apply _ hs]
  exact (setLIntegral_map hs hw hT).symm

theorem statistic_tilt_compProd {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (μ : Measure S) [SFinite μ] (K : Kernel S Ω) [IsSFiniteKernel K]
    (w : S → ℝ≥0∞) (hw : Measurable w) :
    (μ.withDensity w) ⊗ₘ K = (μ ⊗ₘ K).withDensity (fun p => w p.1) := by
  ext s hs
  have hm : Measurable (s.indicator (fun p : S × Ω => w p.1)) :=
    (hw.comp measurable_fst).indicator hs
  rw [Measure.compProd_apply hs,
    lintegral_withDensity_eq_lintegral_mul _ hw (Kernel.measurable_kernel_prod_mk_left hs),
    withDensity_apply _ hs, ← lintegral_indicator hs, Measure.lintegral_compProd hm]
  apply lintegral_congr
  intro a
  have he : (fun b => s.indicator (fun p => w p.1) (a,b)) =
      fun b => w a * (Prod.mk a ⁻¹' s).indicator (fun _ => 1) b := by
    funext b
    by_cases h : (a,b) ∈ s <;> simp [h]
  rw [he, lintegral_const_mul _ (measurable_const.indicator (measurable_prod_mk_left hs)),
    lintegral_indicator (measurable_prod_mk_left hs)]
  simp

/-- A single actual conditional probability kernel works for the entire
family. The joint-law identity retains the observed statistic as well as
the original sample, and is the statistical sufficiency assertion. -/
def HasCommonStatisticKernel {Θ Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Θ → Measure Ω) (T : Ω → S) : Prop :=
  ∃ K : Kernel S Ω, IsMarkovKernel K ∧
    ∀ θ, (P θ).map T ⊗ₘ K = (P θ).map (fun x => (T x,x))

/-- The dominated factorization criterion, proved as a common conditional
kernel, not asserted as an interpretation of a density formula. -/
theorem common_statistic_kernel_of_tilts {Θ Ω S : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace S]
    (μ : Measure Ω) [IsFiniteMeasure μ] (T : Ω → S) (hT : Measurable T)
    (w : Θ → S → ℝ≥0∞) (hw : ∀ θ, Measurable (w θ)) :
    HasCommonStatisticKernel (fun θ => μ.withDensity (fun x => w θ (T x))) T := by
  let ρ := μ.map (fun x => (T x,x))
  have hfst : ρ.fst = μ.map T := Measure.fst_map_prod_mk measurable_id
  refine ⟨ρ.condKernel, inferInstance, ?_⟩
  intro θ
  rw [statistic_tilt_map μ T hT (w θ) (hw θ), ← hfst,
    statistic_tilt_compProd _ _ _ (hw θ), Measure.disintegrate]
  change (μ.map (fun x => (T x,x))).withDensity (fun p => w θ p.1) = _
  exact (statistic_tilt_map μ (fun x => (T x,x)) (hT.prod_mk measurable_id)
    (fun p => w θ p.1) ((hw θ).comp measurable_fst)).symm

end
end Sigma
