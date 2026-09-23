import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Periodic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Exponential

open MeasureTheory Measure Set TopologicalSpace
open scoped ENNReal

namespace Sigma
noncomputable section

abbrev PoissonClockSpace := ℕ → AddCircle (1 : ℝ)

noncomputable def poissonClockProbability : Measure PoissonClockSpace :=
  addHaarMeasure ⊤

instance poissonClockProbability_probability : IsProbabilityMeasure poissonClockProbability where
  measure_univ := by
    change addHaarMeasure (⊤ : PositiveCompacts PoissonClockSpace) univ = 1
    simpa only [PositiveCompacts.coe_top] using
      (addHaarMeasure_self (K₀ := (⊤ : PositiveCompacts PoissonClockSpace)))

instance poissonClockProbability_haar : IsAddHaarMeasure poissonClockProbability :=
  inferInstanceAs (IsAddHaarMeasure (addHaarMeasure (⊤ : PositiveCompacts PoissonClockSpace)))

instance poissonClockCircle_probability : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) where
  measure_univ := by simp

def poissonClockProjection (S : Finset ℕ) : PoissonClockSpace →+ (S → AddCircle (1 : ℝ)) where
  toFun ω i := ω i
  map_zero' := rfl
  map_add' _ _ := rfl

theorem poissonClockProjection_continuous (S : Finset ℕ) :
    Continuous (poissonClockProjection S) := continuous_pi fun i => continuous_apply (i : ℕ)

theorem poissonClockProjection_surjective (S : Finset ℕ) :
    Function.Surjective (poissonClockProjection S) := by
  intro x
  refine ⟨fun n => if h : n ∈ S then x ⟨n, h⟩ else 0, ?_⟩
  ext n
  simp [poissonClockProjection, n.property]

theorem poissonClockProjection_map (S : Finset ℕ) :
    poissonClockProbability.map (poissonClockProjection S) =
      Measure.pi (fun _ : S => (volume : Measure (AddCircle (1 : ℝ)))) := by
  letI : IsAddHaarMeasure (poissonClockProbability.map (poissonClockProjection S)) :=
    isAddHaarMeasure_map_of_isFiniteMeasure poissonClockProbability
      (poissonClockProjection S) (poissonClockProjection_continuous S)
      (poissonClockProjection_surjective S)
  letI : IsProbabilityMeasure (poissonClockProbability.map (poissonClockProjection S)) :=
    isProbabilityMeasure_map (poissonClockProjection_continuous S).measurable.aemeasurable
  exact isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem poissonClockCoordinate_map (n : ℕ) :
    poissonClockProbability.map (fun ω => ω n) = (volume : Measure (AddCircle (1 : ℝ))) := by
  let f : PoissonClockSpace →+ AddCircle (1 : ℝ) :=
    { toFun := fun ω => ω n, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hc : Continuous f := continuous_apply n
  have hs : Function.Surjective f := fun x => ⟨fun _ => x, rfl⟩
  letI : IsAddHaarMeasure (poissonClockProbability.map f) :=
    isAddHaarMeasure_map_of_isFiniteMeasure poissonClockProbability f hc hs
  letI : IsProbabilityMeasure (poissonClockProbability.map f) :=
    isProbabilityMeasure_map hc.measurable.aemeasurable
  exact isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem poissonClockCoordinates_independent :
    ProbabilityTheory.iIndepFun (fun _ : ℕ => inferInstance)
      (fun n (ω : PoissonClockSpace) => ω n) poissonClockProbability := by
  rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hs
  have hm : MeasurableSet (Set.univ.pi (fun i : S => sets i)) :=
    MeasurableSet.univ_pi fun i => hs i i.property
  have he : (poissonClockProjection S) ⁻¹' (Set.univ.pi fun i : S => sets i) =
      ⋂ i ∈ S, (fun ω : PoissonClockSpace => ω i) ⁻¹' sets i := by
    ext ω
    simp [poissonClockProjection]
  rw [← he, ← Measure.map_apply (poissonClockProjection_continuous S).measurable hm,
    poissonClockProjection_map, Measure.pi_pi]
  rw [← Finset.prod_coe_sort S]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← poissonClockCoordinate_map i,
    Measure.map_apply (measurable_pi_apply (i : ℕ)) (hs i i.property)]

def poissonCircleUniform (z : AddCircle (1 : ℝ)) : ℝ :=
  AddCircle.measurableEquivIoc 1 0 z

theorem poissonCircleUniform_measurable : Measurable poissonCircleUniform :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc 1 0).measurable

theorem poissonCircleUniform_mem (z : AddCircle (1 : ℝ)) :
    poissonCircleUniform z ∈ Ioc (0 : ℝ) 1 := by
  simpa only [zero_add] using (AddCircle.measurableEquivIoc 1 0 z).property

theorem poissonCircleUniform_coe (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
    poissonCircleUniform (x : AddCircle (1 : ℝ)) = x := by
  let y : Ioc (0 : ℝ) (0 + 1) := ⟨x, by simpa using hx⟩
  exact congrArg Subtype.val ((AddCircle.measurableEquivIoc 1 0).apply_symm_apply y)

theorem poissonCircleUniform_map :
    (volume : Measure (AddCircle (1 : ℝ))).map poissonCircleUniform =
      volume.restrict (Ioc (0 : ℝ) 1) := by
  rw [← (AddCircle.measurePreserving_mk 1 0).map_eq]
  rw [Measure.map_map poissonCircleUniform_measurable AddCircle.measurable_mk']
  have he : poissonCircleUniform ∘ (fun x : ℝ => (x : AddCircle (1 : ℝ))) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) (0+1))] id := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact poissonCircleUniform_coe x (by simpa using hx)
  rw [Measure.map_congr he, Measure.map_id]
  simp

def poissonExponentialClock (n : ℕ) (ω : PoissonClockSpace) : ℝ :=
  -Real.log (poissonCircleUniform (ω n))

theorem poissonExponentialClock_measurable (n : ℕ) : Measurable (poissonExponentialClock n) :=
  (Real.measurable_log.comp (poissonCircleUniform_measurable.comp (measurable_pi_apply n))).neg

theorem poissonExponentialClocks_independent :
    ProbabilityTheory.iIndepFun (fun _ : ℕ => inferInstance)
      poissonExponentialClock poissonClockProbability :=
  poissonClockCoordinates_independent.comp (fun _ z => -Real.log (poissonCircleUniform z))
    (fun _ => (Real.measurable_log.comp poissonCircleUniform_measurable).neg)

theorem poissonExponentialClock_nonneg (n : ℕ) (ω : PoissonClockSpace) :
    0 ≤ poissonExponentialClock n ω := by
  exact neg_nonneg.mpr (Real.log_nonpos (poissonCircleUniform_mem (ω n)).1.le
    (poissonCircleUniform_mem (ω n)).2)

end
end Sigma
