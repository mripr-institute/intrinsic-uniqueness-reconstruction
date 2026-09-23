import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Independence.Basic

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal

/-- Multiplication of integrable nonnegative densities gives the density of
the actual native finite product measure. -/
theorem finite_iid_density_measure {ι E : Type*} [Fintype ι] [MeasureSpace E]
    [SigmaFinite (volume : Measure E)] (f : E → ℝ) (hf : Integrable f)
    (hpos : ∀ x, 0 ≤ f x) :
    Measure.pi (fun _ : ι => volume.withDensity (fun x => ENNReal.ofReal (f x))) =
      (volume : Measure (ι → E)).withDensity (fun x => ENNReal.ofReal (∏ i, f (x i))) := by
  classical
  have hp : Integrable (fun x : ι → E => ∏ i, f (x i)) :=
    Integrable.fintype_prod (fun _ => hf)
  apply Measure.pi_eq
  intro s hs
  have hb : MeasurableSet (Set.pi univ s) :=
    (measurableSet_pi (Set.to_countable univ)).mpr (Or.inl (fun i _ => hs i))
  rw [withDensity_apply _ hb,
    ← ofReal_integral_eq_lintegral_ofReal hp.integrableOn
      (Eventually.of_forall fun x => Finset.prod_nonneg fun i _ => hpos (x i))]
  have he : (Set.pi univ s).indicator (fun x : ι → E => ∏ i, f (x i)) =
      fun x => ∏ i, (s i).indicator f (x i) := by
    ext x
    by_cases hx : x ∈ Set.pi univ s
    · rw [indicator_of_mem hx]
      apply Finset.prod_congr rfl
      intro i _
      rw [indicator_of_mem (hx i (mem_univ i))]
    · rw [indicator_of_not_mem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by
        simpa only [Set.mem_pi, mem_univ, forall_const, not_forall] using hx
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_not_mem hi f)
  rw [← integral_indicator hb, he, integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ =>
    integral_nonneg fun x => indicator_nonneg (fun a _ => hpos a) x)]
  apply Finset.prod_congr rfl
  intro i _
  rw [integral_indicator (hs i), withDensity_apply _ (hs i),
    ofReal_integral_eq_lintegral_ofReal hf.integrableOn (Eventually.of_forall hpos)]

theorem finite_iid_log_density {ι E : Type*} [Fintype ι]
    (f : E → ℝ) (hf : ∀ x, 0 < f x) (x : ι → E) :
    Real.log (∏ i, f (x i)) = ∑ i, Real.log (f (x i)) := by
  rw [Real.log_prod]
  intro i _
  exact (hf (x i)).ne'

/-- Independent measurable observations with specified marginal laws have the
native finite product joint law. -/
theorem finite_independent_joint_law {ι Ω E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν] (Z : ι → Ω → E)
    (hZ : ∀ i, Measurable (Z i))
    (hind : ProbabilityTheory.iIndepFun (fun _ => inferInstance) Z μ)
    (hlaw : ∀ i, μ.map (Z i) = ν) :
    μ.map (fun ω i => Z i ω) = Measure.pi (fun _ : ι => ν) := by
  classical
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (measurable_pi_lambda _ hZ)
    (MeasurableSet.pi (Set.to_countable univ) (fun i _ => hs i))]
  have he : (fun ω i => Z i ω) ⁻¹' Set.pi univ s = ⋂ i ∈ Finset.univ, Z i ⁻¹' s i := by
    ext ω
    simp
  rw [he, hind.measure_inter_preimage_eq_mul Finset.univ (fun i _ => hs i)]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Measure.map_apply (hZ i) (hs i), hlaw i]

end
end Sigma
