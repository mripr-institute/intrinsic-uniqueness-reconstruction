import SigmaProbTreeSource
import SigmaProbNatSampler
import SigmaRealTreesOffspring
import Mathlib.Probability.Integration

open MeasureTheory Measure Set
open scoped ENNReal BigOperators

namespace Sigma
noncomputable section

def treeRootOffspring (q : PMF ℕ) (ω : TreeSource) : ℕ :=
  natPMFSample q (treeRootSource ω)

theorem treeRootOffspring_measurable (q : PMF ℕ) : Measurable (treeRootOffspring q) :=
  (nat_pmf_sample_measurable q).comp treeRootSource_measurable

theorem treeRootOffspring_map (q : PMF ℕ) :
    treeSourceProbability.map (treeRootOffspring q) = q.toMeasure := by
  change treeSourceProbability.map (natPMFSample q ∘ treeRootSource) = _
  rw [← Measure.map_map (nat_pmf_sample_measurable q)
    treeRootSource_measurable, treeRootSource_map, nat_pmf_sample_map]

theorem treeRootOffspring_fiber (q : PMF ℕ) (n : ℕ) :
    treeSourceProbability {ω | treeRootOffspring q ω = n} = q n := by
  have h := congrArg (fun μ : Measure ℕ => μ {n}) (treeRootOffspring_map q)
  simpa [Measure.map_apply (treeRootOffspring_measurable q) (measurableSet_singleton n),
    PMF.toMeasure_apply_singleton] using h

theorem tree_children_product_measurable (f : TreeSource → ℝ≥0∞)
    (hf : Measurable f) (n : ℕ) :
    Measurable (fun ω => ∏ i ∈ Finset.range n, f (treeChildSource i ω)) := by
  exact Finset.measurable_prod _ fun i _ => hf.comp (treeChildSource_measurable i)

/-- Every finite collection of entire child trees is iid, so its nonnegative
product expectation factors, without any integrability assumptions. -/
theorem tree_children_product_lintegral (f : TreeSource → ℝ≥0∞)
    (hf : Measurable f) (n : ℕ) :
    (∫⁻ ω, ∏ i ∈ Finset.range n, f (treeChildSource i ω) ∂treeSourceProbability) =
      (∫⁻ ω, f ω ∂treeSourceProbability)^n := by
  have hi := treeChildSources_independent.comp (fun _ => f) (fun _ => hf)
  have hm (i : ℕ) : Measurable (fun ω => f (treeChildSource i ω)) :=
    hf.comp (treeChildSource_measurable i)
  have he (i : ℕ) :
      (∫⁻ ω, f (treeChildSource i ω) ∂treeSourceProbability) =
        ∫⁻ ω, f ω ∂treeSourceProbability := by
    rw [← lintegral_map hf (treeChildSource_measurable i), treeChildSource_map]
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.prod_range_succ, pow_succ]
    have hind := hi.indepFun_prod_range_succ hm n
    have hprod := ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      (tree_children_product_measurable f hf n) (hm n)
      (by convert hind using 1; ext ω; simp)
    simp only [Pi.mul_apply] at hprod
    change (∫⁻ ω, (fun ω => ∏ i ∈ Finset.range n, f (treeChildSource i ω)) ω *
      (fun ω => f (treeChildSource n ω)) ω ∂treeSourceProbability) = _
    rw [hprod, ih, he]

theorem tree_root_fiber_independent_product (q : PMF ℕ)
    (f : TreeSource → ℝ≥0∞) (hf : Measurable f) (n : ℕ) :
    ProbabilityTheory.IndepFun
      (fun ω => if treeRootOffspring q ω = n then (1 : ℝ≥0∞) else 0)
      (fun ω => ∏ i ∈ Finset.range n, f (treeChildSource i ω))
      treeSourceProbability := by
  have hr : Measurable (fun z => if natPMFSample q z = n then (1 : ℝ≥0∞) else 0) := by
    exact Measurable.ite ((nat_pmf_sample_measurable q) (measurableSet_singleton n))
      measurable_const measurable_const
  have hp : Measurable (fun x : (Finset.range n) → TreeSource => ∏ i, f (x i)) :=
    Finset.measurable_prod _ fun i _ => hf.comp (measurable_pi_apply i)
  have h := (treeRootSource_independent_children (Finset.range n)).comp hr hp
  convert h using 1
  ext ω
  exact (Finset.prod_coe_sort (Finset.range n)
    (fun i => f (treeChildSource i ω))).symm

/-- Conditioning on the actual sampled root offspring count. This is the
branching identity used for extinction probabilities and total-size PGFs. -/
theorem tree_offspring_product_lintegral (q : PMF ℕ)
    (f : TreeSource → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∏ i ∈ Finset.range (treeRootOffspring q ω),
      f (treeChildSource i ω) ∂treeSourceProbability) =
      ∑' n : ℕ, q n * (∫⁻ ω, f ω ∂treeSourceProbability)^n := by
  have hm (n : ℕ) : Measurable (fun ω =>
      if treeRootOffspring q ω = n then (1 : ℝ≥0∞) else 0) := by
    exact Measurable.ite ((treeRootOffspring_measurable q) (measurableSet_singleton n))
      measurable_const measurable_const
  have hsplit (ω : TreeSource) :
      (∏ i ∈ Finset.range (treeRootOffspring q ω), f (treeChildSource i ω)) =
      ∑' n : ℕ, (if treeRootOffspring q ω = n then (1 : ℝ≥0∞) else 0) *
        ∏ i ∈ Finset.range n, f (treeChildSource i ω) := by
    symm
    rw [tsum_eq_single (treeRootOffspring q ω)]
    · simp
    · intro b hb
      simp [Ne.symm hb]
  simp_rw [hsplit]
  rw [lintegral_tsum (fun n => ((hm n).mul
    (tree_children_product_measurable f hf n)).aemeasurable)]
  apply tsum_congr
  intro n
  have hmul := ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (hm n) (tree_children_product_measurable f hf n)
    (tree_root_fiber_independent_product q f hf n)
  simp only [Pi.mul_apply] at hmul
  rw [hmul, tree_children_product_lintegral f hf n]
  congr 1
  have hset : MeasurableSet {ω | treeRootOffspring q ω = n} :=
    (treeRootOffspring_measurable q) (measurableSet_singleton n)
  have hval := lintegral_indicator_const (μ := treeSourceProbability) hset (1 : ℝ≥0∞)
  simpa only [Set.indicator_apply, Set.mem_setOf_eq, one_mul, treeRootOffspring_fiber] using hval

theorem nat_probability_generating_ennreal_le_one (q : PMF ℕ)
    (x : ℝ≥0∞) (hx : x ≤ 1) : (∑' n : ℕ, q n * x^n) ≤ 1 := by
  calc
    (∑' n : ℕ, q n * x^n) ≤ ∑' n : ℕ, q n := by
      apply ENNReal.tsum_le_tsum
      intro n
      exact mul_le_of_le_one_right (zero_le _) (pow_le_one₀ (zero_le x) hx)
    _ = 1 := q.tsum_coe

theorem nat_probability_generating_ennreal_toReal (q : PMF ℕ)
    (x : ℝ≥0∞) (hx : x ≤ 1) :
    (∑' n : ℕ, q n * x^n).toReal = natProbabilityGenerating q x.toReal := by
  rw [ENNReal.tsum_toReal_eq]
  · simp only [natProbabilityGenerating, ENNReal.toReal_mul, ENNReal.toReal_pow]
  · intro n
    exact ENNReal.mul_ne_top (q.apply_ne_top n)
      (ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hx))

end
end Sigma
