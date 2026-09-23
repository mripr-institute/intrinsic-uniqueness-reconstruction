import Mathlib.MeasureTheory.Covering.OneDim
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

/-- The a.e. fundamental theorem for a locally integrable complex function,
derived from the actual one-dimensional Lebesgue differentiation theorem. -/
theorem locally_integrable_primitive_hasDerivAt_ae (g : ℝ → ℂ)
    (hg : LocallyIntegrable g volume) (a : ℝ) :
    ∀ᵐ x : ℝ, HasDerivAt (fun t => ∫ u in a..t, g u) (g x) x := by
  have hi (b c : ℝ) : IntervalIntegrable g volume b c :=
    (hg.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hav := (IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure ℝ) 1).ae_tendsto_average hg
  filter_upwards [hav] with x hx
  rw [hasDerivAt_iff_tendsto_slope, ← nhds_left'_sup_nhds_right', tendsto_sup]
  constructor
  · have hl := hx.comp (Real.tendsto_Icc_vitaliFamily_left x)
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    change t < x at ht
    dsimp only [Function.comp_apply]
    rw [slope_def_module, intervalIntegral.integral_interval_sub_left (hi a t) (hi a x)]
    rw [setAverage_eq, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr ht.le),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.le,
      intervalIntegral.integral_symm]
    rw [show t-x = -(x-t) by ring, inv_neg, neg_smul, smul_neg]
  · have hr := hx.comp (Real.tendsto_Icc_vitaliFamily_right x)
    apply hr.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    change x < t at ht
    dsimp only [Function.comp_apply]
    rw [slope_def_module, intervalIntegral.integral_interval_sub_left (hi a t) (hi a x)]
    rw [setAverage_eq, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr ht.le),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.le]

theorem locally_integrable_primitive_deriv_ae (g : ℝ → ℂ)
    (hg : LocallyIntegrable g volume) (a : ℝ) :
    deriv (fun t => ∫ u in a..t, g u) =ᵐ[volume] g := by
  filter_upwards [locally_integrable_primitive_hasDerivAt_ae g hg a] with x hx
  exact hx.deriv

/-- The literal epsilon-delta absolute-continuity condition for the primitive:
small total lengths of disjoint intervals force small total increments.
Extended nonnegative reals are used only to state the same nonnegative sums. -/
theorem integrable_primitive_absolute_continuity (g : ℝ → ℂ)
    (hg : Integrable g volume) (a : ℝ) (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ (m : ℕ) (u v : Fin m → ℝ),
      (∀ i, u i ≤ v i) →
      (Set.univ.PairwiseDisjoint (fun i => Ioc (u i) (v i))) →
      (∑ i, ENNReal.ofReal (v i-u i)) < δ →
      (∑ i, (‖(∫ t in a..v i, g t) - ∫ t in a..u i, g t‖₊ : ℝ≥0∞)) < ε := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_setLIntegral_lt_of_measure_lt hg.2.ne hε
  refine ⟨δ, hδ, ?_⟩
  intro m u v huv hdis hlen
  have hdis' : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (fun i => Ioc (u i) (v i)) := by simpa using hdis
  have hm : volume (⋃ i ∈ (Finset.univ : Finset (Fin m)), Ioc (u i) (v i)) < δ := by
    rw [measure_biUnion_finset hdis' (fun _ _ => measurableSet_Ioc)]
    simpa only [Real.volume_Ioc] using hlen
  apply lt_of_le_of_lt _ (hsmall _ hm)
  rw [lintegral_biUnion_finset hdis' (fun _ _ => measurableSet_Ioc)]
  apply Finset.sum_le_sum
  intro i hi
  rw [intervalIntegral.integral_interval_sub_left hg.intervalIntegrable hg.intervalIntegrable,
    intervalIntegral.integral_of_le (huv i)]
  exact ennnorm_integral_le_lintegral_ennnorm _

end
end Sigma
