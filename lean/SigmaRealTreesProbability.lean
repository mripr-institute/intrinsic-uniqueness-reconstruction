import SigmaRealTreesNormalization
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Independence.Basic

namespace Sigma
noncomputable section
open PowerSeries MeasureTheory
open scoped BigOperators

def borelPMF : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal (borelCoefficient n), by
    apply ENNReal.summable.hasSum_iff.mpr
    rw [← ENNReal.ofReal_tsum_of_nonneg borel_coefficient_nonnegative borel_coefficients_summable,
      borel_coefficients_sum_one, ENNReal.ofReal_one]⟩

theorem borel_pmf_apply (n : ℕ) : borelPMF n = ENNReal.ofReal (borelCoefficient n) := rfl

def borelProbability : Measure ℕ := borelPMF.toMeasure

instance borel_probability_isProbability : IsProbabilityMeasure borelProbability :=
  inferInstanceAs (IsProbabilityMeasure borelPMF.toMeasure)

theorem borel_probability_singleton (n : ℕ) :
    borelProbability {n} = ENNReal.ofReal (borelCoefficient n) :=
  borelPMF.toMeasure_apply_singleton n (measurableSet_singleton n)

theorem borel_probability_zero : borelProbability {0} = 0 := by
  rw [borel_probability_singleton, borel_coefficient_zero, ENNReal.ofReal_zero]

theorem borel_probability_positive_singletons (n : ℕ) :
    0 < borelProbability {n + 1} := by
  rw [borel_probability_singleton, ENNReal.ofReal_pos]
  exact borel_coefficient_positive n

theorem borel_probability_identified (μ : Measure ℕ)
    (hμ : ∀ n, μ {n} = ENNReal.ofReal (borelCoefficient n)) : μ = borelProbability := by
  apply Measure.ext_of_singleton
  intro n
  rw [hμ n, borel_probability_singleton]

/-- Independent sampling: the second PMF is fixed and does not depend on the first draw. -/
def independentNatSum (p q : PMF ℕ) : PMF ℕ :=
  p.bind fun a => q.map (fun b => a + b)

theorem translated_nat_pmf (q : PMF ℕ) (a n : ℕ) :
    q.map (fun b => a + b) n = if a ≤ n then q (n - a) else 0 := by
  rw [PMF.map_apply]
  by_cases ha : a ≤ n
  · rw [if_pos ha]
    have htest (b : ℕ) : n = a + b ↔ b = n - a := by omega
    simp_rw [htest]
    rw [tsum_eq_single (n - a)]
    · simp
    · intro b hb
      simp [hb]
  · rw [if_neg ha]
    have htest (b : ℕ) : n ≠ a + b := by omega
    simp only [htest, if_false, tsum_zero]

theorem independent_nat_sum_apply (p q : PMF ℕ) (n : ℕ) :
    independentNatSum p q n = ∑ a ∈ Finset.range (n + 1), p a * q (n - a) := by
  simp only [independentNatSum, PMF.bind_apply, translated_nat_pmf]
  have ht : (∑' a, p a * if a ≤ n then q (n - a) else 0) =
      ∑ a ∈ Finset.range (n + 1), p a * if a ≤ n then q (n - a) else 0 := by
    apply tsum_eq_sum
    intro a ha
    have hn : ¬ a ≤ n := by
      have hh : ¬ a < n + 1 := by simpa only [Finset.mem_range] using ha
      omega
    simp [hn]
  rw [ht]
  apply Finset.sum_congr rfl
  intro a ha
  rw [if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp ha))]

def borelForestPMF : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | k + 1 => independentNatSum (borelForestPMF k) borelPMF

/-- Coefficients identify the law of the explicitly constructed independent sum. -/
theorem borel_forest_pmf_coefficients (k n : ℕ) :
    borelForestPMF k n = ENNReal.ofReal (coeff ℝ n (borelSeries ^ k)) := by
  induction k generalizing n with
  | zero =>
    simp only [borelForestPMF, PMF.pure_apply, pow_zero, coeff_one]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [borelForestPMF, independent_nat_sum_apply, pow_succ, coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => coeff ℝ a (borelSeries ^ k) * coeff ℝ b borelSeries) n]
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro a ha
      rw [ih, borel_pmf_apply, borelCoefficient, ENNReal.ofReal_mul
        (tree_coeff_pow_nonnegative borelSeries borel_coefficient_nonnegative k a)]
    · intro a ha
      exact mul_nonneg (tree_coeff_pow_nonnegative borelSeries borel_coefficient_nonnegative k a)
        (borel_coefficient_nonnegative (n - a))

theorem borel_independent_forest_probabilities (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    borelForestPMF k n = ENNReal.ofReal
      (Real.exp (-(n : ℝ)) * ((k : ℝ) / (n : ℝ) *
        (n : ℝ) ^ (n - k) / ((n - k).factorial : ℝ))) := by
  rw [borel_forest_pmf_coefficients, borel_forest_coefficients n k hk hkn]


theorem borel_independent_forest_below (n k : ℕ) (hn : n < k) :
    borelForestPMF k n = 0 := by
  rw [borel_forest_pmf_coefficients,
    tree_power_coeff_above ℝ borelSeries borel_series_constant n k hn, ENNReal.ofReal_zero]

/-- The PMF convolution is the pushforward of the actual product measure. -/
theorem independent_nat_sum_measure (p q : PMF ℕ) :
    (p.toMeasure.prod q.toMeasure).map (fun x : ℕ × ℕ => x.1 + x.2) =
      (independentNatSum p q).toMeasure := by
  ext s hs
  rw [Measure.map_apply (measurable_fst.add measurable_snd) hs,
    Measure.prod_apply ((measurable_fst.add measurable_snd) hs),
    independentNatSum, PMF.toMeasure_bind_apply _ _ _ hs, lintegral_countable']
  apply tsum_congr
  intro a
  rw [PMF.toMeasure_apply_singleton p a (measurableSet_singleton a),
    PMF.toMeasure_map_apply (fun b : ℕ => a + b) q s
      (measurable_const.add measurable_id) hs]
  exact mul_comm _ _

/-- Arbitrary supplied independent random variables have the constructed sum law. -/
theorem independent_nat_sum_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℕ)
    (hX : Measurable X) (hY : Measurable Y)
    (hI : ProbabilityTheory.IndepFun X Y μ) (p q : PMF ℕ)
    (hp : μ.map X = p.toMeasure) (hq : μ.map Y = q.toMeasure) :
    μ.map (fun ω => X ω + Y ω) = (independentNatSum p q).toMeasure := by
  have hi := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    hX.aemeasurable hY.aemeasurable).mp hI
  rw [hp, hq] at hi
  rw [← independent_nat_sum_measure, ← hi,
    Measure.map_map (measurable_fst.add measurable_snd) (hX.prod_mk hY)]
  rfl

/-- No canonical sample-space assumption: every finite independent Borel family
has the previously computed forest distribution. -/
theorem borel_independent_finset_law {Ω ι : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℕ)
    (hX : ∀ i, Measurable (X i))
    (hI : ProbabilityTheory.iIndepFun (fun _ => inferInstance) X μ)
    (hL : ∀ i, μ.map (X i) = borelProbability) (s : Finset ι) :
    μ.map (fun ω => ∑ i ∈ s, X i ω) = (borelForestPMF s.card).toMeasure := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.card_empty, borelForestPMF]
    rw [PMF.toMeasure_pure, Measure.map_const, measure_univ, one_smul]
  | @insert i s hi ih =>
    have hs : Measurable (fun ω => ∑ j ∈ s, X j ω) :=
      Finset.measurable_sum s (fun j _ => hX j)
    have hind : ProbabilityTheory.IndepFun (fun ω => ∑ j ∈ s, X j ω) (X i) μ := by
      have he : (∑ j ∈ s, X j) = fun ω => ∑ j ∈ s, X j ω := by
        funext ω
        simp only [Finset.sum_apply]
      rw [← he]
      exact hI.indepFun_finset_sum_of_not_mem hX hi
    have hh := independent_nat_sum_law μ _ (X i) hs (hX i) hind
      (borelForestPMF s.card) borelPMF ih (hL i)
    simpa only [Finset.card_insert_of_not_mem hi, borelForestPMF,
      Finset.sum_insert hi, add_comm] using hh

theorem borel_independent_sum_probabilities {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (k n : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (X : Fin k → Ω → ℕ) (hX : ∀ i, Measurable (X i))
    (hI : ProbabilityTheory.iIndepFun (fun _ => inferInstance) X μ)
    (hL : ∀ i, μ.map (X i) = borelProbability) :
    μ {ω | ∑ i, X i ω = n} = ENNReal.ofReal
      (Real.exp (-(n : ℝ)) * ((k : ℝ) / (n : ℝ) *
        (n : ℝ) ^ (n - k) / ((n - k).factorial : ℝ))) := by
  have he : μ.map (fun ω => ∑ i, X i ω) = (borelForestPMF k).toMeasure := by
    simpa using borel_independent_finset_law μ X hX hI hL Finset.univ
  have hm : Measurable (fun ω => ∑ i, X i ω) :=
    Finset.measurable_sum Finset.univ (fun i _ => hX i)
  have hv := congrArg (fun ν : Measure ℕ => ν {n}) he
  dsimp only at hv
  rw [Measure.map_apply hm (measurableSet_singleton n),
    PMF.toMeasure_apply_singleton _ n (measurableSet_singleton n),
    borel_independent_forest_probabilities n k hk hkn] at hv
  exact hv

end
end Sigma
