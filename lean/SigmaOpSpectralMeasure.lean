import SigmaOpMoments
import Mathlib.MeasureTheory.Measure.Dirac

namespace Sigma
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology

/-- The actual weighted atomic measure used by the integer trace inverse.
The index type retains repetitions, hence eigenvalue multiplicities. -/
def spectralWeightedMeasure {ι : Type*} (x : ι → OpUnitInterval) (q : ℕ) :
    Measure OpUnitInterval :=
  Measure.sum (fun i => ENNReal.ofReal ((x i : ℝ)^q) • Measure.dirac (x i))

theorem spectral_weighted_measure_finite {ι : Type*} (x : ι → OpUnitInterval)
    (q : ℕ) (hx : Summable (fun i => (x i : ℝ)^q)) :
    IsFiniteMeasure (spectralWeightedMeasure x q) := by
  constructor
  rw [spectralWeightedMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => pow_nonneg (x i).property.1 q) hx]
  exact ENNReal.ofReal_lt_top

theorem spectral_weighted_measure_moment {ι : Type*} (x : ι → OpUnitInterval)
    (q : ℕ) (hx : Summable (fun i => (x i : ℝ)^q)) (n : ℕ) :
    (∫ y : OpUnitInterval, (y : ℝ)^n ∂spectralWeightedMeasure x q) =
      ∑' i, (x i : ℝ)^(n+q) := by
  letI := spectral_weighted_measure_finite x q hx
  have hi : Integrable (fun y : OpUnitInterval => (y : ℝ)^n)
      (spectralWeightedMeasure x q) :=
    op_continuous_integrable _ ⟨_, continuous_subtype_val.pow n⟩
  rw [spectralWeightedMeasure, integral_sum_measure hi]
  apply tsum_congr
  intro i
  simp only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (pow_nonneg (x i).property.1 q),
    smul_eq_mul, pow_add]
  ring

theorem spectral_weighted_measure_unique {ι κ : Type*}
    (x : ι → OpUnitInterval) (y : κ → OpUnitInterval) (q : ℕ)
    (hx : Summable (fun i => (x i : ℝ)^q))
    (hy : Summable (fun j => (y j : ℝ)^q))
    (hm : ∀ n : ℕ, (∑' i, (x i : ℝ)^(n+q)) = ∑' j, (y j : ℝ)^(n+q)) :
    spectralWeightedMeasure x q = spectralWeightedMeasure y q := by
  letI := spectral_weighted_measure_finite x q hx
  letI := spectral_weighted_measure_finite y q hy
  apply operator_hausdorff_moment_unique
  intro n
  rw [spectral_weighted_measure_moment x q hx, spectral_weighted_measure_moment y q hy, hm]

theorem spectral_weighted_measure_atom {ι : Type*} (x : ι → OpUnitInterval)
    (q : ℕ) (a : OpUnitInterval) :
    spectralWeightedMeasure x q {a} =
      ENNReal.ofReal ((a : ℝ)^q) * ∑' i, if x i = a then (1 : ℝ≥0∞) else 0 := by
  classical
  rw [spectralWeightedMeasure, Measure.sum_apply _ (measurableSet_singleton a),
    ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro i
  by_cases h : x i = a
  · simp [h]
  · simp [Measure.smul_apply, Measure.dirac_apply, h]

theorem spectral_weighted_measure_no_zero_atom {ι : Type*} (x : ι → OpUnitInterval)
    (q : ℕ) (hq : q ≠ 0) :
    spectralWeightedMeasure x q {⟨0, by constructor <;> norm_num⟩} = 0 := by
  rw [spectral_weighted_measure_atom]
  simp [hq]

theorem spectral_integer_moments_recover_multiplicities {ι κ : Type*}
    (x : ι → OpUnitInterval) (y : κ → OpUnitInterval) (q : ℕ)
    (hx : Summable (fun i => (x i : ℝ)^q))
    (hy : Summable (fun j => (y j : ℝ)^q))
    (hm : ∀ n : ℕ, (∑' i, (x i : ℝ)^(n+q)) = ∑' j, (y j : ℝ)^(n+q))
    (a : OpUnitInterval) (ha : (a : ℝ) ≠ 0) :
    (∑' i, if x i = a then (1 : ℝ≥0∞) else 0) =
      ∑' j, if y j = a then (1 : ℝ≥0∞) else 0 := by
  have he := congrArg (fun μ : Measure OpUnitInterval => μ {a})
    (spectral_weighted_measure_unique x y q hx hy hm)
  dsimp only at he
  rw [spectral_weighted_measure_atom, spectral_weighted_measure_atom] at he
  exact (ENNReal.mul_eq_mul_left (by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (pow_pos (lt_of_le_of_ne a.property.1 ha.symm) q)))
    ENNReal.ofReal_ne_top).mp he

theorem spectral_positive_fiber_finite {ι : Type*} (x : ι → OpUnitInterval)
    (q : ℕ) (hx : Summable (fun i => (x i : ℝ)^q))
    (a : OpUnitInterval) (ha : (a : ℝ) ≠ 0) : Finite {i // x i = a} := by
  have hs := hx.subtype {i | x i = a}
  have hc : Summable (fun _ : {i // x i = a} => (a : ℝ)^q) := by
    convert hs using 1
    funext i
    exact congrArg (fun z : OpUnitInterval => (z : ℝ)^q) i.property.symm
  exact Finite.of_summable_const
    (pow_pos (lt_of_le_of_ne a.property.1 ha.symm) q) hc

/-- The recovered atomic masses give a literal eigenvalue-preserving bijection,
including repeated values and finite or empty index types. -/
theorem spectral_integer_moments_equiv {ι κ : Type*}
    (x : ι → OpUnitInterval) (y : κ → OpUnitInterval) (q : ℕ)
    (hx : Summable (fun i => (x i : ℝ)^q))
    (hy : Summable (fun j => (y j : ℝ)^q))
    (hx0 : ∀ i, (x i : ℝ) ≠ 0) (hy0 : ∀ j, (y j : ℝ) ≠ 0)
    (hm : ∀ n : ℕ, (∑' i, (x i : ℝ)^(n+q)) = ∑' j, (y j : ℝ)^(n+q)) :
    ∃ e : ι ≃ κ, ∀ i, y (e i) = x i := by
  classical
  have he (a : OpUnitInterval) : Nonempty ({i // x i = a} ≃ {j // y j = a}) := by
    by_cases ha : (a : ℝ) = 0
    · have hxi : IsEmpty {i // x i = a} := ⟨fun i => hx0 i.val (by rw [i.property, ha])⟩
      have hyi : IsEmpty {j // y j = a} := ⟨fun j => hy0 j.val (by rw [j.property, ha])⟩
      exact ⟨Equiv.equivOfIsEmpty _ _⟩
    · letI := spectral_positive_fiber_finite x q hx a ha
      letI := spectral_positive_fiber_finite y q hy a ha
      letI := Fintype.ofFinite {i // x i = a}
      letI := Fintype.ofFinite {j // y j = a}
      have hc := spectral_integer_moments_recover_multiplicities x y q hx hy hm a ha
      have hcx : (∑' i, if x i = a then (1 : ℝ≥0∞) else 0) =
          Fintype.card {i // x i = a} := by
        simpa [Set.indicator, tsum_fintype] using
          (tsum_subtype {i | x i = a} (fun _ => (1 : ℝ≥0∞))).symm
      have hcy : (∑' j, if y j = a then (1 : ℝ≥0∞) else 0) =
          Fintype.card {j // y j = a} := by
        simpa [Set.indicator, tsum_fintype] using
          (tsum_subtype {j | y j = a} (fun _ => (1 : ℝ≥0∞))).symm
      rw [hcx, hcy] at hc
      exact ⟨Fintype.equivOfCardEq (by exact_mod_cast hc)⟩
  let e := Equiv.ofFiberEquiv (fun a => (he a).some)
  exact ⟨e, Equiv.ofFiberEquiv_map _⟩

end
end Sigma
