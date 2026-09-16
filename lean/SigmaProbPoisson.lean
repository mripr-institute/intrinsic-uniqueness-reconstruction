import SigmaProbResidual
import Mathlib.Probability.Distributions.Poisson
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

theorem pmf_real_mass (p : PMF ℕ) : HasSum (fun n => (p n).toReal) 1 := by
  have hs := ENNReal.hasSum_toReal p.tsum_coe_ne_top
  rw [← ENNReal.tsum_toReal_eq p.apply_ne_top, p.tsum_coe] at hs
  simpa using hs

theorem pmf_integrable_of_summable (p : PMF ℕ) (f : ℕ → ℝ)
    (hs : Summable (fun n => ‖f n‖ * (p n).toReal)) : Integrable f p.toMeasure := by
  refine ⟨(measurable_of_countable f).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm, lintegral_countable']
  have he : (fun n => ENNReal.ofReal ‖f n‖ * p.toMeasure {n}) =
      (fun n => ENNReal.ofReal (‖f n‖ * (p n).toReal)) := by
    funext n
    rw [PMF.toMeasure_apply_singleton p n (measurableSet_singleton n),
      ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_toReal (p.apply_ne_top n)]
  rw [he, ← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (norm_nonneg _) ENNReal.toReal_nonneg) hs]
  exact ENNReal.ofReal_lt_top

theorem poisson_probability_recurrence (p : PMF ℕ)
    (hrec : ∀ n, ((n+1 : ℕ) : ℝ) * (p (n+1)).toReal = (p n).toReal) :
    p = ProbabilityTheory.poissonPMF 1 := by
  apply PMF.ext
  intro n
  have hn := SigmaPresentations.poisson_normalized_recurrence (fun n => (p n).toReal)
    hrec (pmf_real_mass p) n
  rw [← ENNReal.ofReal_toReal (p.apply_ne_top n), hn]
  change ENNReal.ofReal _ = ENNReal.ofReal (ProbabilityTheory.poissonPMFReal 1 n)
  simp [ProbabilityTheory.poissonPMFReal]

theorem poisson_one_mass (n : ℕ) :
    (ProbabilityTheory.poissonPMF 1 n).toReal = Real.exp (-1) / (n.factorial : ℝ) := by
  change (ENNReal.ofReal (ProbabilityTheory.poissonPMFReal 1 n)).toReal = _
  rw [ENNReal.toReal_ofReal ProbabilityTheory.poissonPMFReal_nonneg]
  simp [ProbabilityTheory.poissonPMFReal]

theorem poisson_one_recurrence (n : ℕ) :
    ((n+1 : ℕ) : ℝ) * (ProbabilityTheory.poissonPMF 1 (n+1)).toReal =
      (ProbabilityTheory.poissonPMF 1 n).toReal := by
  rw [poisson_one_mass, poisson_one_mass, Nat.factorial_succ, Nat.cast_mul]
  field_simp
  ring

theorem poisson_exponential_integrable (u : ℝ) :
    Integrable (fun n : ℕ => Real.exp ((n : ℝ)*u)) (ProbabilityTheory.poissonMeasure 1) := by
  apply pmf_integrable_of_summable
  have hs := (SigmaPresentations.poisson_mgf_hasSum u).summable
  convert hs using 1
  funext n
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), poisson_one_mass]
  ring

theorem poisson_probability_mgf (u : ℝ) :
    (∫ n : ℕ, Real.exp ((n : ℝ)*u) ∂ProbabilityTheory.poissonMeasure 1) =
      Real.exp (Real.exp u - 1) := by
  rw [ProbabilityTheory.poissonMeasure,
    PMF.integral_eq_tsum _ _ (poisson_exponential_integrable u)]
  simpa only [smul_eq_mul, poisson_one_mass] using (SigmaPresentations.poisson_mgf_hasSum u).tsum_eq

theorem poisson_probability_cgf (u : ℝ) :
    Real.log (∫ n : ℕ, Real.exp ((n : ℝ)*u) ∂ProbabilityTheory.poissonMeasure 1) =
      Real.exp u - 1 := by rw [poisson_probability_mgf, Real.log_exp]

theorem poisson_centered_probability_mgf (u : ℝ) :
    (∫ n : ℕ, Real.exp (((n : ℝ)-1)*u) ∂ProbabilityTheory.poissonMeasure 1) =
      Real.exp (SigmaPresentations.centeredCGF u) := by
  have he : (fun n : ℕ => Real.exp (((n : ℝ)-1)*u)) =
      fun n : ℕ => Real.exp (-u) * Real.exp ((n : ℝ)*u) := by
    funext n
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, integral_mul_left, poisson_probability_mgf, ← Real.exp_add]
  congr 1
  unfold SigmaPresentations.centeredCGF
  ring

theorem poisson_centered_probability_cgf (u : ℝ) :
    Real.log (∫ n : ℕ, Real.exp (((n : ℝ)-1)*u) ∂ProbabilityTheory.poissonMeasure 1) =
      SigmaPresentations.centeredCGF u := by rw [poisson_centered_probability_mgf, Real.log_exp]

theorem centered_shift_cancels (n k : ℕ) :
    ((n+k : ℕ) : ℝ) - ((k : ℝ)+1) = (n : ℝ)-1 := by push_cast; ring

theorem poisson_mean_hasSum :
    HasSum (fun n : ℕ => (n : ℝ) * (ProbabilityTheory.poissonPMF 1 n).toReal) 1 := by
  have hs : HasSum (fun n : ℕ => ((n+1 : ℕ) : ℝ) *
      (ProbabilityTheory.poissonPMF 1 (n+1)).toReal) 1 := by
    simpa only [poisson_one_recurrence] using pmf_real_mass (ProbabilityTheory.poissonPMF 1)
  have hh := (hasSum_nat_add_iff
    (f := fun n : ℕ => (n : ℝ) * (ProbabilityTheory.poissonPMF 1 n).toReal)
    (g := (1 : ℝ)) 1).mp hs
  simpa only [Finset.sum_range_one, Nat.cast_zero, zero_mul, add_zero] using hh

theorem poisson_identity_integrable :
    Integrable (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure 1) := by
  apply pmf_integrable_of_summable
  convert poisson_mean_hasSum.summable using 1
  funext n
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]

theorem poisson_probability_mean :
    (∫ n : ℕ, (n : ℝ) ∂ProbabilityTheory.poissonMeasure 1) = 1 := by
  rw [ProbabilityTheory.poissonMeasure,
    PMF.integral_eq_tsum _ _ poisson_identity_integrable]
  simpa only [smul_eq_mul, mul_comm] using poisson_mean_hasSum.tsum_eq

def shiftedPoissonProbability (k : ℕ) : Measure ℕ :=
  Measure.map (fun n : ℕ => n+k) (ProbabilityTheory.poissonMeasure 1)

instance shiftedPoissonProbability_is_probability (k : ℕ) :
    IsProbabilityMeasure (shiftedPoissonProbability k) :=
  MeasureTheory.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem shifted_poisson_mean (k : ℕ) :
    (∫ n : ℕ, (n : ℝ) ∂shiftedPoissonProbability k) = (k : ℝ)+1 := by
  rw [shiftedPoissonProbability, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  simp only [Nat.cast_add]
  rw [integral_add poisson_identity_integrable (integrable_const _),
    poisson_probability_mean, integral_const]
  simp
  ring

theorem shifted_poisson_centered_cgf (k : ℕ) (u : ℝ) :
    Real.log (∫ n : ℕ, Real.exp (((n : ℝ) -
      (∫ m : ℕ, (m : ℝ) ∂shiftedPoissonProbability k))*u)
      ∂shiftedPoissonProbability k) = SigmaPresentations.centeredCGF u := by
  rw [shifted_poisson_mean, shiftedPoissonProbability,
    integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
  simpa only [centered_shift_cancels] using poisson_centered_probability_cgf u

theorem shifted_poisson_not_original (k : ℕ) (hk : 0 < k) :
    shiftedPoissonProbability k ≠ ProbabilityTheory.poissonMeasure 1 := by
  intro he
  have hm := shifted_poisson_mean k
  rw [he, poisson_probability_mean] at hm
  have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  linarith

end
end Sigma
