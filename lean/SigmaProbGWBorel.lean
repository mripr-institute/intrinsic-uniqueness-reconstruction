import SigmaRealTreesOffspring
import SigmaProbPoisson
import SigmaProbTreeConditioning

namespace Sigma
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem nat_probability_generating_summable (p : PMF ℕ) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Summable (fun n => (p n).toReal*s^n) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hs0 n))
    (fun n => ?_) (pmf_real_mass p).summable
  exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ hs0 hs1)

theorem nat_probability_generating_nonnegative (p : PMF ℕ) (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ natProbabilityGenerating p s :=
  tsum_nonneg fun n => mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hs n)

theorem nat_probability_generating_le_one (p : PMF ℕ) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : natProbabilityGenerating p s ≤ 1 := by
  rw [← (pmf_real_mass p).tsum_eq]
  exact tsum_le_tsum (fun n => mul_le_of_le_one_right ENNReal.toReal_nonneg
    (pow_le_one₀ hs0 hs1)) (nat_probability_generating_summable p s hs0 hs1)
    (pmf_real_mass p).summable

theorem borel_native_pgf (s : ℝ) :
    natProbabilityGenerating borelPMF s = borelGenerating s := by
  rw [borel_generating_is_pgf]
  exact tsum_congr fun n => mul_comm _ _

/-- Within the probability range, the Borel equation has exactly the canonical
solution. This uses the proved strict monotonicity of its scalar inverse. -/
theorem borel_fixed_point_unique (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (he : t = s*Real.exp (t-1)) :
    t = borelGenerating s := by
  apply borel_inverse_strictMono.injOn ht
    ⟨borel_generating_nonnegative s hs.1,borel_generating_le_one s hs.1 hs.2⟩
  rw [borel_generating_right_inverse s hs]
  change t*Real.exp (1-t) = s
  calc
    t*Real.exp (1-t) = s*(Real.exp (t-1)*Real.exp (1-t)) := by
      linear_combination Real.exp (1-t)*he
    _ = s := by rw [← Real.exp_add]; simp

/-- A probability distribution solving the Poisson branching PGF equation is
the Borel law; normalization and the probability range are derived from `p`. -/
theorem nat_pgf_poisson_branching_identifies_borel (p : PMF ℕ)
    (he : ∀ s : ℝ, 0 < s → s < 1 →
      natProbabilityGenerating p s = s*Real.exp (natProbabilityGenerating p s-1)) :
    p = borelPMF := by
  apply native_pgf_identifies_nat_probability
  intro s hs0 hs1
  rw [borel_native_pgf]
  exact borel_fixed_point_unique s (natProbabilityGenerating p s) ⟨hs0.le,hs1.le⟩
    ⟨nat_probability_generating_nonnegative p s hs0.le,
      nat_probability_generating_le_one p s hs0.le hs1.le⟩ (he s hs0 hs1)

theorem nat_pgf_poisson_branching_iff (p : PMF ℕ) :
    p = borelPMF ↔ ∀ s : ℝ, 0 < s → s < 1 →
      natProbabilityGenerating p s = s*Real.exp (natProbabilityGenerating p s-1) := by
  constructor
  · rintro rfl s hs0 hs1
    simpa only [borel_native_pgf] using borel_generating_fixed_point s hs0.le hs1.le
  · exact nat_pgf_poisson_branching_identifies_borel p

theorem nat_probability_generating_integrable (p : PMF ℕ) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : Integrable (fun n : ℕ => s^n) p.toMeasure := by
  apply pmf_integrable_of_summable
  simpa only [Real.norm_of_nonneg (pow_nonneg hs0 _),mul_comm] using
    nat_probability_generating_summable p s hs0 hs1

theorem nat_probability_generating_integral (p : PMF ℕ) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∫ n : ℕ, s^n ∂p.toMeasure) = natProbabilityGenerating p s := by
  simpa only [smul_eq_mul] using p.integral_eq_tsum (fun n : ℕ => s^n)
    (nat_probability_generating_integrable p s hs0 hs1)

theorem nat_probability_generating_lintegral (p : PMF ℕ) (s : ℝ≥0∞) :
    (∫⁻ n : ℕ, s^n ∂p.toMeasure) = ∑' n : ℕ, p n*s^n := by
  rw [lintegral_countable']
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),mul_comm]

theorem nat_probability_generating_lintegral_toReal (p : PMF ℕ) (s : ℝ≥0∞)
    (hs : s ≤ 1) :
    (∫⁻ n : ℕ, s^n ∂p.toMeasure).toReal = natProbabilityGenerating p s.toReal := by
  rw [nat_probability_generating_lintegral,nat_probability_generating_ennreal_toReal p s hs]

end
end Sigma
