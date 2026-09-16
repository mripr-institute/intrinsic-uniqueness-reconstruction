import SigmaRealTreesInverse
import Mathlib.Probability.Distributions.Poisson

namespace Sigma
noncomputable section
open MeasureTheory PowerSeries Set Filter
open scoped Topology BigOperators

def natProbabilityGenerating (q : PMF ℕ) (s : ℝ) : ℝ :=
  ∑' n, (q n).toReal * s ^ n

def natProbabilityAnalyticSeries (q : PMF ℕ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun n => (q n).toReal)

theorem nat_probability_generating_sum (q : PMF ℕ) :
    (natProbabilityAnalyticSeries q).sum = natProbabilityGenerating q := by
  funext s
  exact FormalMultilinearSeries.ofScalars_sum_eq _ s

theorem nat_probability_series_radius (q : PMF ℕ) :
    1 ≤ (natProbabilityAnalyticSeries q).radius := by
  apply (natProbabilityAnalyticSeries q).le_radius_of_bound (r := (1 : NNReal)) 1
  intro n
  simp only [natProbabilityAnalyticSeries, FormalMultilinearSeries.ofScalars_norm,
    NNReal.coe_one, one_pow, mul_one, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top (q.coe_le_one n)

theorem nat_probability_generating_analytic (q : PMF ℕ) (s : ℝ) (hs : |s| < 1) :
    AnalyticAt ℝ (natProbabilityGenerating q) s := by
  have hr : 0 < (natProbabilityAnalyticSeries q).radius :=
    lt_of_lt_of_le (by norm_num) (nat_probability_series_radius q)
  rw [← nat_probability_generating_sum]
  apply ((natProbabilityAnalyticSeries q).hasFPowerSeriesOnBall hr).analyticAt_of_mem
  rw [EMetric.mem_ball, edist_dist, Real.dist_eq, sub_zero]
  exact lt_of_lt_of_le (by simpa using (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr hs)
    (nat_probability_series_radius q)

theorem native_pgf_identifies_nat_probability (q r : PMF ℕ)
    (he : ∀ s : ℝ, 0 < s → s < 1 → natProbabilityGenerating q s = natProbabilityGenerating r s) :
    q = r := by
  have hq : AnalyticOnNhd ℝ (natProbabilityGenerating q) (Ioo (-1) 1) :=
    fun s hs => nat_probability_generating_analytic q s (abs_lt.mpr hs)
  have hr : AnalyticOnNhd ℝ (natProbabilityGenerating r) (Ioo (-1) 1) :=
    fun s hs => nat_probability_generating_analytic r s (abs_lt.mpr hs)
  have hg : natProbabilityGenerating q =ᶠ[𝓝 (1 / 2 : ℝ)] natProbabilityGenerating r := by
    filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 1 by norm_num)] with s hs
    exact he s hs.1 hs.2
  have hall := hq.eqOn_of_preconnected_of_eventuallyEq hr (convex_Ioo (-1 : ℝ) 1).isPreconnected
    (show (1 / 2 : ℝ) ∈ Ioo (-1) 1 by norm_num) hg
  have hg0 : natProbabilityGenerating q =ᶠ[𝓝 (0 : ℝ)] natProbabilityGenerating r := by
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact hall hs
  have hqs := ((natProbabilityAnalyticSeries q).hasFPowerSeriesOnBall
    (lt_of_lt_of_le (by norm_num) (nat_probability_series_radius q))).hasFPowerSeriesAt
  have hrs := ((natProbabilityAnalyticSeries r).hasFPowerSeriesOnBall
    (lt_of_lt_of_le (by norm_num) (nat_probability_series_radius r))).hasFPowerSeriesAt
  rw [nat_probability_generating_sum] at hqs hrs
  have hser := hqs.eq_formalMultilinearSeries_of_eventually hrs hg0
  have hc := FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ hser
  apply PMF.ext
  intro n
  exact (ENNReal.toReal_eq_toReal (q.apply_ne_top n) (r.apply_ne_top n)).mp (congrFun hc n)

theorem poisson_one_native_pgf (s : ℝ) :
    natProbabilityGenerating (ProbabilityTheory.poissonPMF 1) s = Real.exp (s - 1) := by
  have hexp : HasSum (fun n : ℕ => s ^ n / (n.factorial : ℝ)) (Real.exp s) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp ℝ s
  have hs := hexp.mul_left (Real.exp (-1))
  have he : Real.exp (-1) * Real.exp s = Real.exp (s - 1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hs
  unfold natProbabilityGenerating
  rw [← hs.tsum_eq]
  apply tsum_congr
  intro n
  change (ENNReal.ofReal (ProbabilityTheory.poissonPMFReal 1 n)).toReal * s ^ n = _
  rw [ENNReal.toReal_ofReal ProbabilityTheory.poissonPMFReal_nonneg]
  simp only [ProbabilityTheory.poissonPMFReal, NNReal.coe_one, one_pow, mul_one]
  ring

/-- The conditioning equation is exposed explicitly here; deriving it from a native
Galton--Watson construction is a separate obligation. The law and its PGF are native. -/
theorem offspring_pgf_equation_identifies_poisson (q : PMF ℕ)
    (hcondition : ∀ s : ℝ, 0 < s → s < 1 →
      borelGenerating s = s * natProbabilityGenerating q (borelGenerating s)) :
    q = ProbabilityTheory.poissonPMF 1 := by
  apply native_pgf_identifies_nat_probability
  intro w hw0 hw1
  have hw : w ∈ Icc 0 1 := ⟨hw0.le,hw1.le⟩
  have hs0 : 0 < borelInverse w := by
    have h := borel_inverse_strictMono (show (0 : ℝ) ∈ Icc 0 1 by norm_num) hw hw0
    simpa [borelInverse] using h
  have hs1 : borelInverse w < 1 := by
    have h := borel_inverse_strictMono hw (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hw1
    simpa [borelInverse] using h
  have hq := hcondition (borelInverse w) hs0 hs1
  have hb := borel_generating_fixed_point (borelInverse w) hs0.le hs1.le
  rw [borel_generating_left_inverse w hw] at hq hb
  rw [poisson_one_native_pgf]
  exact mul_left_cancel₀ hs0.ne' (hq.symm.trans hb)

theorem poisson_offspring_pgf_equation :
    ∀ s : ℝ, 0 < s → s < 1 → borelGenerating s =
      s * natProbabilityGenerating (ProbabilityTheory.poissonPMF 1) (borelGenerating s) := by
  intro s hs0 hs1
  rw [poisson_one_native_pgf]
  exact borel_generating_fixed_point s hs0.le hs1.le

theorem native_offspring_pgf_characterization (q : PMF ℕ) :
    q = ProbabilityTheory.poissonPMF 1 ↔ ∀ s : ℝ, 0 < s → s < 1 →
      borelGenerating s = s * natProbabilityGenerating q (borelGenerating s) := by
  constructor
  · rintro rfl
    exact poisson_offspring_pgf_equation
  · exact offspring_pgf_equation_identifies_poisson q

end
end Sigma
