import SigmaProbInverse
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros

namespace Sigma
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology

def complexMGF (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (z*(t : ℂ)) ∂μ

def mgfStrip (c : ℝ) : Set ℂ := {z | |z.re| < c}

theorem exp_abs_integrable_of_two_real_mgfs (μ : Measure ℝ) (c : ℝ)
    (hp : Integrable (fun t : ℝ => Real.exp (c*t)) μ)
    (hm : Integrable (fun t : ℝ => Real.exp (-c*t)) μ) :
    Integrable (fun t : ℝ => Real.exp (c*|t|)) μ := by
  apply (hp.add hm).mono' ((continuous_const.mul continuous_id.abs).rexp.aestronglyMeasurable)
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  change Real.exp (c*|t|) ≤ Real.exp (c*t) + Real.exp (-c*t)
  rcases le_or_lt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_neg ht]
    have he : c*(-t) = -c*t := by ring
    rw [he]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

theorem weighted_exp_abs_integrable (μ : Measure ℝ) {b c : ℝ} (hbc : b < c)
    (hc : Integrable (fun t : ℝ => Real.exp (c*|t|)) μ) :
    Integrable (fun t : ℝ => |t| *Real.exp (b*|t|)) μ := by
  let d : ℝ := c-b
  have hd : 0 < d := sub_pos.mpr hbc
  apply (hc.const_mul d⁻¹).mono'
    ((continuous_id.abs.mul (continuous_const.mul continuous_id.abs).rexp).aestronglyMeasurable)
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)]
  have hw : |t| ≤ Real.exp (d*|t|)/d := by
    apply (le_div_iff₀ hd).mpr
    have he := Real.add_one_le_exp (d*|t|)
    nlinarith
  calc
    |t| *Real.exp (b*|t|) ≤ (Real.exp (d*|t|)/d)*Real.exp (b*|t|) :=
      mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
    _ = d⁻¹*(Real.exp (d*|t|)*Real.exp (b*|t|)) := by rw [div_eq_mul_inv]; ring
    _ = d⁻¹*Real.exp (c*|t|) := by
      rw [← Real.exp_add]
      congr 2
      dsimp [d]
      ring

theorem complex_mgf_integrable_of_exp_abs (μ : Measure ℝ) {c : ℝ}
    (hc : Integrable (fun t : ℝ => Real.exp (c*|t|)) μ) (z : ℂ) (hz : |z.re| ≤ c) :
    Integrable (fun t : ℝ => Complex.exp (z*(t : ℂ))) μ := by
  apply hc.mono' ((continuous_const.mul Complex.continuous_ofReal).cexp.aestronglyMeasurable)
  filter_upwards with t
  rw [Complex.norm_eq_abs, Complex.abs_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  calc
    z.re*t ≤ |z.re*t| := le_abs_self _
    _ = |z.re| *|t| := abs_mul _ _
    _ ≤ c*|t| := mul_le_mul_of_nonneg_right hz (abs_nonneg _)

theorem complex_mgf_differentiable_at (μ : Measure ℝ) {c : ℝ}
    (hc : Integrable (fun t : ℝ => Real.exp (c*|t|)) μ) (z : ℂ) (hz : |z.re| < c) :
    DifferentiableAt ℂ (complexMGF μ) z := by
  let e : ℝ := (c-|z.re|)/2
  let b : ℝ := |z.re|+e
  have he : 0 < e := by dsimp [e]; linarith
  have hbc : b < c := by dsimp [b,e]; linarith
  have hbound := weighted_exp_abs_integrable μ hbc hc
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (ε := e)
    (F := fun w : ℂ => fun t : ℝ => Complex.exp (w*(t : ℂ)))
    (F' := fun w : ℂ => fun t : ℝ => Complex.exp (w*(t : ℂ))*(t : ℂ))
    (x₀ := z) (bound := fun t : ℝ => |t| *Real.exp (b*|t|)) he
    (Eventually.of_forall fun w =>
      (continuous_const.mul Complex.continuous_ofReal).cexp.aestronglyMeasurable)
    (complex_mgf_integrable_of_exp_abs μ hc z hz.le)
    (((continuous_const.mul Complex.continuous_ofReal).cexp.mul
      Complex.continuous_ofReal).aestronglyMeasurable) ?_ hbound ?_
  · exact hder.2.differentiableAt
  · apply Eventually.of_forall
    intro t w hw
    have hd : |(w-z).re| < e := lt_of_le_of_lt (Complex.abs_re_le_abs _)
      (by simpa only [mem_ball, dist_eq_norm, Complex.norm_eq_abs] using hw)
    have hwre : |w.re| ≤ b := by
      have hh := abs_add_le (w.re-z.re) z.re
      simp only [Complex.sub_re] at hd
      dsimp [b]
      have hrew : w.re-z.re+z.re = w.re := by ring
      rw [hrew] at hh
      linarith
    rw [norm_mul, Complex.norm_eq_abs, Complex.abs_exp, Complex.norm_real, Real.norm_eq_abs,
      mul_comm]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc
      w.re*t ≤ |w.re*t| := le_abs_self _
      _ = |w.re| * |t| := abs_mul _ _
      _ ≤ b*|t| := mul_le_mul_of_nonneg_right hwre (abs_nonneg _)
  · apply Eventually.of_forall
    intro t w hw
    simpa using ((hasDerivAt_id w).mul_const (t : ℂ)).cexp

theorem mgf_strip_open (c : ℝ) : IsOpen (mgfStrip c) :=
  isOpen_lt Complex.continuous_re.abs continuous_const

theorem mgf_strip_convex (c : ℝ) : Convex ℝ (mgfStrip c) := by
  convert (convex_Ioo (-c) c).linear_preimage Complex.reLm using 1
  ext z
  simp [mgfStrip, abs_lt]

theorem complex_mgf_analytic (μ : Measure ℝ) {c : ℝ}
    (hc : Integrable (fun t : ℝ => Real.exp (c*|t|)) μ) :
    AnalyticOnNhd ℂ (complexMGF μ) (mgfStrip c) := by
  apply DifferentiableOn.analyticOnNhd _ (mgf_strip_open c)
  intro z hz
  exact (complex_mgf_differentiable_at μ hc z hz).differentiableWithinAt

theorem complex_mgf_ofReal (μ : Measure ℝ) (s : ℝ) :
    complexMGF μ (Complex.ofReal s) =
      Complex.ofReal (∫ t : ℝ, Real.exp (s*t) ∂μ) := by
  unfold complexMGF
  have he : (fun t : ℝ => Complex.exp (Complex.ofReal s*(t : ℂ))) =
      fun t : ℝ => Complex.ofReal (Real.exp (s*t)) := by
    funext t
    rw [Complex.ofReal_exp, Complex.ofReal_mul]
  rw [he]
  exact (@RCLike.ofRealLI ℂ _).integral_comp_comm (fun t : ℝ => Real.exp (s*t))

theorem complex_mgf_imaginary (μ : Measure ℝ) (x : ℝ) :
    complexMGF μ (Complex.I*(x : ℂ)) = probabilityCharacteristic μ x := by
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  push_cast
  ring

/-- Actual finite measures with finite real MGFs on a common open interval about
zero are identified by equality of those observed MGFs on that interval. -/
theorem finite_measure_local_mgf_unique (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (a : ℝ) (ha : 0 < a)
    (hμ : ∀ s : ℝ, |s| < a → Integrable (fun t : ℝ => Real.exp (s*t)) μ)
    (hν : ∀ s : ℝ, |s| < a → Integrable (fun t : ℝ => Real.exp (s*t)) ν)
    (hm : ∀ s : ℝ, |s| < a → (∫ t : ℝ, Real.exp (s*t) ∂μ) =
      ∫ t : ℝ, Real.exp (s*t) ∂ν) : μ = ν := by
  let c : ℝ := a/2
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hca : c < a := by dsimp [c]; linarith
  have hc : |c| < a := by rwa [abs_of_pos hc0]
  have hnc : |-c| < a := by simpa using hc
  have hμe := exp_abs_integrable_of_two_real_mgfs μ c (hμ c hc) (hμ (-c) hnc)
  have hνe := exp_abs_integrable_of_two_real_mgfs ν c (hν c hc) (hν (-c) hnc)
  have hzero : (0 : ℂ) ∈ mgfStrip c := by simpa [mgfStrip] using hc0
  have hclosure : (0 : ℂ) ∈ closure ({z | complexMGF μ z = complexMGF ν z} \ {0}) := by
    have hlimR : Tendsto (fun n : ℕ => c/((n : ℝ)+1)) atTop (𝓝 0) := by
      have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
        (tendsto_const_nhds (x := (1 : ℝ)))
      simpa [div_eq_mul_inv] using ht.inv_tendsto_atTop.const_mul c
    have hlimC : Tendsto (fun n : ℕ => Complex.ofReal (c/((n : ℝ)+1))) atTop (𝓝 0) := by
      have h := Complex.continuous_ofReal.continuousAt.tendsto.comp hlimR
      simpa only [Function.comp_def, Complex.ofReal_zero] using h
    apply mem_closure_of_tendsto hlimC
    apply Eventually.of_forall
    intro n
    have hn : 0 < (n : ℝ)+1 := by positivity
    have hp : 0 < c/((n : ℝ)+1) := div_pos hc0 hn
    have hle : c/((n : ℝ)+1) ≤ c := by
      apply (div_le_iff₀ hn).mpr
      nlinarith [(show (0 : ℝ) ≤ n by positivity)]
    have hsa : |c/((n : ℝ)+1)| < a := by rw [abs_of_pos hp]; exact hle.trans_lt hca
    constructor
    · change complexMGF μ (Complex.ofReal _) = complexMGF ν (Complex.ofReal _)
      rw [complex_mgf_ofReal, complex_mgf_ofReal, hm _ hsa]
    · exact fun he => hp.ne' (Complex.ofReal_injective he)
  have heq := (complex_mgf_analytic μ hμe).eqOn_of_preconnected_of_mem_closure
    (complex_mgf_analytic ν hνe) (mgf_strip_convex c).isPreconnected hzero hclosure
  apply finite_measure_characteristic_unique μ ν
  intro x
  have hxi : Complex.I*(x : ℂ) ∈ mgfStrip c := by simpa [mgfStrip] using hc0
  simpa only [complex_mgf_imaginary] using heq hxi

end
end Sigma
