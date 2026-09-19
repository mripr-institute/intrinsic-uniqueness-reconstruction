import SigmaProbCompletion
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

/-- The explicit family as a native probability measure, with its weak topology. -/
def gammaCompletionProbability (r : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨gammaCompletion r, gamma_completion_probability r⟩

/-- Scheffé's argument for normalized nonnegative densities. -/
theorem normalized_density_tendsto_l1 {ι α : Type*} [MeasurableSpace α]
    {l : Filter ι} [l.IsCountablyGenerated] {μ : Measure α}
    {p : ι → α → ℝ} {q : α → ℝ}
    (hq : Integrable q μ) (hq0 : ∀ᵐ x ∂μ, 0 ≤ q x) (hq1 : ∫ x, q x ∂μ = 1)
    (hp : ∀ᶠ i in l, Integrable (p i) μ ∧ (∀ᵐ x ∂μ, 0 ≤ p i x) ∧ ∫ x, p i x ∂μ = 1)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun i => p i x) l (𝓝 (q x))) :
    Tendsto (fun i => ∫ x, |p i x-q x| ∂μ) l (𝓝 0) := by
  have hm : Tendsto (fun i => ∫ x, min (p i x) (q x) ∂μ) l (𝓝 1) := by
    rw [← hq1]
    apply tendsto_integral_filter_of_dominated_convergence q
    · filter_upwards [hp] with i hi
      exact (hi.1.inf hq).aestronglyMeasurable
    · filter_upwards [hp] with i hi
      filter_upwards [hi.2.1, hq0] with x hx hqx
      rw [Real.norm_of_nonneg (le_min hx hqx)]
      exact min_le_right _ _
    · exact hq
    · filter_upwards [ht] with x hx
      simpa using hx.min (tendsto_const_nhds (x := q x))
  have he : (fun i => ∫ x, |p i x-q x| ∂μ) =ᶠ[l]
      fun i => 2-2*(∫ x, min (p i x) (q x) ∂μ) := by
    filter_upwards [hp] with i hi
    have heq : (fun x => |p i x-q x|) =
        fun x => p i x+q x-2*min (p i x) (q x) := by
      funext x
      rcases le_total (p i x) (q x) with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
    rw [heq]
    have hsum : Integrable (fun x => p i x+q x) μ := hi.1.add hq
    have hmin : Integrable (fun x => 2*min (p i x) (q x)) μ := (hi.1.inf hq).const_mul 2
    rw [integral_sub hsum hmin, integral_add hi.1 hq, integral_mul_left, hi.2.2, hq1]
    ring
  apply Tendsto.congr' he.symm
  simpa using (tendsto_const_nhds (x := (2:ℝ))).sub
    ((tendsto_const_nhds (x := (2:ℝ))).mul hm)

theorem bounded_integral_tendsto_of_l1 {ι α : Type*} [MeasurableSpace α]
    {l : Filter ι} {μ : Measure α} {p : ι → α → ℝ} {q f : α → ℝ}
    (hq : Integrable q μ) (hp : ∀ᶠ i in l, Integrable (p i) μ)
    (hf : AEStronglyMeasurable f μ) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (ht : Tendsto (fun i => ∫ x, |p i x-q x| ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, f x*p i x ∂μ) l (𝓝 (∫ x, f x*q x ∂μ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun i => norm_nonneg _))
    (show ∀ᶠ i in l, ‖(∫ x, f x*p i x ∂μ)-(∫ x, f x*q x ∂μ)‖ ≤
      C*(∫ x, |p i x-q x| ∂μ) from ?_) (by simpa using tendsto_const_nhds.mul ht)
  filter_upwards [hp] with i hi
  rw [← integral_sub (hi.bdd_mul hf ⟨C,hC⟩) (hq.bdd_mul hf ⟨C,hC⟩)]
  calc
    _ ≤ ∫ x, ‖f x*p i x-f x*q x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, C*|p i x-q x| ∂μ := by
      apply integral_mono
        (((hi.bdd_mul hf ⟨C,hC⟩).sub (hq.bdd_mul hf ⟨C,hC⟩)).norm)
        (((hi.sub hq).abs).const_mul C)
      intro x
      change ‖f x*p i x-f x*q x‖ ≤ C*|p i x-q x|
      rw [← mul_sub, norm_mul, Real.norm_eq_abs (p i x-q x)]
      exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)
    _ = _ := integral_mul_left _ _

theorem gamma_pdf_integrable (a : ℝ) (ha : 0 < a) : Integrable (gammaPDFReal a 1) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_gammaPDFReal a 1).aestronglyMeasurable
    (ae_of_all _ (gammaPDFReal_nonneg ha (by norm_num)))).mp
  change (∫⁻ x, gammaPDF a 1 x) ≠ ∞
  rw [lintegral_gammaPDF_eq_one ha (by norm_num)]
  simp

theorem gamma_pdf_integral (a : ℝ) (ha : 0 < a) : ∫ x, gammaPDFReal a 1 x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (gammaPDFReal_nonneg ha (by norm_num)))
    (measurable_gammaPDFReal a 1).aestronglyMeasurable]
  change (∫⁻ x, gammaPDF a 1 x).toReal = 1
  rw [lintegral_gammaPDF_eq_one ha (by norm_num)]
  simp

theorem gamma_pdf_shape_continuousAt (a x : ℝ) (ha : 0 < a) (hx : x ≠ 0) :
    ContinuousAt (fun b : ℝ => gammaPDFReal b 1 x) a := by
  by_cases hxp : 0 ≤ x
  · have hxx : 0 < x := lt_of_le_of_ne hxp (Ne.symm hx)
    simp only [gammaPDFReal, if_pos hxp, Real.one_rpow, one_mul]
    have hg : ContinuousAt Real.Gamma a :=
      (Real.differentiableAt_Gamma (fun n => by
        have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
        linarith)).continuousAt
    have hp : ContinuousAt (fun b : ℝ => x^(b-1)) a := by
      simp only [Real.rpow_def_of_pos hxx]
      fun_prop
    exact ((continuousAt_const.div hg (Real.Gamma_pos_of_pos ha).ne').mul hp).mul
      continuousAt_const
  · simp only [gammaPDFReal, if_neg hxp]
    exact continuousAt_const

theorem gamma_shape_integral_density (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ) :
    (∫ t, f t ∂gammaMeasure a 1) = ∫ t, f t*gammaPDFReal a 1 t := by
  change (∫ t, f t ∂volume.withDensity
    (fun t => ((Real.toNNReal (gammaPDFReal a 1 t) : ℝ≥0) : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul
    ((measurable_gammaPDFReal a 1).real_toNNReal)]
  apply integral_congr_ae
  filter_upwards with t
  rw [NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (gammaPDFReal_nonneg ha (by norm_num) t), mul_comm]

theorem gamma_completion_continuousAt_positive (r : ℝ≥0) (hr : 0 < r) :
    ContinuousAt gammaCompletionProbability r := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have har : 0 < 2*(r:ℝ) := mul_pos (by norm_num) (NNReal.coe_pos.mpr hr)
  have hp : ∀ᶠ s : ℝ≥0 in 𝓝 r, 0 < s := eventually_gt_nhds hr
  have hl : Tendsto (fun s : ℝ≥0 =>
      ∫ x, |gammaPDFReal (2*(s:ℝ)) 1 x-gammaPDFReal (2*(r:ℝ)) 1 x|)
      (𝓝 r) (𝓝 0) := by
    apply normalized_density_tendsto_l1 (gamma_pdf_integrable _ har)
      (ae_of_all _ (gammaPDFReal_nonneg har (by norm_num))) (gamma_pdf_integral _ har)
    · filter_upwards [hp] with s hs
      have has : 0 < 2*(s:ℝ) := mul_pos (by norm_num) (NNReal.coe_pos.mpr hs)
      exact ⟨gamma_pdf_integrable _ has,
        ae_of_all _ (gammaPDFReal_nonneg has (by norm_num)), gamma_pdf_integral _ has⟩
    · filter_upwards [show ∀ᵐ x : ℝ, x ≠ 0 from by
        rw [ae_iff]; simp] with x hx
      exact (gamma_pdf_shape_continuousAt _ x har hx).tendsto.comp
        ((continuous_const.mul NNReal.continuous_coe).tendsto r)
  have ht := bounded_integral_tendsto_of_l1 (gamma_pdf_integrable _ har)
    (hp.mono fun s hs => gamma_pdf_integrable _
      (mul_pos (by norm_num) (NNReal.coe_pos.mpr hs)))
    f.continuous.aestronglyMeasurable ‖f‖ (fun x => f.norm_coe_le_norm x) hl
  change Tendsto (fun s => ∫ x, f x ∂gammaCompletion s) (𝓝 r)
    (𝓝 (∫ x, f x ∂gammaCompletion r))
  rw [gamma_completion_positive r hr, gamma_shape_integral_density _ har]
  apply ht.congr'
  filter_upwards [hp] with s hs
  rw [gamma_completion_positive s hs,
    gamma_shape_integral_density _ (mul_pos (by norm_num) (NNReal.coe_pos.mpr hs))]

theorem nonnegative_probability_tendsto_dirac {ι : Type*} {l : Filter ι}
    (μ : ι → Measure ℝ) (hp : ∀ i, IsProbabilityMeasure (μ i))
    (hsupport : ∀ i, ∀ᵐ x ∂μ i, 0 ≤ x)
    (hl : Tendsto (fun i => realLaplace (μ i) 1) l (𝓝 1))
    (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun i => ∫ x, f x ∂μ i) l (𝓝 (f 0)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hcontrol⟩ := Metric.continuousAt_iff.mp f.continuous.continuousAt
    (ε/2) (half_pos hε)
  let C : ℝ := 2*‖f‖/(1-Real.exp (-δ))
  have hden : 0 < 1-Real.exp (-δ) := by
    have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hδ)
    linarith
  have hC : 0 ≤ C := div_nonneg (by positivity) hden.le
  have hmul : C*(1-Real.exp (-δ)) = 2*‖f‖ := div_mul_cancel₀ _ hden.ne'
  have hpoint (x : ℝ) (hx : 0 ≤ x) :
      ‖f x-f 0‖ ≤ ε/2+C*(1-Real.exp (-x)) := by
    have hex : 0 ≤ 1-Real.exp (-x) := by
      have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
      linarith
    by_cases hxd : x < δ
    · have hn : ‖f x-f 0‖ < ε/2 := by
        simpa only [dist_eq_norm, sub_zero, Real.norm_of_nonneg hx] using
          hcontrol (by simpa only [dist_eq_norm, sub_zero, Real.norm_of_nonneg hx] using hxd)
      linarith [mul_nonneg hC hex]
    · have hex' : 1-Real.exp (-δ) ≤ 1-Real.exp (-x) := by
        have := Real.exp_le_exp.mpr (neg_le_neg (le_of_not_gt hxd))
        linarith
      have hn : ‖f x-f 0‖ ≤ 2*‖f‖ := by
        calc
          _ ≤ ‖f x‖+‖f 0‖ := norm_sub_le _ _
          _ ≤ ‖f‖+‖f‖ := add_le_add (f.norm_coe_le_norm x) (f.norm_coe_le_norm 0)
          _ = _ := by ring
      have hm := mul_le_mul_of_nonneg_left hex' hC
      rw [hmul] at hm
      linarith
  have hb (i : ι) : ‖(∫ x, f x ∂μ i)-f 0‖ ≤ ε/2+C*(1-realLaplace (μ i) 1) := by
    letI := hp i
    have hf : Integrable (fun x => f x) (μ i) :=
      (integrable_const ‖f‖).mono' f.continuous.aestronglyMeasurable
        (ae_of_all _ (fun x => f.norm_coe_le_norm x))
    have he := nonnegative_probability_laplace_integrable _ (hsupport i) 1 (by norm_num)
    have he' : Integrable (fun x => Real.exp (-x)) (μ i) := by simpa using he
    have hbd : Integrable (fun x => ε/2+C*(1-Real.exp (-x))) (μ i) :=
      (integrable_const _).add (((integrable_const 1).sub he').const_mul C)
    calc
      _ = ‖∫ x, f x-f 0 ∂μ i‖ := by rw [integral_sub hf (integrable_const _)]; simp
      _ ≤ ∫ x, ‖f x-f 0‖ ∂μ i := norm_integral_le_integral_norm _
      _ ≤ ∫ x, ε/2+C*(1-Real.exp (-x)) ∂μ i :=
        integral_mono_ae ((hf.sub (integrable_const _)).norm) hbd
          ((hsupport i).mono hpoint)
      _ = _ := by
        have hci : Integrable (fun x => C*(1-Real.exp (-x))) (μ i) :=
          ((integrable_const 1).sub he').const_mul C
        rw [integral_add (integrable_const _) hci, integral_mul_left,
          integral_sub (integrable_const 1) he']
        simp [realLaplace]
  have ht : Tendsto (fun i => C*(1-realLaplace (μ i) 1)) l (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := C)).mul
      ((tendsto_const_nhds (x := (1:ℝ))).sub hl)
  filter_upwards [ht.eventually (gt_mem_nhds (half_pos hε))] with i hi
  rw [dist_eq_norm]
  linarith [hb i]

theorem gamma_completion_continuousAt_zero : ContinuousAt gammaCompletionProbability 0 := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  change Tendsto (fun r => ∫ x, f x ∂gammaCompletion r) (𝓝 0)
    (𝓝 (∫ x, f x ∂gammaCompletion 0))
  rw [gamma_completion_zero, integral_dirac]
  apply nonnegative_probability_tendsto_dirac gammaCompletion gamma_completion_probability
    gamma_completion_nonnegative _ f
  simp_rw [gamma_completion_laplace _ 1 (by norm_num)]
  have ht : Continuous (fun r : ℝ≥0 => Real.exp (-2*(r:ℝ)*Real.log (1+1))) := by fun_prop
  simpa using ht.tendsto 0

/-- Weak continuity, including time zero, is derived from the explicit family. -/
theorem gamma_completion_weak_continuous : Continuous gammaCompletionProbability := by
  apply continuous_iff_continuousAt.mpr
  intro r
  by_cases hr : r = 0
  · subst r; exact gamma_completion_continuousAt_zero
  · exact gamma_completion_continuousAt_positive r (pos_iff_ne_zero.mpr hr)

end
end Sigma
