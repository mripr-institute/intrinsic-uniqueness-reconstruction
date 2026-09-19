import SigmaProbResidual
import SigmaOpMixing
import SigmaProbMGFUnique
import Mathlib.MeasureTheory.Group.Convolution

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

theorem nonnegative_integer_laplace_unique (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    (he : ∀ n : ℕ, realLaplace μ n = realLaplace ν n) : μ = ν := by
  have hf := opFullExpCoordinate_continuous.measurable
  have hi (ρ : Measure ℝ) [IsFiniteMeasure ρ] (hρ : ∀ᵐ t ∂ρ, 0 ≤ t) (n : ℕ) :
      (∫ y : OpUnitInterval, (y : ℝ)^n ∂ρ.map opFullExpCoordinate) = realLaplace ρ n := by
    rw [integral_map hf.aemeasurable
      (continuous_subtype_val.pow n).measurable.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hρ] with t ht
    simp only [opFullExpCoordinate, opExpCoordinate, max_eq_left ht]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hp : μ.map opFullExpCoordinate = ν.map opFullExpCoordinate := by
    apply operator_hausdorff_moment_unique
    intro n
    rw [hi μ hμ n, hi ν hν n, he n]
  have hb (ρ : Measure ℝ) [IsFiniteMeasure ρ] (hρ : ∀ᵐ t ∂ρ, 0 ≤ t) :
      (ρ.map opFullExpCoordinate).map opFullLogCoordinate = ρ := by
    rw [Measure.map_map opFullLogCoordinate_measurable hf]
    calc
      _ = ρ.map id := Measure.map_congr (hρ.mono fun t ht => opFullLog_exp_coordinate ht)
      _ = ρ := Measure.map_id
  rw [← hb μ hμ, hp, hb ν hν]

theorem gamma_shape_integral (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ) :
    (∫ t, f t ∂gammaMeasure a 1) =
      ∫ t : ℝ in Ioi 0, (t^(a-1)*Real.exp (-t)/Real.Gamma a)*f t := by
  change (∫ t, f t ∂volume.withDensity
    (fun t => ((Real.toNNReal (gammaPDFReal a 1 t) : ℝ≥0) : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul
    ((measurable_gammaPDFReal a 1).real_toNNReal)]
  have he : (fun t => Real.toNNReal (gammaPDFReal a 1 t) • f t) =
      (Ici (0 : ℝ)).indicator (fun t => (t^(a-1)*Real.exp (-t)/Real.Gamma a)*f t) := by
    funext t
    rw [NNReal.smul_def, smul_eq_mul,
      Real.coe_toNNReal _ (gammaPDFReal_nonneg ha (by norm_num) t)]
    by_cases ht : 0 ≤ t
    · rw [Set.indicator_of_mem (show t ∈ Ici (0:ℝ) from ht)]
      simp only [gammaPDFReal, if_pos ht, Real.one_rpow, one_mul]
      ring
    · simp [gammaPDFReal, ht]
  rw [he, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

theorem gamma_shape_laplace (a s : ℝ) (ha : 0 < a) (hs : 0 ≤ s) :
    realLaplace (gammaMeasure a 1) s = Real.exp (-a*Real.log (1+s)) := by
  rw [realLaplace, gamma_shape_integral a ha]
  have he : (fun t : ℝ => (t^(a-1)*Real.exp (-t)/Real.Gamma a)*Real.exp (-(s*t))) =
      fun t => (Real.Gamma a)⁻¹*(t^(a-1)*Real.exp (-((1+s)*t))) := by
    funext t
    rw [show -((1+s)*t) = -t + -(s*t) by ring, Real.exp_add]
    ring
  rw [he, integral_mul_left, Real.integral_rpow_mul_exp_neg_mul_Ioi ha (by positivity)]
  have hg : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  rw [mul_comm _ (Real.Gamma a), ← mul_assoc, inv_mul_cancel₀ hg, one_mul,
    Real.rpow_def_of_pos (by positivity : 0 < 1/(1+s)), one_div, Real.log_inv]
  congr 1
  ring

theorem gamma_shape_nonnegative (a : ℝ) : ∀ᵐ t ∂gammaMeasure a 1, 0 ≤ t := by
  rw [ae_iff]
  simp only [not_le]
  change gammaMeasure a 1 (Iio 0) = 0
  rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

/-- The actual Gamma convolution family, including its probability at time zero. -/
def gammaCompletion (r : ℝ≥0) : Measure ℝ :=
  if r = 0 then Measure.dirac 0 else gammaMeasure (2*(r:ℝ)) 1

theorem gamma_completion_zero : gammaCompletion 0 = Measure.dirac 0 := by simp [gammaCompletion]

theorem gamma_completion_positive (r : ℝ≥0) (hr : 0 < r) :
    gammaCompletion r = gammaMeasure (2*(r:ℝ)) 1 := by
  simp [gammaCompletion, hr.ne']

instance gamma_completion_probability (r : ℝ≥0) : IsProbabilityMeasure (gammaCompletion r) := by
  by_cases hr : r = 0
  · subst r
    rw [gamma_completion_zero]
    infer_instance
  · rw [gammaCompletion, if_neg hr]
    exact isProbabilityMeasureGamma (mul_pos (by norm_num) (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)))
      (by norm_num)

theorem gamma_completion_nonnegative (r : ℝ≥0) : ∀ᵐ t ∂gammaCompletion r, 0 ≤ t := by
  by_cases hr : r = 0
  · subst r
    simp [gamma_completion_zero]
  · rw [gammaCompletion, if_neg hr]
    exact gamma_shape_nonnegative _

theorem gamma_completion_one : gammaCompletion 1 = gammaProbability := by
  norm_num [gammaCompletion, gammaProbability]

theorem gamma_completion_laplace (r : ℝ≥0) (s : ℝ) (hs : 0 ≤ s) :
    realLaplace (gammaCompletion r) s = Real.exp (-2*(r:ℝ)*Real.log (1+s)) := by
  by_cases hr : r = 0
  · subst r
    simp [gamma_completion_zero, realLaplace]
  · rw [gammaCompletion, if_neg hr]
    simpa only [neg_mul] using gamma_shape_laplace (2*(r:ℝ)) s
      (mul_pos (by norm_num) (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr))) hs

theorem independent_sum_nonnegative (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) :
    ∀ᵐ t ∂independentAffineSum μ ν 1, 0 ≤ t := by
  rw [independentAffineSum, ae_map_iff (by fun_prop) measurableSet_Ici]
  apply (Measure.ae_prod_iff_ae_ae
    (isClosed_le continuous_const
      ((continuous_const.mul continuous_fst).add continuous_snd)).measurableSet).mpr
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  simpa using add_nonneg hx hy

/-- The convolution identity is equality of actual product-space sum laws. -/
theorem gamma_completion_convolution (r s : ℝ≥0) :
    independentAffineSum (gammaCompletion r) (gammaCompletion s) 1 = gammaCompletion (r+s) := by
  apply nonnegative_integer_laplace_unique _ _
    (independent_sum_nonnegative _ _ (gamma_completion_nonnegative r) (gamma_completion_nonnegative s))
    (gamma_completion_nonnegative (r+s))
  intro n
  rw [independent_affine_sum_laplace, one_mul,
    gamma_completion_laplace r n (Nat.cast_nonneg n),
    gamma_completion_laplace s n (Nat.cast_nonneg n),
    gamma_completion_laplace (r+s) n (Nat.cast_nonneg n), ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem nonnegative_additive_time_linear (f : ℝ≥0 → ℝ)
    (hnonneg : ∀ r, 0 ≤ f r) (hadd : ∀ r s, f (r+s) = f r+f s) (r : ℝ≥0) :
    f r = (r:ℝ)*f 1 := by
  have hz : f 0 = 0 := by have := hadd 0 0; simp only [add_zero] at this; linarith
  have hmono : Monotone f := by
    intro a b hab
    have he := hadd a (b-a)
    rw [add_tsub_cancel_of_le hab] at he
    linarith [hnonneg (b-a)]
  have hnat (n : ℕ) (a : ℝ≥0) : f ((n:ℝ≥0)*a) = (n:ℝ)*f a := by
    induction n with
    | zero => simp [hz]
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, hadd, ih]
      push_cast
      ring
  have hn (n : ℕ) : f (n:ℝ≥0) = (n:ℝ)*f 1 := by simpa using hnat n 1
  have hbound (n : ℕ) :
      (n:ℝ)*|f r-(r:ℝ)*f 1| ≤ f 1 := by
    let k : ℕ := ⌊(n:ℝ)*(r:ℝ)⌋₊
    have hlo : (k:ℝ) ≤ (n:ℝ)*(r:ℝ) := Nat.floor_le (by positivity)
    have hhi : (n:ℝ)*(r:ℝ) < (k:ℝ)+1 := Nat.lt_floor_add_one _
    have hfl := hmono (show (k:ℝ≥0) ≤ (n:ℝ≥0)*r by exact_mod_cast hlo)
    have hfu := hmono (show (n:ℝ≥0)*r ≤ ((k+1:ℕ):ℝ≥0) by exact_mod_cast hhi.le)
    rw [hn, hnat] at hfl
    rw [hnat, hn] at hfu
    push_cast at hfu
    have hl := mul_le_mul_of_nonneg_right hlo (hnonneg 1)
    have hu := mul_le_mul_of_nonneg_right hhi.le (hnonneg 1)
    rw [← abs_of_nonneg (show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n), ← abs_mul]
    apply abs_le.mpr
    constructor <;> nlinarith
  by_contra hne
  have hd : 0 < |f r-(r:ℝ)*f 1| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n,hn⟩ := exists_nat_gt (f 1 / |f r-(r:ℝ)*f 1|)
  have hh := (div_lt_iff₀ hd).mp hn
  nlinarith [hbound n]

theorem nonnegative_probability_laplace_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun t : ℝ => Real.exp (-(s*t))) μ := by
  apply (integrable_const (1:ℝ)).mono'
    ((continuous_const.mul continuous_id).neg.rexp.aestronglyMeasurable)
  filter_upwards [hμ] with t ht
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hs ht))

theorem nonnegative_probability_laplace_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (s : ℝ) (hs : 0 ≤ s) :
    0 < realLaplace μ s ∧ realLaplace μ s ≤ 1 := by
  have hi := nonnegative_probability_laplace_integrable μ hμ s hs
  refine ⟨integral_exp_pos hi, ?_⟩
  have hh : (∫ t : ℝ, Real.exp (-(s*t)) ∂μ) ≤ ∫ _ : ℝ, (1:ℝ) ∂μ := by
    apply integral_mono_ae hi (integrable_const 1)
    filter_upwards [hμ] with t ht
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hs ht))
  simpa [realLaplace] using hh

/-- Every actual nonnegative probability convolution family with the prescribed
time-one marginal is this family. No regularity in the time parameter is assumed. -/
theorem gamma_completion_unique (μ : ℝ≥0 → Measure ℝ)
    (hp : ∀ r, IsProbabilityMeasure (μ r))
    (hsupport : ∀ r, ∀ᵐ t ∂μ r, 0 ≤ t)
    (hadd : ∀ r s, independentAffineSum (μ r) (μ s) 1 = μ (r+s))
    (hone : μ 1 = gammaProbability) : μ = gammaCompletion := by
  have hlap (r : ℝ≥0) (s : ℝ) (hs : 0 ≤ s) :
      realLaplace (μ r) s = Real.exp (-2*(r:ℝ)*Real.log (1+s)) := by
    let f : ℝ≥0 → ℝ := fun t => -Real.log (realLaplace (μ t) s)
    have hb (t : ℝ≥0) : 0 < realLaplace (μ t) s ∧ realLaplace (μ t) s ≤ 1 := by
      letI := hp t
      exact nonnegative_probability_laplace_bounds _ (hsupport t) s hs
    have hf := nonnegative_additive_time_linear f
      (fun t => neg_nonneg.mpr (Real.log_nonpos (hb t).1.le (hb t).2))
      (fun a b => by
        letI := hp a
        letI := hp b
        dsimp [f]
        rw [← hadd a b, independent_affine_sum_laplace, one_mul,
          Real.log_mul (hb a).1.ne' (hb b).1.ne']
        ring) r
    have hone' : realLaplace (μ 1) s = Real.exp (-2*Real.log (1+s)) := by
      rw [hone, ← gamma_completion_one, gamma_completion_laplace 1 s hs]
      simp
    dsimp [f] at hf
    rw [hone', Real.log_exp] at hf
    rw [← Real.exp_log (hb r).1]
    congr 1
    linarith
  funext r
  letI := hp r
  apply nonnegative_integer_laplace_unique _ _ (hsupport r) (gamma_completion_nonnegative r)
  intro n
  rw [hlap r n (Nat.cast_nonneg n), gamma_completion_laplace r n (Nat.cast_nonneg n)]

theorem gamma_completion_native_convolution (r s : ℝ≥0) :
    (gammaCompletion r).conv (gammaCompletion s) = gammaCompletion (r+s) := by
  simpa only [Measure.conv, independentAffineSum, one_mul] using gamma_completion_convolution r s

theorem gamma_completion_laplace_rpow (r : ℝ≥0) (s : ℝ) (hs : 0 ≤ s) :
    realLaplace (gammaCompletion r) s = (1+s)^(-2*(r:ℝ)) := by
  rw [gamma_completion_laplace r s hs, Real.rpow_def_of_pos (by positivity : 0 < 1+s)]
  congr 1
  ring

/-- Existence and uniqueness in the exact category of nonnegative probability
convolution families, without any time-continuity premise. -/
theorem gamma_probability_convolution_completion :
    ∃! μ : ℝ≥0 → Measure ℝ,
      (∀ r, IsProbabilityMeasure (μ r)) ∧
      (∀ r, ∀ᵐ t ∂μ r, 0 ≤ t) ∧ μ 0 = Measure.dirac 0 ∧
      μ 1 = gammaProbability ∧ ∀ r s, (μ r).conv (μ s) = μ (r+s) := by
  refine ⟨gammaCompletion, ⟨gamma_completion_probability, gamma_completion_nonnegative,
    gamma_completion_zero, gamma_completion_one, gamma_completion_native_convolution⟩, ?_⟩
  intro μ hμ
  apply gamma_completion_unique μ hμ.1 hμ.2.1 _ hμ.2.2.2.1
  intro r s
  simpa only [independentAffineSum, Measure.conv, one_mul] using hμ.2.2.2.2 r s

end
end Sigma
