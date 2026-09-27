import SigmaOpSpectral
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

/-- The exponential in the compactified spectral variable `r = (1+λ)⁻¹`.
The value at the unattained endpoint zero is zero for positive time. -/
def resolventHeatScalar (t r : ℝ) : ℝ :=
  Real.exp t * expNegInvGlue (r / t)

theorem resolvent_heat_scalar_eq {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    resolventHeatScalar t r = Real.exp (-t * (r⁻¹ - 1)) := by
  rw [resolventHeatScalar, expNegInvGlue, if_neg (not_le.mpr (div_pos hr ht)),
    ← Real.exp_add]
  congr 1
  field_simp
  ring

theorem resolvent_heat_scalar_zero (t : ℝ) : resolventHeatScalar t 0 = 0 := by
  simp [resolventHeatScalar]

theorem resolvent_heat_scalar_nonneg (t r : ℝ) : 0 ≤ resolventHeatScalar t r :=
  mul_nonneg (Real.exp_pos _).le (expNegInvGlue.nonneg _)

theorem resolvent_heat_scalar_le_one {t r : ℝ} (ht : 0 < t)
    (hr : r ∈ Icc (0 : ℝ) 1) : resolventHeatScalar t r ≤ 1 := by
  rcases hr.1.eq_or_lt with h | h
  · rw [← h, resolvent_heat_scalar_zero]; exact zero_le_one
  · rw [resolvent_heat_scalar_eq ht h, Real.exp_le_one_iff]
    apply mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le)
    exact sub_nonneg.mpr ((one_le_inv₀ h).mpr hr.2)

theorem resolvent_heat_scalar_continuous (t : ℝ) :
    Continuous (resolventHeatScalar t) := by
  exact continuous_const.mul
    ((expNegInvGlue.contDiff (n := 0)).continuous.comp (continuous_id.div_const t))

/-- Multiplying by the Gamma density cancels the positive exponential factor. -/
def resolventGammaScalar (t r : ℝ) : ℝ := t * expNegInvGlue (r / t)

theorem resolvent_gamma_scalar_eq (t r : ℝ) :
    resolventGammaScalar t r = (t * Real.exp (-t)) * resolventHeatScalar t r := by
  unfold resolventGammaScalar resolventHeatScalar
  rw [← mul_assoc, mul_assoc t, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

theorem exp_neg_inv_glue_le_one (r : ℝ) : expNegInvGlue r ≤ 1 := by
  by_cases hr : r ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hr]; exact zero_le_one
  · rw [expNegInvGlue, if_neg hr, Real.exp_le_one_iff]
    exact neg_nonpos.mpr (inv_nonneg.mpr (not_le.mp hr).le)

theorem resolvent_gamma_scalar_abs_le (t r : ℝ) :
    |resolventGammaScalar t r| ≤ |t| := by
  rw [resolventGammaScalar, abs_mul, abs_of_nonneg (expNegInvGlue.nonneg _)]
  exact (mul_le_mul_of_nonneg_left (exp_neg_inv_glue_le_one _) (abs_nonneg _)).trans_eq
    (mul_one _)

theorem resolvent_gamma_scalar_continuous :
    Continuous (fun p : ℝ × ℝ => resolventGammaScalar p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p.1 = 0
  · have hz : resolventGammaScalar p.1 p.2 = 0 := by simp [resolventGammaScalar, hp]
    rw [ContinuousAt, hz]
    apply squeeze_zero_norm' (a := fun q : ℝ × ℝ => |q.1|)
    · filter_upwards with q
      simpa only [Real.norm_eq_abs] using resolvent_gamma_scalar_abs_le q.1 q.2
    · simpa [hp] using (continuous_fst.abs.tendsto p)
  · exact continuousAt_fst.mul
      ((expNegInvGlue.contDiff (n := 0)).continuous.continuousAt.comp
        (continuousAt_snd.div continuousAt_fst hp))

theorem resolvent_gamma_scalar_integral {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    (∫ t : ℝ in Ioi 0, resolventGammaScalar t r) = r ^ 2 := by
  rcases hr.1.eq_or_lt with h | h
  · rw [← h]; simp [resolventGammaScalar]
  · have hlam : 0 ≤ r⁻¹ - 1 := sub_nonneg.mpr ((one_le_inv₀ h).mpr hr.2)
    have he : (∫ t : ℝ in Ioi 0, resolventGammaScalar t r) =
        ∫ t : ℝ in Ioi 0, t * Real.exp (-(1 + (r⁻¹ - 1)) * t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change resolventGammaScalar t r = t * Real.exp (-(1 + (r⁻¹ - 1)) * t)
      rw [resolvent_gamma_scalar_eq, resolvent_heat_scalar_eq ht h]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [he, operator_gamma_mixing_integral hlam]
    field_simp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Heat functional calculus through the actual bounded shift resolvent.
No eigenbasis or discreteness assumption enters this construction. -/
def resolventHeatOperator (R : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  if 0 < t then cfc (resolventHeatScalar t) R else 1

theorem resolvent_heat_operator_contracts (R : H →L[ℂ] H)
    (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (t : ℝ) (x : H) :
    ‖resolventHeatOperator R t x‖ ≤ ‖x‖ := by
  unfold resolventHeatOperator
  split_ifs with ht
  · have hn : ‖cfc (resolventHeatScalar t) R‖ ≤ 1 := by
      apply norm_cfc_le zero_le_one
      intro r hr
      rw [Real.norm_of_nonneg (resolvent_heat_scalar_nonneg _ _)]
      exact resolvent_heat_scalar_le_one ht (hσ hr)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      ((mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans_eq (one_mul _))
  · simp

theorem resolvent_gamma_scalar_bound (t : ℝ) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    ‖resolventGammaScalar t r‖ ≤ ‖t * Real.exp (-t)‖ := by
  by_cases ht : 0 < t
  · rw [resolvent_gamma_scalar_eq, norm_mul,
      Real.norm_of_nonneg (resolvent_heat_scalar_nonneg _ _)]
    exact (mul_le_mul_of_nonneg_left (resolvent_heat_scalar_le_one ht hr)
      (norm_nonneg _)).trans_eq (mul_one _)
  · have hd : r / t ≤ 0 := div_nonpos_of_nonneg_of_nonpos hr.1 (not_lt.mp ht)
    rw [resolventGammaScalar, expNegInvGlue.zero_of_nonpos hd, mul_zero, norm_zero]
    exact norm_nonneg _

theorem resolvent_gamma_scalar_cfc_integral (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) :
    (∫ t : ℝ in Ioi 0, cfc (resolventGammaScalar t) R) = R ^ 2 := by
  letI : CompactSpace (spectrum ℝ R) :=
    ContinuousFunctionalCalculus.compactSpace_spectrum (p := IsSelfAdjoint) R
  have hw : IntegrableOn (fun t : ℝ => t * Real.exp (-t)) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    have hi := operator_gamma_mixing_integral (lam := 0) (le_refl 0)
    rw [show (∫ t : ℝ in Ioi 0, t * Real.exp (-t)) = 1 by simpa using hi]
    exact one_ne_zero
  have hc : Continuous (fun t : ℝ => (spectrum ℝ R).restrict
      (resolventGammaScalar t)).uncurry := by
    exact resolvent_gamma_scalar_continuous.comp
      (continuous_fst.prod_mk (continuous_subtype_val.comp continuous_snd))
  have hi := cfc_integral' (μ := volume.restrict (Ioi (0 : ℝ)))
    resolventGammaScalar (fun t : ℝ => t * Real.exp (-t)) R hc
    (fun t r hr => resolvent_gamma_scalar_bound t (hσ hr)) hw.hasFiniteIntegral hR
  rw [← hi]
  have he : cfc (fun r : ℝ => ∫ t : ℝ in Ioi 0, resolventGammaScalar t r) R =
      cfc (fun r : ℝ => r ^ 2) R := by
    apply cfc_congr
    intro r hr
    exact resolvent_gamma_scalar_integral (hσ hr)
  rw [he]
  simpa only [id_eq, cfc_id ℝ R] using cfc_pow (id : ℝ → ℝ) 2 R

theorem resolvent_heat_operator_weighted (R : H →L[ℂ] H)
    {t : ℝ} (ht : 0 < t) :
    (t * Real.exp (-t)) • resolventHeatOperator R t =
      cfc (resolventGammaScalar t) R := by
  rw [resolventHeatOperator, if_pos ht,
    ← cfc_smul (t * Real.exp (-t)) (resolventHeatScalar t) R
      (resolvent_heat_scalar_continuous t).continuousOn]
  apply cfc_congr
  intro r _
  exact (resolvent_gamma_scalar_eq t r).symm

theorem resolvent_gamma_cfc_continuous (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) :
    Continuous (fun t : ℝ => cfc (resolventGammaScalar t) R) := by
  letI : CompactSpace (spectrum ℝ R) :=
    ContinuousFunctionalCalculus.compactSpace_spectrum (p := IsSelfAdjoint) R
  have hc : Continuous (fun t : ℝ => (spectrum ℝ R).restrict
      (resolventGammaScalar t)).uncurry := by
    exact resolvent_gamma_scalar_continuous.comp
      (continuous_fst.prod_mk (continuous_subtype_val.comp continuous_snd))
  have hcur := (ContinuousMap.curry ⟨_, hc⟩).continuous
  have hout := (cfcHom_continuous hR).comp hcur
  convert hout using 1
  funext t
  exact cfc_apply (resolventGammaScalar t) R hR
    (continuousOn_iff_continuous_restrict.mpr (hc.uncurry_left t))

theorem resolvent_gamma_cfc_integrable (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) :
    IntegrableOn (fun t : ℝ => cfc (resolventGammaScalar t) R) (Ioi 0) := by
  letI : SecondCountableTopologyEither ℝ (H →L[ℂ] H) :=
    ⟨Or.inl inferInstance⟩
  have hw : IntegrableOn (fun t : ℝ => t * Real.exp (-t)) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    have hi := operator_gamma_mixing_integral (lam := 0) (le_refl 0)
    rw [show (∫ t : ℝ in Ioi 0, t * Real.exp (-t)) = 1 by simpa using hi]
    exact one_ne_zero
  have hm : AEStronglyMeasurable (fun t : ℝ => cfc (resolventGammaScalar t) R)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (resolvent_gamma_cfc_continuous R hR).aestronglyMeasurable
  apply hw.norm.mono' hm
  exact ae_of_all _ fun t => norm_cfc_le (norm_nonneg _)
    (fun r hr => resolvent_gamma_scalar_bound t (hσ hr))

/-- The operator integral exists in norm, and hence also as a strong integral. -/
theorem resolvent_heat_operator_gamma_integral (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) :
    (∫ t : ℝ in Ioi 0, (t * Real.exp (-t)) • resolventHeatOperator R t) = R ^ 2 := by
  rw [show (∫ t : ℝ in Ioi 0, (t * Real.exp (-t)) • resolventHeatOperator R t) =
      ∫ t : ℝ in Ioi 0, cfc (resolventGammaScalar t) R by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact resolvent_heat_operator_weighted R ht]
  exact resolvent_gamma_scalar_cfc_integral R hR hσ

theorem resolvent_heat_strong_gamma_integral (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (x : H) :
    (∫ t : ℝ in Ioi 0, (t * Real.exp (-t)) • resolventHeatOperator R t x) = R (R x) := by
  have hi := congrArg (fun T : H →L[ℂ] H => T x)
    (resolvent_gamma_scalar_cfc_integral R hR hσ)
  change (∫ t : ℝ in Ioi 0, cfc (resolventGammaScalar t) R) x = (R ^ 2) x at hi
  rw [ContinuousLinearMap.integral_apply (resolvent_gamma_cfc_integrable R hR hσ) x] at hi
  rw [show (∫ t : ℝ in Ioi 0, (t * Real.exp (-t)) • resolventHeatOperator R t x) =
      ∫ t : ℝ in Ioi 0, cfc (resolventGammaScalar t) R x by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact congrArg (fun T : H →L[ℂ] H => T x) (resolvent_heat_operator_weighted R ht)]
  simpa only [pow_two, ContinuousLinearMap.mul_apply] using hi

end
end Sigma
