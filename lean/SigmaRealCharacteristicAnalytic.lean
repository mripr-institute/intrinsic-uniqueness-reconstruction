import SigmaPresentations
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology

theorem real_exp_analytic (x : ℝ) : AnalyticAt ℝ Real.exp x := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.exp_analytic x

/-- Analytic removal at the base point is supplied by the shifted native
power series, not by an assumed removable-singularity conclusion. -/
theorem analytic_dslope_real (f : ℝ → ℝ) (a : ℝ)
    (hf : ∀ x, AnalyticAt ℝ f x) (x : ℝ) : AnalyticAt ℝ (dslope f a) x := by
  by_cases hx : x=a
  · subst x
    obtain ⟨p,hp⟩ := hf a
    exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩
  · have hq : AnalyticAt ℝ (fun y => (f y-f a)/(y-a)) x :=
      ((hf x).sub analyticAt_const).div
        (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hx)
    apply hq.congr
    filter_upwards [dslope_eventuallyEq_slope_of_ne f hx] with y hy
    simpa [slope,div_eq_mul_inv,mul_comm] using hy.symm

def realToddDenominator (u : ℝ) : ℝ := dslope (fun x : ℝ => 1-Real.exp (-x)) 0 u

theorem real_todd_denominator_zero : realToddDenominator 0=1 := by
  unfold realToddDenominator
  rw [dslope_same]
  have h := (hasDerivAt_const (0:ℝ) (1:ℝ)).sub
    (((hasDerivAt_id (0:ℝ)).neg).exp)
  simpa using h.deriv

theorem real_todd_denominator_nonzero (u : ℝ) : realToddDenominator u ≠ 0 := by
  by_cases hu : u=0
  · simp [hu,real_todd_denominator_zero]
  · unfold realToddDenominator
    rw [dslope_of_ne _ hu]
    simp only [slope, vsub_eq_sub, sub_zero, neg_zero, Real.exp_zero, sub_self, smul_eq_mul]
    apply mul_ne_zero (inv_ne_zero hu)
    intro h
    have he : Real.exp (-u)=1 := by linarith
    have h0 : -u=0 := Real.exp_injective (he.trans Real.exp_zero.symm)
    exact hu (by linarith)

theorem real_todd_denominator_analytic (u : ℝ) : AnalyticAt ℝ realToddDenominator u := by
  apply analytic_dslope_real
  intro x
  exact analyticAt_const.sub ((real_exp_analytic (-x)).comp (analyticAt_id.neg))

def realTodd (u : ℝ) : ℝ := (realToddDenominator u)⁻¹

theorem real_todd_zero : realTodd 0=1 := by simp [realTodd,real_todd_denominator_zero]

theorem real_todd_nonzero (u : ℝ) : realTodd u ≠ 0 :=
  inv_ne_zero (real_todd_denominator_nonzero u)

theorem real_todd_analytic (u : ℝ) : AnalyticAt ℝ realTodd u :=
  (real_todd_denominator_analytic u).inv (real_todd_denominator_nonzero u)

theorem real_todd_quotient (u : ℝ) (hu : u ≠ 0) :
    realTodd u=u/(1-Real.exp (-u)) := by
  unfold realTodd realToddDenominator
  rw [dslope_of_ne _ hu]
  simp [slope,div_eq_mul_inv,mul_comm]

theorem real_todd_quotient_identity (u : ℝ) : realTodd u*(1-Real.exp (-u))=u := by
  by_cases hu : u=0
  · simp [hu]
  · rw [real_todd_quotient u hu]
    have he : 1-Real.exp (-u) ≠ 0 := by
      intro h
      have he : Real.exp (-u)=1 := by linarith
      have h0 : -u=0 := Real.exp_injective (he.trans Real.exp_zero.symm)
      exact hu (by linarith)
    exact div_mul_cancel₀ u he

theorem real_todd_exponential_denominator (u : ℝ) :
    realTodd u-u=realTodd u*Real.exp (-u) := by
  have h := real_todd_quotient_identity u
  nlinarith

theorem real_todd_recovers_real_exponential (u : ℝ) :
    realTodd u/(realTodd u-u)=Real.exp u := by
  rw [real_todd_exponential_denominator]
  rw [Real.exp_neg]
  field_simp [real_todd_nonzero,Real.exp_ne_zero]

def realAhat (u : ℝ) : ℝ := Real.exp (-(u/2))*realTodd u

def realLgenus (u : ℝ) : ℝ := realTodd (2*u)-u

def realChi (y u : ℝ) : ℝ := realTodd ((1+y)*u)-y*u

theorem real_characteristic_zero :
    realAhat 0=1 ∧ realLgenus 0=1 ∧ ∀ y, realChi y 0=1 := by
  simp [realAhat,realLgenus,realChi,real_todd_zero]

theorem real_ahat_analytic (u : ℝ) : AnalyticAt ℝ realAhat u := by
  have ha : AnalyticAt ℝ (fun x : ℝ => -(x/2)) u :=
    (analyticAt_id.div analyticAt_const (by norm_num : (2:ℝ) ≠ 0)).neg
  exact ((real_exp_analytic (-(u/2))).comp (f := fun x : ℝ => -(x/2)) ha).mul
    (real_todd_analytic u)

theorem real_lgenus_analytic (u : ℝ) : AnalyticAt ℝ realLgenus u :=
  ((real_todd_analytic (2*u)).comp (analyticAt_const.mul analyticAt_id)).sub analyticAt_id

theorem real_chi_analytic (y u : ℝ) : AnalyticAt ℝ (realChi y) u :=
  ((real_todd_analytic ((1+y)*u)).comp (analyticAt_const.mul analyticAt_id)).sub
    (analyticAt_const.mul analyticAt_id)

theorem real_exp_neg_mul_sinh (x : ℝ) :
    Real.exp (-x)*Real.sinh x=(1-Real.exp (-(2*x)))/2 := by
  rw [Real.sinh_eq, ← mul_div_assoc, mul_sub, ← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [neg_add_cancel,Real.exp_zero]
  congr 2
  ring

theorem real_ahat_sinh_identity (u : ℝ) :
    realAhat u*Real.sinh (u/2)=u/2 := by
  unfold realAhat
  calc
    Real.exp (-(u/2))*realTodd u*Real.sinh (u/2) =
        realTodd u*(Real.exp (-(u/2))*Real.sinh (u/2)) := by ring
    _ = realTodd u*((1-Real.exp (-u))/2) := by
      rw [real_exp_neg_mul_sinh]; congr 3; ring
    _ = u/2 := by rw [← mul_div_assoc,real_todd_quotient_identity]

theorem real_ahat_quotient (u : ℝ) (hu : u ≠ 0) :
    realAhat u=(u/2)/Real.sinh (u/2) := by
  apply (eq_div_iff (Real.sinh_ne_zero.mpr (div_ne_zero hu (by norm_num)))).mpr
  exact real_ahat_sinh_identity u

theorem real_ahat_nonzero (u : ℝ) : realAhat u ≠ 0 :=
  mul_ne_zero (Real.exp_ne_zero _) (real_todd_nonzero u)

theorem real_lgenus_sinh_identity (u : ℝ) :
    realLgenus u*Real.sinh u=u*Real.cosh u := by
  have h : realTodd (2*u)*(Real.exp (-u)*Real.sinh u)=u := by
    rw [real_exp_neg_mul_sinh,← mul_div_assoc,real_todd_quotient_identity]
    ring
  have he : Real.exp (-u)*(Real.cosh u+Real.sinh u)=1 := by
    rw [Real.cosh_add_sinh,← Real.exp_add]
    simp
  have ht : realTodd (2*u)*Real.sinh u=u*(Real.cosh u+Real.sinh u) := by
    calc
      realTodd (2*u)*Real.sinh u =
          realTodd (2*u)*Real.sinh u*(Real.exp (-u)*(Real.cosh u+Real.sinh u)) := by rw [he,mul_one]
      _ = (realTodd (2*u)*(Real.exp (-u)*Real.sinh u))*(Real.cosh u+Real.sinh u) := by ring
      _ = u*(Real.cosh u+Real.sinh u) := by rw [h]
  unfold realLgenus
  nlinarith

theorem real_lgenus_quotient (u : ℝ) (hu : u ≠ 0) :
    realLgenus u=u/Real.tanh u := by
  rw [Real.tanh_eq_sinh_div_cosh,div_div_eq_mul_div]
  apply (eq_div_iff (Real.sinh_ne_zero.mpr hu)).mpr
  exact real_lgenus_sinh_identity u

theorem real_lgenus_nonzero (u : ℝ) : realLgenus u ≠ 0 := by
  by_cases hu : u=0
  · simp [hu,realLgenus,real_todd_zero]
  · intro h
    have hi := real_lgenus_sinh_identity u
    rw [h,zero_mul] at hi
    exact (mul_ne_zero hu (ne_of_gt (Real.cosh_pos u))) hi.symm

theorem real_lgenus_recovers_exponential (u : ℝ) :
    (realLgenus u+u)/(realLgenus u-u)=Real.exp (2*u) := by
  convert real_todd_recovers_real_exponential (2*u) using 1
  unfold realLgenus
  congr 1 <;> ring

theorem real_ahat_recovers_todd (u : ℝ) :
    Real.exp (u/2)*realAhat u=realTodd u := by
  unfold realAhat
  rw [← mul_assoc,← Real.exp_add]
  simp

theorem real_lgenus_todd_inverse (u : ℝ) : realLgenus (u/2)+u/2=realTodd u := by
  unfold realLgenus
  rw [show 2*(u/2)=u by ring]
  ring

theorem real_chi_inverse (y v : ℝ) (hy : 1+y ≠ 0) :
    realChi y (v/(1+y))+y*v/(1+y)=realTodd v := by
  unfold realChi
  rw [mul_div_cancel₀ _ hy]
  ring

theorem real_chi_minus_one (u : ℝ) : realChi (-1) u=1+u := by
  simp [realChi,real_todd_zero]

theorem real_characteristic_recovery_denominators (u : ℝ) :
    realTodd u-u ≠ 0 ∧ realLgenus u-u ≠ 0 := by
  constructor
  · rw [real_todd_exponential_denominator]
    exact mul_ne_zero (real_todd_nonzero u) (Real.exp_ne_zero _)
  · have h : realLgenus u-u=realTodd (2*u)-2*u := by unfold realLgenus; ring
    rw [h,real_todd_exponential_denominator]
    exact mul_ne_zero (real_todd_nonzero _) (Real.exp_ne_zero _)

/-- Multiplicative inverse representatives are analytic on their exact
nonvanishing domains; the marked chi parameter is unrestricted here. -/
theorem real_characteristic_inverses_analytic (u : ℝ) :
    AnalyticAt ℝ (fun x => (realTodd x)⁻¹) u ∧
    AnalyticAt ℝ (fun x => (realAhat x)⁻¹) u ∧
    AnalyticAt ℝ (fun x => (realLgenus x)⁻¹) u ∧
    ∀ y, realChi y u ≠ 0 → AnalyticAt ℝ (fun x => (realChi y x)⁻¹) u := by
  exact ⟨(real_todd_analytic u).inv (real_todd_nonzero u),
    (real_ahat_analytic u).inv (real_ahat_nonzero u),
    (real_lgenus_analytic u).inv (real_lgenus_nonzero u),
    fun y hy => (real_chi_analytic y u).inv hy⟩

theorem real_characteristic_inverse_reversal (u y : ℝ) :
    ((realTodd u)⁻¹)⁻¹=realTodd u ∧ ((realAhat u)⁻¹)⁻¹=realAhat u ∧
    ((realLgenus u)⁻¹)⁻¹=realLgenus u ∧ ((realChi y u)⁻¹)⁻¹=realChi y u := by
  simp

theorem real_ahat_square_root (u : ℝ) :
    Real.sqrt ((u/realAhat u)^2+4)=2*Real.cosh (u/2) := by
  have hb : u/realAhat u=2*Real.sinh (u/2) := by
    apply (div_eq_iff (real_ahat_nonzero u)).mpr
    have h := real_ahat_sinh_identity u
    nlinarith
  rw [hb]
  have hs : (2*Real.sinh (u/2))^2+4=(2*Real.cosh (u/2))^2 := by
    have h := Real.cosh_sq_sub_sinh_sq (u/2)
    nlinarith
  rw [hs,Real.sqrt_sq (by positivity)]

theorem real_ahat_recovers_exponential_half (u : ℝ) :
    (u/realAhat u+Real.sqrt ((u/realAhat u)^2+4))/2=Real.exp (u/2) := by
  have hb : u/realAhat u=2*Real.sinh (u/2) := by
    apply (div_eq_iff (real_ahat_nonzero u)).mpr
    have h := real_ahat_sinh_identity u
    nlinarith
  rw [real_ahat_square_root,hb,← Real.sinh_add_cosh]
  ring

theorem real_ahat_square_root_reconstructs_todd (u : ℝ) :
    ((u/realAhat u+Real.sqrt ((u/realAhat u)^2+4))/2)*realAhat u=realTodd u := by
  rw [real_ahat_recovers_exponential_half,real_ahat_recovers_todd]

/-- The supplied function is independent of the characteristic-series construction;
analyticity on the same connected domain is the stated uniqueness category. -/
theorem real_analytic_global_recovery {f g : ℝ → ℝ} {U : Set ℝ} {a : ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hg : AnalyticOnNhd ℝ g U)
    (hU : IsPreconnected U) (ha : a ∈ U) (hfg : f =ᶠ[𝓝 a] g) : EqOn f g U :=
  hf.eqOn_of_preconnected_of_eventuallyEq hg hU ha hfg

end
end Sigma
