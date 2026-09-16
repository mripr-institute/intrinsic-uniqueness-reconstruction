import SigmaCore
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Analytic.Constructions

namespace Sigma
noncomputable section
open Filter Set MeasureTheory
open scoped Topology

/-- A positive rational density sharing every positive derivative zero with Gamma(2,1). -/
def zeroCounterdensity (t : ℝ) : ℝ := 4*t/(t+2)^3

def zeroCounterDerivative (n : ℕ) (t : ℝ) : ℝ :=
  4 * (-1 : ℝ)^n * (n+1).factorial * (t-n) / (t+2)^(n+3)

theorem zeroCounterdensity_pos {t : ℝ} (ht : 0 < t) :
    0 < zeroCounterdensity t := by
  unfold zeroCounterdensity
  positivity

theorem zeroCounterDerivative_zero (t : ℝ) :
    zeroCounterDerivative 0 t = zeroCounterdensity t := by
  simp [zeroCounterDerivative, zeroCounterdensity]

theorem zeroCounterDerivative_step (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (zeroCounterDerivative n) (zeroCounterDerivative (n+1) t) t := by
  have hn : t+2 ≠ 0 := by linarith
  have hp : (t+2)^(n+3) ≠ 0 := pow_ne_zero _ hn
  have hd := ((((hasDerivAt_id t).sub_const (n : ℝ)).const_mul
    (4 * (-1 : ℝ)^n * (n+1).factorial)).div
    (((hasDerivAt_id t).add_const 2).pow (n+3)) hp)
  convert hd using 1
  simp only [zeroCounterDerivative, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ, Nat.add_sub_cancel, Nat.cast_ofNat, id_eq]
  field_simp
  ring

theorem zeroCounterdensity_iteratedDeriv (n : ℕ) :
    ∀ t > 0, iteratedDeriv n zeroCounterdensity t = zeroCounterDerivative n t := by
  induction n with
  | zero => intro t ht; simpa using (zeroCounterDerivative_zero t).symm
  | succ n ih =>
    intro t ht
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n zeroCounterdensity =ᶠ[nhds t] zeroCounterDerivative n := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
      exact ih x hx
    exact ((zeroCounterDerivative_step n ht).congr_of_eventuallyEq he).deriv

theorem zeroCounterdensity_exact_zeros (n : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv n zeroCounterdensity t = 0 ↔ t = n := by
  rw [zeroCounterdensity_iteratedDeriv n t ht]
  have hf : ((n+1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n+1)
  have hn : (t+2)^(n+3) ≠ 0 := pow_ne_zero _ (by linarith)
  simp only [zeroCounterDerivative, div_eq_zero_iff, mul_eq_zero]
  simp [hf, hn, pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0), sub_eq_zero]

def zeroCounterPrimitive (t : ℝ) : ℝ := -4/(t+2) + 4/(t+2)^2

theorem zeroCounterPrimitive_deriv {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt zeroCounterPrimitive (zeroCounterdensity t) t := by
  have hn : t+2 ≠ 0 := by linarith
  have hd := (((hasDerivAt_const t (-4 : ℝ)).div
    ((hasDerivAt_id t).add_const 2) hn).add
    ((hasDerivAt_const t (4 : ℝ)).div
      (((hasDerivAt_id t).add_const 2).pow 2) (pow_ne_zero _ hn)))
  convert hd using 1
  unfold zeroCounterdensity
  norm_num only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_mul, mul_one]
  field_simp
  ring

theorem zeroCounterPrimitive_limit :
    Tendsto zeroCounterPrimitive atTop (nhds 0) := by
  have hi : Tendsto (fun t : ℝ => (t+2)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 2 tendsto_id)
  have h := (hi.const_mul (-4)).add ((hi.pow 2).const_mul 4)
  convert h using 1
  · funext t
    simp [zeroCounterPrimitive, div_eq_mul_inv, inv_pow]
  · norm_num

theorem zeroCounterdensity_integrable : IntegrableOn zeroCounterdensity (Ioi 0) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun t ht => zeroCounterPrimitive_deriv ht)
    (fun t ht => (zeroCounterdensity_pos ht).le) zeroCounterPrimitive_limit

theorem zeroCounterdensity_mass_one : ∫ t in Ioi (0 : ℝ), zeroCounterdensity t = 1 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun t ht => zeroCounterPrimitive_deriv ht)
    (fun t ht => (zeroCounterdensity_pos ht).le) zeroCounterPrimitive_limit
  norm_num [zeroCounterPrimitive] at h
  exact h

def gammaDerivative (n : ℕ) (t : ℝ) : ℝ := (-1 : ℝ)^n * (t-n) * Real.exp (-t)

theorem gammaDerivative_step (n : ℕ) (t : ℝ) :
    HasDerivAt (gammaDerivative n) (gammaDerivative (n+1) t) t := by
  have hd := (((hasDerivAt_id t).sub_const (n : ℝ)).const_mul ((-1 : ℝ)^n)).mul
    ((hasDerivAt_id t).neg.exp)
  convert hd using 1
  simp only [gammaDerivative, Nat.cast_add, Nat.cast_one, pow_succ, id_eq]
  ring

theorem gamma_iteratedDeriv (n : ℕ) : iteratedDeriv n p = gammaDerivative n := by
  induction n with
  | zero => funext t; simp [gammaDerivative, p, SigmaPresentations.density]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (gammaDerivative_step n t).deriv

theorem gamma_exact_zeros (n : ℕ) (t : ℝ) :
    iteratedDeriv n p t = 0 ↔ t = n := by
  rw [gamma_iteratedDeriv]
  simp [gammaDerivative, Real.exp_ne_zero, pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0), sub_eq_zero]

theorem gamma_zeros_eq_counterdensity_zeros (n : ℕ) :
    {t : ℝ | 0 < t ∧ iteratedDeriv n p t = 0} =
      {t : ℝ | 0 < t ∧ iteratedDeriv n zeroCounterdensity t = 0} := by
  ext t
  by_cases ht : 0 < t
  · simp [ht, gamma_exact_zeros, zeroCounterdensity_exact_zeros n ht]
  · simp [ht]

theorem zeroCounterdensity_not_gamma : ¬ ∀ t > 0, zeroCounterdensity t = p t := by
  intro he
  have he1 : ∀ t > 0, deriv zeroCounterdensity t = deriv p t := by
    intro t ht
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    exact he x hx
  have he2 : deriv (deriv zeroCounterdensity) 1 = deriv (deriv p) 1 := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioi.mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact he1 x hx
  have hf : iteratedDeriv 2 zeroCounterdensity 1 = iteratedDeriv 2 p 1 := by
    simpa [iteratedDeriv_succ] using he2
  rw [zeroCounterdensity_iteratedDeriv 2 1 (by norm_num), gamma_iteratedDeriv] at hf
  have hv := he 1 (by norm_num)
  norm_num [zeroCounterdensity, p, SigmaPresentations.density] at hv
  norm_num [zeroCounterDerivative, gammaDerivative, Nat.factorial] at hf
  linarith

theorem zeroCounterdensity_analytic {t : ℝ} (ht : 0 < t) :
    AnalyticAt ℝ zeroCounterdensity t := by
  have hn : (t+2)^3 ≠ 0 := pow_ne_zero _ (by linarith)
  have ha : AnalyticAt ℝ (fun x : ℝ => (x+2)^3) t :=
    ((analyticAt_id (𝕜 := ℝ) (z := t)).add (analyticAt_const (v := (2 : ℝ)))).pow 3
  have hb : AnalyticAt ℝ (fun x : ℝ => 4*x) t :=
    (analyticAt_const (v := (4 : ℝ))).mul analyticAt_id
  exact hb.div ha hn

end
end Sigma
