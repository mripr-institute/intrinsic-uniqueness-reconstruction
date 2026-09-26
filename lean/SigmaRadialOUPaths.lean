import SigmaRadialOUNormalization
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Tactic.Module

/-!
The explicit OU solution driven by an arbitrary continuous path. The noise
path need not be differentiable. All integrals in this file are ordinary
Bochner integrals; the Brownian construction and stochastic calculus are
separate obligations.
-/

namespace Sigma
noncomputable section
open MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The differentiable correction to the driving path. -/
def ouPathCorrection (z : V) (B : ℝ → V) (t : ℝ) : V :=
  Real.exp (-t / 2) •
    (z - (1 / 2 : ℝ) • ∫ s in (0 : ℝ)..t, Real.exp (s / 2) • B s)

/-- The continuous-path OU solution with initial value `z`, when `B 0 = 0`. -/
def ouPath (z : V) (B : ℝ → V) (t : ℝ) : V :=
  B t + ouPathCorrection z B t

theorem ou_path_correction_hasDerivAt (z : V) (B : ℝ → V)
    (hB : Continuous B) (t : ℝ) :
    HasDerivAt (ouPathCorrection z B) (-(1 / 2 : ℝ) • ouPath z B t) t := by
  have hc : Continuous (fun s : ℝ => Real.exp (s / 2) • B s) := by fun_prop
  have hi := (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s / 2))
      (Real.exp (-t / 2) * (-(1 / 2 : ℝ))) t := by
    convert (((hasDerivAt_id t).neg.div_const 2).exp) using 1
    simp only [id_eq]
    ring
  have h := he.smul ((hasDerivAt_const t z).sub (hi.const_smul (1 / 2 : ℝ)))
  convert h using 1
  dsimp [ouPath, ouPathCorrection]
  have hexp : Real.exp (-t / 2) * Real.exp (t / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  simp only [smul_add, smul_sub, smul_smul, mul_zero, zero_smul, sub_zero]
  match_scalars <;> nlinarith [hexp]

theorem ou_path_correction_continuous (z : V) (B : ℝ → V) (hB : Continuous B) :
    Continuous (ouPathCorrection z B) :=
  continuous_iff_continuousAt.mpr fun t =>
    (ou_path_correction_hasDerivAt z B hB t).continuousAt

theorem ou_path_continuous (z : V) (B : ℝ → V) (hB : Continuous B) :
    Continuous (ouPath z B) :=
  hB.add (ou_path_correction_continuous z B hB)

omit [CompleteSpace V] in
theorem ou_path_initial (z : V) (B : ℝ → V) (hB : B 0 = 0) :
    ouPath z B 0 = z := by
  simp [ouPath, ouPathCorrection, hB]

/-- The genuine integral OU equation, valid for every continuous driving path. -/
theorem ou_path_integral_equation (z : V) (B : ℝ → V) (hB : Continuous B) (t : ℝ) :
    ouPath z B t = z + B t + ∫ s in (0 : ℝ)..t, -(1 / 2 : ℝ) • ouPath z B s := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_ : s ∈ Set.uIcc 0 t) => ou_path_correction_hasDerivAt z B hB s)
    (((ou_path_continuous z B hB).const_smul (-(1 / 2 : ℝ))).intervalIntegrable 0 t)
  rw [hi]
  simp only [ouPathCorrection, intervalIntegral.integral_same, smul_zero, sub_zero,
    neg_zero, zero_div, Real.exp_zero, one_smul]
  dsimp [ouPath, ouPathCorrection]
  abel

/-- No different continuous solution can satisfy the same driven OU equation. -/
theorem ou_path_unique (z : V) (B X : ℝ → V) (hB : Continuous B)
    (hX : Continuous X)
    (h : ∀ t, X t = z + B t + ∫ s in (0 : ℝ)..t, -(1 / 2 : ℝ) • X s) :
    X = ouPath z B := by
  let D : ℝ → V := fun t => X t - ouPath z B t
  have hd (t : ℝ) : HasDerivAt D (-(1 / 2 : ℝ) • D t) t := by
    have heq : D = fun t =>
        (∫ s in (0 : ℝ)..t, -(1 / 2 : ℝ) • X s) -
        (∫ s in (0 : ℝ)..t, -(1 / 2 : ℝ) • ouPath z B s) := by
      funext t
      dsimp [D]
      rw [h t, ou_path_integral_equation z B hB t]
      abel
    have hder := (((hX.const_smul (-(1 / 2 : ℝ))).integral_hasStrictDerivAt 0 t).hasDerivAt.sub
        ((((ou_path_continuous z B hB).const_smul (-(1 / 2 : ℝ))).integral_hasStrictDerivAt 0 t).hasDerivAt))
    rw [← heq] at hder
    simpa only [D, smul_sub] using hder
  have hz (t : ℝ) : HasDerivAt (fun s => Real.exp (s / 2) • D s) 0 t := by
    have he : HasDerivAt (fun s : ℝ => Real.exp (s / 2))
        (Real.exp (t / 2) / 2) t := by
      convert ((hasDerivAt_id t).div_const 2).exp using 1
      simp [div_eq_mul_inv]
    convert he.smul (hd t) using 1
    module
  have hD0 : D 0 = 0 := by
    dsimp [D]
    rw [h 0, ou_path_integral_equation z B hB 0]
    simp
  funext t
  have hc := is_const_of_deriv_eq_zero (fun s => (hz s).differentiableAt)
    (fun s => (hz s).deriv) t 0
  simp only [hD0, smul_zero] at hc
  have hzero : D t = 0 := (smul_eq_zero.mp hc).resolve_left (Real.exp_ne_zero _)
  exact sub_eq_zero.mp hzero

end
end Sigma
