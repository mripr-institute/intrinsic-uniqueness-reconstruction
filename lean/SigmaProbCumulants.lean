import SigmaProbSupport
import SigmaProbMGFUnique
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

namespace Sigma
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

def probabilityCGF (μ : Measure ℝ) (s : ℝ) : ℝ :=
  Real.log (∫ t : ℝ, Real.exp (s*t) ∂μ)

/-- Cumulants are the actual derivatives of the logarithm of the MGF at zero. -/
def probabilityCumulant (μ : Measure ℝ) (n : ℕ) : ℝ :=
  iteratedDeriv n (probabilityCGF μ) 0

theorem gamma_probability_cgf (s : ℝ) (hs : s < 1) :
    probabilityCGF gammaProbability s = -2*Real.log (1-s) := by
  have hm := gamma_probability_laplace (s := -s) (by linarith)
  have he : (fun t : ℝ => Real.exp (-(-s*t))) = fun t => Real.exp (s*t) := by
    funext t
    congr 1
    ring
  rw [he] at hm
  rw [probabilityCGF, hm, Real.log_pow, Real.log_inv]
  simp only [sub_eq_add_neg]
  ring

def gammaCGFDerivative (n : ℕ) (s : ℝ) : ℝ :=
  2*(n.factorial : ℝ)*(1/(1-s))^(n+1)

theorem gamma_cgf_first_derivative (s : ℝ) (hs : s < 1) :
    HasDerivAt (probabilityCGF gammaProbability) (gammaCGFDerivative 0 s) s := by
  have hd := ((((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).log
    (by linarith : 1-s ≠ 0)).const_mul (-2))
  have he : probabilityCGF gammaProbability =ᶠ[𝓝 s] (fun u => -2*Real.log (1-u)) := by
    filter_upwards [isOpen_Iio.mem_nhds hs] with u hu
    exact gamma_probability_cgf u hu
  apply HasDerivAt.congr_of_eventuallyEq _ he
  convert hd using 1
  simp [gammaCGFDerivative]
  ring

theorem gamma_cgf_derivative_step (n : ℕ) (s : ℝ) (hs : s < 1) :
    HasDerivAt (gammaCGFDerivative n) (gammaCGFDerivative (n+1) s) s := by
  have hd := (((hasDerivAt_const s (1 : ℝ)).div
    ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s))
    (by linarith : 1-s ≠ 0)).pow (n+1)).const_mul (2*(n.factorial : ℝ))
  convert hd using 1
  simp only [gammaCGFDerivative, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, mul_zero, zero_sub, zero_sub, sub_neg_eq_add, zero_add, mul_one,
    Nat.add_sub_cancel]
  rw [pow_succ, pow_succ]
  field_simp
  ring

theorem gamma_cgf_iterated_derivative (n : ℕ) :
    ∀ s : ℝ, s < 1 → iteratedDeriv (n+1) (probabilityCGF gammaProbability) s =
      gammaCGFDerivative n s := by
  induction n with
  | zero =>
    intro s hs
    simpa [iteratedDeriv_succ] using (gamma_cgf_first_derivative s hs).deriv
  | succ n ih =>
    intro s hs
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv (n+1) (probabilityCGF gammaProbability) =ᶠ[𝓝 s]
        gammaCGFDerivative n := by
      filter_upwards [isOpen_Iio.mem_nhds hs] with u hu
      exact ih u hu
    exact ((gamma_cgf_derivative_step n s hs).congr_of_eventuallyEq he).deriv

theorem gamma_probability_cumulants (n : ℕ) :
    probabilityCumulant gammaProbability (n+1) = 2*(n.factorial : ℝ) := by
  rw [probabilityCumulant, gamma_cgf_iterated_derivative n 0 (by norm_num)]
  simp [gammaCGFDerivative]

end
end Sigma
