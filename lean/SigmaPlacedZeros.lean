import SigmaPlacement
import SigmaZeros

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology

def placedExpDerivative (μ a : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  μ*Real.exp a/(1+a)*μ^n*gammaDerivative n (μ*r+a)

theorem placedExpDerivative_step (μ a : ℝ) (n : ℕ) (r : ℝ) :
    HasDerivAt (placedExpDerivative μ a n) (placedExpDerivative μ a (n+1) r) r := by
  have hd := ((gammaDerivative_step n (μ*r+a)).comp r
    (((hasDerivAt_id r).const_mul μ).add_const a)).const_mul
    (μ*Real.exp a/(1+a)*μ^n)
  convert hd using 1
  simp only [placedExpDerivative, pow_succ]
  ring

theorem placed_density_iteratedDeriv {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a)
    (n : ℕ) : ∀ r : ℝ, 0 < μ*r+a →
    iteratedDeriv n (fun r => Real.exp (placed μ a r)) r = placedExpDerivative μ a n r := by
  induction n with
  | zero =>
    intro r hr
    simpa [placedExpDerivative, gammaDerivative, p, SigmaPresentations.density] using placed_density_identity hμ ha hr
  | succ n ih =>
    intro r hr
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (fun r => Real.exp (placed μ a r)) =ᶠ[nhds r]
        placedExpDerivative μ a n := by
      have ho : IsOpen {x : ℝ | 0 < μ*x+a} :=
        isOpen_lt continuous_const ((continuous_const.mul continuous_id).add continuous_const)
      filter_upwards [ho.mem_nhds hr] with x hx
      exact ih x hx
    exact ((placedExpDerivative_step μ a n r).congr_of_eventuallyEq he).deriv

theorem placed_density_exact_derivative_zero {μ a r : ℝ}
    (hμ : 0 < μ) (ha : 0 < a) (ht : 0 < μ*r+a) (n : ℕ) :
    iteratedDeriv n (fun r => Real.exp (placed μ a r)) r = 0 ↔ r = (n-a)/μ := by
  rw [placed_density_iteratedDeriv hμ ha n r ht]
  have hcoef : μ*Real.exp a/(1+a)*μ^n*(-1 : ℝ)^n ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (ne_of_gt (div_pos (mul_pos hμ (Real.exp_pos _)) (by linarith)))
        (pow_ne_zero _ (ne_of_gt hμ))
    · exact pow_ne_zero _ (by norm_num)
  have he : placedExpDerivative μ a n r =
      (μ*Real.exp a/(1+a)*μ^n*(-1 : ℝ)^n)*(μ*r+a-n)*Real.exp (-(μ*r+a)) := by
    unfold placedExpDerivative gammaDerivative
    ring
  rw [he]
  simp only [mul_eq_zero, hcoef, Real.exp_ne_zero, or_false, false_or]
  rw [eq_div_iff (ne_of_gt hμ)]
  constructor <;> intro h <;> nlinarith

end
end Sigma
