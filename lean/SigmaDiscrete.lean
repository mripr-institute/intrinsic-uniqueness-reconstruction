import SigmaPlacedZeros
import SigmaAffineCurvature

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology

def placedLogDerivative (μ a : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  (-1 : ℝ)^(n+1)*(n+1).factorial*(μ/(μ*r+a))^(n+2)

theorem placedLogDerivative_step (μ a : ℝ) (n : ℕ) (r : ℝ)
    (hr : 0 < μ*r+a) :
    HasDerivAt (placedLogDerivative μ a n) (placedLogDerivative μ a (n+1) r) r := by
  have hd := (((hasDerivAt_const r μ).div
    (((hasDerivAt_id r).const_mul μ).add_const a) (ne_of_gt hr)).pow (n+2)).const_mul
    ((-1 : ℝ)^(n+1)*(n+1).factorial)
  convert hd using 1
  simp only [placedLogDerivative, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat, mul_zero, zero_sub, mul_one]
  have hn : n+1+2 = (n+2)+1 := by omega
  rw [hn, pow_succ, show n+1+1 = (n+1)+1 by omega, pow_succ]
  field_simp
  ring

theorem placed_log_iteratedDeriv (μ a : ℝ) (n : ℕ) :
    ∀ r, 0 < μ*r+a → iteratedDeriv (n+2) (placed μ a) r = placedLogDerivative μ a n r := by
  induction n with
  | zero =>
    intro r hr
    simpa [iteratedDeriv_succ, placedLogDerivative] using placed_second_deriv hr
  | succ n ih =>
    intro r hr
    rw [show n+1+2 = (n+2)+1 by omega, iteratedDeriv_succ]
    have he : iteratedDeriv (n+2) (placed μ a) =ᶠ[𝓝 r] placedLogDerivative μ a n := by
      have ho : IsOpen {x : ℝ | 0 < μ*x+a} :=
        isOpen_lt continuous_const ((continuous_const.mul continuous_id).add continuous_const)
      filter_upwards [ho.mem_nhds hr] with x hx
      exact ih x hx
    exact ((placedLogDerivative_step μ a n r hr).congr_of_eventuallyEq he).deriv

theorem derivative_zero_spacing (μ a : ℝ) (hμ : μ ≠ 0) (n : ℕ) :
    (((n+1 : ℕ) : ℝ)-a)/μ-((n : ℝ)-a)/μ = 1/μ := by
  push_cast
  ring

theorem two_indexed_derivative_zeros_identify (μ a ν b : ℝ)
    (hμ : μ ≠ 0) (hν : ν ≠ 0) (n : ℕ)
    (h0 : ((n : ℝ)-a)/μ = ((n : ℝ)-b)/ν)
    (h1 : (((n+1 : ℕ) : ℝ)-a)/μ = (((n+1 : ℕ) : ℝ)-b)/ν) :
    μ = ν ∧ a = b := by
  have hs : 1/μ = 1/ν := by
    rw [← derivative_zero_spacing μ a hμ n, h0, h1, derivative_zero_spacing ν b hν n]
  have hm : μ = ν := inv_injective (by simpa only [one_div] using hs)
  refine ⟨hm, ?_⟩
  rw [hm] at h0
  have he := (div_left_inj' hν).mp h0
  linarith

theorem second_difference_sequence_unique (f g : ℕ → ℝ)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (hΔ : ∀ n, f (n+2)-2*f (n+1)+f n = g (n+2)-2*g (n+1)+g n) : f = g := by
  have he : ∀ n, f n = g n ∧ f (n+1) = g (n+1) := by
    intro n
    induction n with
    | zero => exact ⟨h0,h1⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hd := hΔ n
      rw [ih.1, ih.2] at hd
      linarith
  funext n
  exact (he n).1

end
end Sigma
