import SigmaPlacement
import SigmaZeros
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

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

/-- The unnormalized shape family, with amplitude independent of shape and rate. -/
def affineExponentialDensity (C γ μ r : ℝ) : ℝ := C*(1+γ*r)*Real.exp (-μ*r)

def affineExponentialDerivative (C γ μ : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  C*(-μ)^n*Real.exp (-μ*r)*(((n+1 : ℕ) : ℝ)*γ-μ*(1+γ*r))

theorem affine_exponential_first_derivative (C γ μ r : ℝ) :
    HasDerivAt (affineExponentialDensity C γ μ)
      (affineExponentialDerivative C γ μ 0 r) r := by
  have hd := ((((hasDerivAt_id r).const_mul γ).const_add 1).const_mul C).mul
    (((hasDerivAt_id r).const_mul (-μ)).exp)
  convert hd using 1
  simp [affineExponentialDensity, affineExponentialDerivative]
  ring

theorem affine_exponential_derivative_step (C γ μ : ℝ) (n : ℕ) (r : ℝ) :
    HasDerivAt (affineExponentialDerivative C γ μ n)
      (affineExponentialDerivative C γ μ (n+1) r) r := by
  have hd := ((((hasDerivAt_id r).const_mul (-μ)).exp).const_mul (C*(-μ)^n)).mul
    ((hasDerivAt_const r (((n+1 : ℕ) : ℝ)*γ)).sub
      ((((hasDerivAt_id r).const_mul γ).const_add 1).const_mul μ))
  convert hd using 1
  simp only [affineExponentialDerivative, pow_succ, Nat.cast_add, Nat.cast_one, id_eq]
  ring

theorem affine_exponential_iteratedDeriv (C γ μ : ℝ) (n : ℕ) :
    iteratedDeriv (n+1) (affineExponentialDensity C γ μ) =
      affineExponentialDerivative C γ μ n := by
  induction n with
  | zero =>
    funext r
    simpa only [Nat.zero_add, iteratedDeriv_one] using (affine_exponential_first_derivative C γ μ r).deriv
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext r
    exact (affine_exponential_derivative_step C γ μ n r).deriv

theorem affine_exponential_exact_zero {C γ μ : ℝ} (hC : 0 < C)
    (hγ : 0 < γ) (hμ : 0 < μ) (n : ℕ) (r : ℝ) :
    iteratedDeriv (n+1) (affineExponentialDensity C γ μ) r = 0 ↔
      r = ((n+1 : ℕ) : ℝ)/μ-1/γ := by
  rw [affine_exponential_iteratedDeriv]
  have hp : C*(-μ)^n*Real.exp (-μ*r) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hC.ne' (pow_ne_zero _ (neg_ne_zero.mpr hμ.ne')))
      (Real.exp_ne_zero _)
  rw [affineExponentialDerivative, mul_eq_zero, or_iff_right hp]
  have he : ((n+1 : ℕ) : ℝ)*γ-μ*(1+γ*r) =
      μ*γ*(((n+1 : ℕ) : ℝ)/μ-1/γ-r) := by field_simp; ring
  rw [he, mul_eq_zero, or_iff_right (mul_ne_zero hμ.ne' hγ.ne')]
  constructor <;> intro h <;> linarith

theorem affine_exponential_mass {μ : ℝ} (hμ : 0 < μ) (C γ : ℝ) :
    (∫ r : ℝ in Ioi 0, affineExponentialDensity C γ μ r) = C*(1/μ+γ/μ^2) := by
  have h0 := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := μ)
    (by norm_num) hμ
  have h1 := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := μ)
    (by norm_num) hμ
  simp only [sub_self, Real.rpow_zero, one_mul, Real.Gamma_one, Real.rpow_one,
    mul_one] at h0
  have hg : Real.Gamma 2 = 1 := by
    simp
  norm_num only [show (2 : ℝ)-1=1 by norm_num, Real.rpow_one, Real.rpow_two,
    hg, mul_one] at h1
  have hi0 : MeasureTheory.IntegrableOn (fun r : ℝ => Real.exp (-(μ*r))) (Ioi 0) :=
    MeasureTheory.Integrable.of_integral_ne_zero (by rw [h0]; positivity)
  have hi1 : MeasureTheory.IntegrableOn (fun r : ℝ => r*Real.exp (-(μ*r))) (Ioi 0) :=
    MeasureTheory.Integrable.of_integral_ne_zero (by rw [h1]; positivity)
  have he : affineExponentialDensity C γ μ = fun r =>
      C*(Real.exp (-(μ*r))+γ*(r*Real.exp (-(μ*r)))) := by
    funext r
    simp only [affineExponentialDensity, neg_mul]
    ring
  rw [he, MeasureTheory.integral_mul_left,
    MeasureTheory.integral_add hi0 (hi1.const_mul γ),
    MeasureTheory.integral_mul_left, h0, h1]
  ring

theorem affine_exponential_mass_identifies_amplitude {μ γ C D : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ)
    (hm : (∫ r : ℝ in Ioi 0, affineExponentialDensity C γ μ r) =
      ∫ r : ℝ in Ioi 0, affineExponentialDensity D γ μ r) : C = D := by
  rw [affine_exponential_mass hμ, affine_exponential_mass hμ] at hm
  exact mul_right_cancel₀ (ne_of_gt (by positivity : 0 < 1/μ+γ/μ^2)) hm

theorem affine_exponential_indexed_zeros_identify {μ γ ν δ : ℝ}
    (n : ℕ)
    (h0 : (n : ℝ)/μ-1/γ = (n : ℝ)/ν-1/δ)
    (h1 : ((n+1 : ℕ) : ℝ)/μ-1/γ = ((n+1 : ℕ) : ℝ)/ν-1/δ) :
    μ = ν ∧ γ = δ := by
  have hdiff : 1/μ = 1/ν := by
    push_cast at h1
    have ha : ((n : ℝ)+1)/μ-1/γ-((n : ℝ)/μ-1/γ) = 1/μ := by ring
    have hb : ((n : ℝ)+1)/ν-1/δ-((n : ℝ)/ν-1/δ) = 1/ν := by ring
    rw [← ha, h0, h1, hb]
  have hm : μ = ν := inv_injective (by simpa only [one_div] using hdiff)
  refine ⟨hm, ?_⟩
  rw [hm] at h0
  exact inv_injective (by simpa only [one_div] using (show 1/γ=1/δ by linarith))

end
end Sigma
