import SigmaProbGamma
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Sigma
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
set_option maxHeartbeats 6000000

/-- The exact Gamma(2,1) exponential monomial integral used in the
Hille--Hardy generating-transform calculation. -/
theorem gamma_probability_exp_monomial_integral (k : ℕ) {s : ℝ} (hs : -1 < s) :
    (∫ y : ℝ, Real.exp (-(s*y))*y^k ∂gammaProbability) =
      ((k+1).factorial:ℝ)/(1+s)^(k+2) := by
  have hb : 0 < 1+s := by linarith
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (k:ℝ)+2) (r := 1+s) (by positivity) hb
  have hg : Real.Gamma ((k:ℝ)+2) = ((k+1).factorial:ℝ) := by
    convert Real.Gamma_nat_eq_factorial (k+1) using 1 <;> push_cast <;> ring
  rw [hg] at hi
  have hpow : (↑k + 2 : ℝ) = ((k+2:ℕ):ℝ) := by push_cast; ring
  rw [hpow, Real.rpow_natCast] at hi
  rw [gamma_probability_integral]
  have htarget : ((k+1).factorial:ℝ)/(1+s)^(k+2) =
      (1/(1+s))^(k+2) * ((k+1).factorial:ℝ) := by
    rw [one_div, inv_pow, div_eq_mul_inv]
    ring
  rw [htarget, ← hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have hypos : 0 < y := hy
  simp only [SigmaPresentations.density]
  have hk : ((k+2:ℕ):ℝ)-1 = ((k+1:ℕ):ℝ) := by push_cast; ring
  rw [hk, Real.rpow_natCast]
  have he : Real.exp (-y) * Real.exp (-(s*y)) =
      Real.exp (-(1+s)*y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    y * Real.exp (-y) * (Real.exp (-(s*y)) * y^k) =
        (Real.exp (-y) * Real.exp (-(s*y))) * y^(k+1) := by
          rw [pow_succ]
          ring
    _ = y^(k+1) * Real.exp (-((1+s)*y)) := by
      rw [he]
      simp only [neg_mul]
      exact mul_comm _ _

/-- The terms in the paper's defining series for the modified Bessel function `I₁`. -/
def modifiedBesselI1Term (t : ℝ) (m : ℕ) : ℝ :=
  (t/2) * ((t/2)^(2*m) / ((m.factorial:ℝ)*((m+1).factorial:ℝ)))

theorem modified_bessel_i1_term_summable (t : ℝ) :
    Summable (modifiedBesselI1Term t) := by
  have hexp : Summable (fun n : ℕ => ‖t/2‖^n / (n.factorial:ℝ)) := by
    simpa only [Real.norm_eq_abs, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ℝ ‖t/2‖).summable
  have hfac (m : ℕ) : (m.factorial:ℝ) ≤ ((m+1).factorial:ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    nlinarith [show (0:ℝ) ≤ (m.factorial:ℝ) by positivity]
  have hbound (m : ℕ) :
      ‖modifiedBesselI1Term t m‖ ≤
        ‖t/2‖ * (‖t/2‖^(2*m) / (m.factorial:ℝ)^2) := by
    simp only [modifiedBesselI1Term, norm_mul, norm_div, norm_pow,
      Real.norm_eq_abs]
    simp only [abs_of_nonneg (show (0:ℝ) ≤ (m.factorial:ℝ) by positivity),
      abs_of_nonneg (show (0:ℝ) ≤ ((m+1).factorial:ℝ) by positivity)]
    rw [← abs_div]
    change |t/2| * (|t/2|^(2*m) /
      ((m.factorial:ℝ)*((m+1).factorial:ℝ))) ≤
      |t/2| * (|t/2|^(2*m) / (m.factorial:ℝ)^2)
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg _) _)
    have hpos : 0 < (m.factorial:ℝ) := by positivity
    have hh := one_div_le_one_div_of_le (mul_pos hpos hpos)
      (mul_le_mul_of_nonneg_left (hfac m) hpos.le)
    simpa only [sq, one_div] using hh
  have hrough : Summable (fun m : ℕ => ‖t/2‖^(2*m) / (m.factorial:ℝ)^2) := by
    have he : Summable (fun m : ℕ => (‖t/2‖^2)^m / (m.factorial:ℝ)) := by
      simpa only [Real.norm_eq_abs, ← Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp ℝ (‖t/2‖^2)).summable
    apply Summable.of_nonneg_of_le
      (fun m => div_nonneg (pow_nonneg (norm_nonneg _) _) (sq_nonneg _))
      (fun m => ?_) he
    rw [← pow_mul]
    have hm : (1:ℝ) ≤ (m.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos m
    have hdiv : 1 / (m.factorial:ℝ)^2 ≤ 1 / (m.factorial:ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    simpa only [div_eq_mul_inv, one_mul] using
      (mul_le_mul_of_nonneg_left (by simpa only [one_div] using hdiv)
        (pow_nonneg (norm_nonneg (t/2)) (2*m)))
  exact Summable.of_norm_bounded _ (hrough.mul_left ‖t/2‖) hbound

/-- Modified Bessel `I₁`, defined by its exact paper series. -/
def modifiedBesselI1 (t : ℝ) : ℝ := ∑' m : ℕ, modifiedBesselI1Term t m

/-- The generating function for parameter-one Laguerre polynomials. -/
def laguerreGeneratingFunction (z y : ℝ) : ℝ :=
  (1-z)⁻¹^2 * Real.exp (-y*z/(1-z))

/-- The closed Hille--Hardy expression on the positive quadrant. -/
def laguerreHeatKernelClosed (τ x y : ℝ) : ℝ :=
  (Real.exp (-Real.exp (-τ)*(x+y)/(1-Real.exp (-τ))) /
    ((1-Real.exp (-τ))*Real.sqrt (Real.exp (-τ)*x*y))) *
      modifiedBesselI1 (2*Real.sqrt (Real.exp (-τ)*x*y)/(1-Real.exp (-τ)))

/-- A total representative; the Gamma measure is supported on positive `y`. -/
def laguerreHeatKernel (τ x y : ℝ) : ℝ :=
  if 0 < y then laguerreHeatKernelClosed τ x y else 0

/-- The nonnegative series obtained by expanding the Bessel factor. -/
theorem laguerre_heat_kernel_closed_series {τ x y : ℝ}
    (hτ : 0 < τ) (hx : 0 < x) (hy : 0 < y) :
    laguerreHeatKernelClosed τ x y =
      ∑' m : ℕ, Real.exp (-Real.exp (-τ)*(x+y)/(1-Real.exp (-τ))) *
        ((Real.exp (-τ)*x*y)^m /
          ((m.factorial:ℝ)*((m+1).factorial:ℝ)*
            (1-Real.exp (-τ))^(2*m+2))) := by
  let r := Real.exp (-τ)
  let d := 1-r
  let v := Real.sqrt (r*x*y)
  have hr : 0 < r := Real.exp_pos _
  have hd : 0 < d := by
    dsimp [d, r]
    have : Real.exp (-τ) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hv2 : v^2 = r*x*y := by
    dsimp [v]
    rw [Real.sq_sqrt (by positivity)]
  have hv : 0 < v := Real.sqrt_pos.2 (by positivity)
  let c := Real.exp (-r*(x+y)/d)
  change c / (d*v) * (∑' m : ℕ, modifiedBesselI1Term (2*v/d) m) =
    ∑' m : ℕ, c * ((r*x*y)^m /
      ((m.factorial:ℝ)*((m+1).factorial:ℝ)*d^(2*m+2)))
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  change c / (d*v) * modifiedBesselI1Term (2*v/d) m =
    c * ((r*x*y)^m /
      ((m.factorial:ℝ)*((m+1).factorial:ℝ)*d^(2*m+2)))
  rw [modifiedBesselI1Term]
  have hsimplify : (2*v/d)/2 = v/d := by field_simp [ne_of_gt hd]; ring
  rw [hsimplify]
  rw [← hv2]
  have hpow : (v^2)^m = v^(2*m) := by rw [← pow_mul]
  rw [hpow]
  rw [div_pow, pow_add]
  field_simp [ne_of_gt hd, ne_of_gt hv, Nat.factorial_ne_zero]
  ring

theorem modified_bessel_i1_pos {t : ℝ} (ht : 0 < t) :
    0 < modifiedBesselI1 t := by
  unfold modifiedBesselI1
  apply tsum_pos (modified_bessel_i1_term_summable t)
    (by intro m; unfold modifiedBesselI1Term; positivity) 0
  simpa [modifiedBesselI1Term] using (half_pos ht)

theorem laguerre_heat_kernel_closed_pos {τ x y : ℝ}
    (hτ : 0 < τ) (hx : 0 < x) (hy : 0 < y) :
    0 < laguerreHeatKernelClosed τ x y := by
  have hr : 0 < Real.exp (-τ) := Real.exp_pos _
  have hd : 0 < 1-Real.exp (-τ) := by
    have : Real.exp (-τ) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  unfold laguerreHeatKernelClosed
  apply mul_pos
  · exact div_pos (Real.exp_pos _) (mul_pos hd (Real.sqrt_pos.2 (by positivity)))
  · apply modified_bessel_i1_pos
    exact div_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by positivity))) hd

theorem laguerre_heat_kernel_closed_symm (τ x y : ℝ) :
    laguerreHeatKernelClosed τ x y = laguerreHeatKernelClosed τ y x := by
  simp only [laguerreHeatKernelClosed]
  congr 1
  · congr 1
    · congr 1 <;> ring
    · congr 1 <;> ring
  · congr 1 <;> ring

private theorem gamma_probability_exp_monomial_integrable {β : ℝ} (hβ : -1 < β)
    (m : ℕ) : Integrable (fun y : ℝ => Real.exp (-(β*y))*y^m) gammaProbability := by
  apply Integrable.of_integral_ne_zero
  rw [gamma_probability_exp_monomial_integral m hβ]
  exact div_ne_zero (by positivity) (pow_ne_zero _ (ne_of_gt (by linarith)))

/-- The termwise Gamma integral that drives the Hille--Hardy transform. -/
theorem gamma_bessel_series_integral {a β : ℝ} (ha : 0 ≤ a) (hβ : -1 < β) :
    (∫ y : ℝ, (∑' m : ℕ,
      (a^m / ((m.factorial:ℝ)*((m+1).factorial:ℝ))) *
        Real.exp (-(β*y)) * y^m) ∂gammaProbability) =
      (1+β)⁻¹^2 * Real.exp (a/(1+β)) := by
  let F : ℕ → ℝ → ℝ := fun m y =>
    (a^m / ((m.factorial:ℝ)*((m+1).factorial:ℝ))) *
      Real.exp (-(β*y)) * y^m
  have hb : 0 < 1+β := by linarith
  have hFint (m : ℕ) : Integrable (F m) gammaProbability := by
    have h := (gamma_probability_exp_monomial_integrable hβ m).const_mul
      (a^m / ((m.factorial:ℝ)*((m+1).factorial:ℝ)))
    convert h using 1
    funext y
    simp only [F]
    ring
  have hFnonneg (m : ℕ) : ∀ᵐ y : ℝ ∂gammaProbability, 0 ≤ F m y := by
    have hnonneg : ∀ᵐ y : ℝ ∂gammaProbability, 0 ≤ y := by
      simpa only [ae_iff, not_le] using gamma_probability_negative_ray
    filter_upwards [hnonneg] with y hy
    dsimp [F]
    positivity
  have hFformula (m : ℕ) :
      (∫ y : ℝ, F m y ∂gammaProbability) =
        (1+β)⁻¹^2 * ((a/(1+β))^m / (m.factorial:ℝ)) := by
    have hfun : F m = fun y =>
        (a^m / ((m.factorial:ℝ)*((m+1).factorial:ℝ))) *
          (Real.exp (-(β*y))*y^m) := by
      funext y
      dsimp [F]
      ring
    rw [hfun]
    rw [integral_mul_left, gamma_probability_exp_monomial_integral m hβ]
    rw [div_pow, pow_add]
    field_simp [ne_of_gt hb, Nat.factorial_ne_zero]
    ring
  have hFnorm (m : ℕ) :
      (∫ y : ℝ, ‖F m y‖ ∂gammaProbability) =
        (1+β)⁻¹^2 * ((a/(1+β))^m / (m.factorial:ℝ)) := by
    rw [← hFformula]
    apply integral_congr_ae
    filter_upwards [hFnonneg m] with y hy
    exact Real.norm_eq_abs _ ▸ abs_of_nonneg hy
  have hexp : Summable (fun m : ℕ => (a/(1+β))^m / (m.factorial:ℝ)) := by
    simpa only [← Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ℝ (a/(1+β))).summable
  have hnormsum : Summable (fun m : ℕ => ∫ y : ℝ, ‖F m y‖ ∂gammaProbability) := by
    simpa only [hFnorm] using hexp.mul_left ((1+β)⁻¹^2)
  have hint := (integral_tsum_of_summable_integral_norm hFint hnormsum).symm
  change (∫ y : ℝ, ∑' m : ℕ, F m y ∂gammaProbability) = _ at hint ⊢
  rw [hint]
  simp_rw [hFformula]
  rw [tsum_mul_left]
  have he := (NormedSpace.expSeries_div_hasSum_exp ℝ (a/(1+β))).tsum_eq
  simpa only [← Real.exp_eq_exp_ℝ] using congrArg (fun t : ℝ => (1+β)⁻¹^2 * t) he

/-- Gamma integration of the actual Bessel expression gives the Laguerre
generating function at the heat-scaled parameter. -/
theorem laguerre_heat_kernel_generating_transform {τ x z : ℝ}
    (hτ : 0 < τ) (hx : 0 < x) (hz : z < 1)
    (hβ : 0 ≤ Real.exp (-τ)/(1-Real.exp (-τ))+z/(1-z)) :
    (∫ y : ℝ, laguerreHeatKernel τ x y * laguerreGeneratingFunction z y
      ∂gammaProbability) =
      laguerreGeneratingFunction (Real.exp (-τ)*z) x := by
  let r := Real.exp (-τ)
  let d := 1-r
  let β := r/d+z/(1-z)
  let a := r*x/d^2
  let C := (d⁻¹)^2 * (1-z)⁻¹^2 * Real.exp (-r*x/d)
  let F : ℕ → ℝ → ℝ := fun m y =>
    (a^m / ((m.factorial:ℝ)*((m+1).factorial:ℝ))) *
      Real.exp (-(β*y)) * y^m
  have hr : 0 < r := Real.exp_pos _
  have hd : 0 < d := by
    dsimp [d, r]
    have : Real.exp (-τ) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hzden : 0 < 1-z := by linarith
  have hb : 0 ≤ β := hβ
  have hb' : -1 < β := by linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hden : 1+β = (1-r*z)/(d*(1-z)) := by
    dsimp [β, d]
    field_simp [ne_of_gt hd, ne_of_gt hzden]
    ring
  have hrz : 0 < 1-r*z := by
    calc
      0 < (1+β)*(d*(1-z)) := mul_pos (by linarith) (mul_pos hd hzden)
      _ = 1-r*z := by rw [hden]; field_simp [ne_of_gt hd, ne_of_gt hzden]
  have hpoint (y : ℝ) (hy : 0 < y) :
      laguerreHeatKernel τ x y * laguerreGeneratingFunction z y =
        C * (∑' m : ℕ, F m y) := by
    rw [laguerreHeatKernel, if_pos hy, laguerre_heat_kernel_closed_series hτ hx hy]
    dsimp [laguerreGeneratingFunction]
    rw [← tsum_mul_right, ← tsum_mul_left]
    apply tsum_congr
    intro m
    dsimp [F, C, a, β]
    have he : -r*(x+y)/d + (-y*z/(1-z)) =
        -r*x/d + -((r/d+z/(1-z))*y) := by
      field_simp [ne_of_gt hd, ne_of_gt hzden]
      ring
    have hexp : Real.exp (-r*(x+y)/d) * Real.exp (-y*z/(1-z)) =
        Real.exp (-r*x/d) * Real.exp (-((r/d+z/(1-z))*y)) := by
      rw [← Real.exp_add, ← Real.exp_add, he]
    have hcoef :
        ((r*x*y)^m /
          ((m.factorial:ℝ)*((m+1).factorial:ℝ)*d^(2*m+2))) * (1-z)⁻¹^2 =
        (d⁻¹)^2 * (1-z)⁻¹^2 *
          (((r*x/d^2)^m /
            ((m.factorial:ℝ)*((m+1).factorial:ℝ)))*y^m) := by
      rw [show (r*x*y)^m = (r*x)^m*y^m by rw [mul_pow],
        div_pow, ← pow_mul, pow_add]
      field_simp [ne_of_gt hd, ne_of_gt hzden, Nat.factorial_ne_zero]
      ring
    change Real.exp (-r*(x+y)/d) *
        ((r*x*y)^m /
          ((m.factorial:ℝ)*((m+1).factorial:ℝ)*d^(2*m+2))) *
        ((1-z)⁻¹^2 * Real.exp (-y*z/(1-z))) =
      (d⁻¹)^2 * (1-z)⁻¹^2 * Real.exp (-r*x/d) *
        (((r*x/d^2)^m /
          ((m.factorial:ℝ)*((m+1).factorial:ℝ))) *
          Real.exp (-((r/d+z/(1-z))*y)) * y^m)
    calc
      _ = (Real.exp (-r*(x+y)/d) * Real.exp (-y*z/(1-z))) *
          (((r*x*y)^m /
            ((m.factorial:ℝ)*((m+1).factorial:ℝ)*d^(2*m+2))) *
              (1-z)⁻¹^2) := by ring
      _ = (Real.exp (-r*x/d) * Real.exp (-((r/d+z/(1-z))*y))) *
          ((d⁻¹)^2 * (1-z)⁻¹^2 *
            (((r*x/d^2)^m /
              ((m.factorial:ℝ)*((m+1).factorial:ℝ)))*y^m)) := by
              rw [hexp, hcoef]
      _ = _ := by ring
  have hpos : ∀ᵐ y : ℝ ∂gammaProbability, 0 < y := by
    have hnonneg : ∀ᵐ y : ℝ ∂gammaProbability, 0 ≤ y := by
      simpa only [ae_iff, not_le] using gamma_probability_negative_ray
    have hne : ∀ᵐ y : ℝ ∂gammaProbability, y ≠ 0 := by
      rw [ae_iff]
      simpa only [not_ne_iff, Set.setOf_eq_eq_singleton] using
        gamma_probability_no_atom 0
    filter_upwards [hnonneg, hne] with y hy hyn
    exact lt_of_le_of_ne hy (Ne.symm hyn)
  have hcongr :
      (fun y : ℝ => laguerreHeatKernel τ x y * laguerreGeneratingFunction z y) =ᵐ[
        gammaProbability] fun y => C * (∑' m : ℕ, F m y) := by
    filter_upwards [hpos] with y hy
    exact hpoint y hy
  rw [integral_congr_ae hcongr, integral_mul_left]
  have hgamma := gamma_bessel_series_integral ha hb'
  change (∫ y : ℝ, ∑' m : ℕ, F m y ∂gammaProbability) = _ at hgamma
  rw [hgamma]
  have hscalar : (d⁻¹)^2 * (1-z)⁻¹^2 * (1+β)⁻¹^2 =
      (1-r*z)⁻¹^2 := by
    rw [hden]
    field_simp [ne_of_gt hd, ne_of_gt hzden, ne_of_gt hrz]
    ring
  have hexparg : -r*x/d + a/(1+β) = -x*(r*z)/(1-r*z) := by
    rw [hden]
    dsimp [a]
    field_simp [ne_of_gt hd, ne_of_gt hzden, ne_of_gt hrz]
    ring
  calc
    C * ((1+β)⁻¹^2 * Real.exp (a/(1+β))) =
        ((d⁻¹)^2 * (1-z)⁻¹^2 * (1+β)⁻¹^2) *
          Real.exp (-r*x/d + a/(1+β)) := by
            rw [Real.exp_add]
            dsimp [C]
            ring
    _ = (1-r*z)⁻¹^2 * Real.exp (-x*(r*z)/(1-r*z)) := by
      rw [hscalar, hexparg]
    _ = laguerreGeneratingFunction (r*z) x := by
      unfold laguerreGeneratingFunction
      ring

theorem laguerre_heat_kernel_row_mass {τ x : ℝ} (hτ : 0 < τ) (hx : 0 < x) :
    (∫ y : ℝ, laguerreHeatKernel τ x y ∂gammaProbability) = 1 := by
  have hβ : 0 ≤ Real.exp (-τ)/(1-Real.exp (-τ)) + (0:ℝ)/(1-0) := by
    have hd : 0 < 1-Real.exp (-τ) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -τ < 0)
      linarith
    positivity
  have h := laguerre_heat_kernel_generating_transform hτ hx
    (show (0:ℝ) < 1 by norm_num) hβ
  simpa [laguerreGeneratingFunction] using h

theorem laguerre_heat_kernel_pos {τ x y : ℝ}
    (hτ : 0 < τ) (hx : 0 < x) (hy : 0 < y) :
    0 < laguerreHeatKernel τ x y := by
  rw [laguerreHeatKernel, if_pos hy]
  exact laguerre_heat_kernel_closed_pos hτ hx hy

theorem laguerre_heat_kernel_symm {τ x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    laguerreHeatKernel τ x y = laguerreHeatKernel τ y x := by
  rw [laguerreHeatKernel, if_pos hy, laguerreHeatKernel, if_pos hx]
  exact laguerre_heat_kernel_closed_symm τ x y

end
end Sigma
