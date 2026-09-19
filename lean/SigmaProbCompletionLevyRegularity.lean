import SigmaProbLevy
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import SigmaProbStieltjes
import SigmaProbCompletionSamples

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- A positive derivative majorant. The recurrence differentiates positive
linear combinations of exp(-x)/x^(k+1), retaining their exact coefficients. -/
def gammaLevyDerivativeMajorant : ℕ → ℕ → ℝ → ℝ
  | 0, k, x => 2*Real.exp (-x)/x^(k+1)
  | n+1, k, x => gammaLevyDerivativeMajorant n k x+
      (k+1:ℝ)*gammaLevyDerivativeMajorant n (k+1) x

theorem gamma_levy_derivative_majorant_nonnegative (n k : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ gammaLevyDerivativeMajorant n k x := by
  induction n generalizing k with
  | zero => simp only [gammaLevyDerivativeMajorant]; positivity
  | succ n ih =>
    exact add_nonneg (ih k) (mul_nonneg (by positivity) (ih (k+1)))

theorem gamma_levy_derivative_majorant_hasDerivAt (n k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (gammaLevyDerivativeMajorant n k)
      (-gammaLevyDerivativeMajorant (n+1) k x) x := by
  induction n generalizing k with
  | zero =>
    have hd := ((((hasDerivAt_id x).neg.exp).const_mul 2).div
      ((hasDerivAt_id x).pow (k+1)) (pow_ne_zero _ hx.ne'))
    convert hd using 1
    simp only [gammaLevyDerivativeMajorant, Nat.cast_add, Nat.cast_one, id_eq]
    simp only [Nat.add_sub_cancel, mul_one]
    field_simp
    ring
  | succ n ih =>
    have hd := (ih k).add ((ih (k+1)).const_mul (k+1:ℝ))
    convert hd using 1
    simp only [gammaLevyDerivativeMajorant]
    ring

theorem gamma_levy_iterated_derivative (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n gammaLevyDensity x = (-1:ℝ)^n*gammaLevyDerivativeMajorant n 0 x := by
  induction n generalizing x with
  | zero => simp [iteratedDeriv_zero, gammaLevyDensity, gammaLevyDerivativeMajorant]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n gammaLevyDensity =ᶠ[𝓝 x]
        (fun y => (-1:ℝ)^n*gammaLevyDerivativeMajorant n 0 y) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact ih hy
    rw [he.deriv_eq]
    rw [((gamma_levy_derivative_majorant_hasDerivAt n 0 hx).const_mul ((-1:ℝ)^n)).deriv]
    rw [pow_succ]
    ring

/-- The exact complete-monotonicity inequalities for the actual Lévy density,
at every differentiation order on the open positive ray. -/
theorem gamma_levy_density_completely_monotone (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ (-1:ℝ)^n*iteratedDeriv n gammaLevyDensity x := by
  rw [gamma_levy_iterated_derivative n hx, ← mul_assoc, ← pow_add,
    ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  exact gamma_levy_derivative_majorant_nonnegative n 0 hx

theorem gamma_levy_density_smooth : ContDiffOn ℝ ⊤ gammaLevyDensity (Ioi 0) := by
  unfold gammaLevyDensity
  apply (contDiffOn_const.mul (contDiffOn_id.neg.exp)).div contDiffOn_id
  intro x hx
  exact ne_of_gt hx

theorem gamma_levy_completely_monotone : CompletelyMonotoneOnPositive gammaLevyDensity :=
  fun n _x hx => gamma_levy_density_completely_monotone n hx

/-- The Stieltjes representation has the concrete measure 2δ₁. -/
theorem gamma_exponent_derivative_stieltjes :
    HasStieltjesRepresentation (deriv gammaLaplaceExponent) := by
  refine ⟨0,0,(2:ℝ≥0∞) • Measure.dirac 1, le_rfl, le_rfl, ?_, ?_, ?_⟩
  · exact Measure.ae_smul_measure (by simp) _
  · apply Integrable.smul_measure _ (by norm_num)
    apply (integrable_const ((1+(1:ℝ))⁻¹)).congr
    exact (ae_eq_dirac (fun t : ℝ => (1+t)⁻¹)).symm
  · intro x hx
    rw [(gamma_exponent_derivative x hx.le).deriv, integral_smul_measure, integral_dirac]
    norm_num
    ring

theorem gamma_exponent_sublinear :
    Tendsto (fun l : ℝ => gammaLaplaceExponent l/l) atTop (𝓝 0) := by
  have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 (by norm_num)).comp
    (tendsto_const_nhds.add_atTop tendsto_id : Tendsto (fun x : ℝ => 1+x) atTop atTop)
  have ht' : Tendsto (fun x : ℝ => Real.log (1+x)/x) atTop (𝓝 0) := by
    simpa [Function.comp_def] using ht
  simpa only [gammaLaplaceExponent, mul_zero, mul_div_assoc] using ht'.const_mul 2

theorem gamma_drifted_exponent_ratio (d : ℝ) :
    Tendsto (fun l : ℝ => (d*l+gammaLaplaceExponent l)/l) atTop (𝓝 d) := by
  have ht := (tendsto_const_nhds (x := d)).add gamma_exponent_sublinear
  apply (show Tendsto (fun l : ℝ => d+gammaLaplaceExponent l/l) atTop (𝓝 d) by
    simpa using ht).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with l hl
  rw [add_div, mul_div_cancel_right₀ _ hl.ne']

theorem gamma_drift_zero_iff_sublinear (d : ℝ) :
    d = 0 ↔ Tendsto (fun l : ℝ => (d*l+gammaLaplaceExponent l)/l) atTop (𝓝 0) := by
  constructor
  · intro hd
    simpa [hd] using gamma_drifted_exponent_ratio 0
  · intro ht
    exact tendsto_nhds_unique (gamma_drifted_exponent_ratio d) ht

/-- A Bernstein representation whose actual Lévy measure has a smooth,
completely monotone density on the positive ray. -/
def HasCompleteBernsteinRepresentation (f : ℝ → ℝ) : Prop :=
  ∃ (B : BernsteinRepresentation) (q : ℝ → ℝ),
    (∀ l : ℝ, 0 ≤ l → f l = B.exponent l) ∧
    B.levy = (volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal (q x)) ∧
    ContDiffOn ℝ ⊤ q (Ioi 0) ∧ CompletelyMonotoneOnPositive q

theorem gamma_exponent_complete_bernstein :
    HasCompleteBernsteinRepresentation gammaLaplaceExponent := by
  refine ⟨gammaBernsteinRepresentation, gammaLevyDensity, ?_, rfl,
    gamma_levy_density_smooth, gamma_levy_completely_monotone⟩
  intro l hl
  exact (gamma_bernstein_representation_exponent l hl).symm

end
end Sigma
