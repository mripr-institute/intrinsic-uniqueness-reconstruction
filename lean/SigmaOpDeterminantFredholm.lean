import SigmaOpLaguerreResolventTrace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.FDeriv.Analytic

namespace Sigma
noncomputable section
open Filter
open scoped Topology BigOperators

/-- The actual matrix of an operator compressed to the first `N` Hilbert basis vectors. -/
def hilbertCompressionMatrix {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (b : HilbertBasis ℕ ℂ H) (T : H →L[ℂ] H) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ := fun i j => @inner ℂ H _ (b i) (T (b j))

theorem hilbert_compression_matrix_diagonal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (b : HilbertBasis ℕ ℂ H) (T : H →L[ℂ] H)
    (f : ℕ → ℂ) (hT : ∀ n, T (b n) = f n • b n) (N : ℕ) :
    hilbertCompressionMatrix b T N = Matrix.diagonal (fun i : Fin N => f i) := by
  classical
  ext i j
  simp only [hilbertCompressionMatrix, hT, inner_smul_right]
  rw [← b.repr_apply_apply, b.repr_self]
  by_cases h : i = j
  · subst j
    simp [Matrix.diagonal_apply, lp.single_apply_self]
  · have hij : (i : ℕ) ≠ (j : ℕ) := fun he => h (Fin.ext he)
    simp [Matrix.diagonal_apply, h, lp.single_apply_ne _ _ _ hij]

/-- The finite Fredholm approximants use the actual squared Laguerre resolvent. -/
def laguerreFredholmApprox (z : ℂ) (N : ℕ) : ℂ :=
  (1 + z • hilbertCompressionMatrix laguerreHilbertBasis
    (laguerreSquaredResolvent 1 (by norm_num)) N).det

theorem laguerre_fredholm_approx_product (z : ℂ) (N : ℕ) :
    laguerreFredholmApprox z N = ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)^2) := by
  classical
  unfold laguerreFredholmApprox
  rw [hilbert_compression_matrix_diagonal _ _ _
    (laguerre_squared_resolvent_basis_action 1 (by norm_num))]
  have hm : (1 + z • Matrix.diagonal (fun i : Fin N =>
      (((i : ℕ) : ℂ) + ((1 : ℝ) : ℂ))⁻¹ ^ 2)) =
      Matrix.diagonal (fun i : Fin N => 1 + z / (((i : ℕ) : ℂ) + 1)^2) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [Matrix.diagonal_apply, div_eq_mul_inv, inv_pow]
    · simp [Matrix.diagonal_apply, h]
  rw [hm, Matrix.det_diagonal]
  exact Fin.prod_univ_eq_prod_range (fun n : ℕ => 1 + z / ((n : ℂ)+1)^2) N

/-- The branch-free power series occurring in the paper's square-root quotient. -/
def laguerreFredholmSeries (z : ℂ) : ℂ :=
  ∑' n : ℕ, (Real.pi : ℂ)^(2*n) * z^n / ((2*n+1).factorial : ℂ)

theorem laguerre_fredholm_series_zero : laguerreFredholmSeries 0 = 1 := by
  unfold laguerreFredholmSeries
  rw [tsum_eq_single 0]
  · norm_num
  · intro n hn
    simp [zero_pow hn]

theorem laguerre_fredholm_series_hasSum_sqrt (w : ℂ) (hw : w ≠ 0) :
    HasSum (fun n : ℕ => (Real.pi : ℂ)^(2*n) * (w^2)^n / ((2*n+1).factorial : ℂ))
      (Complex.sinh ((Real.pi : ℂ)*w) / ((Real.pi : ℂ)*w)) := by
  have hp : (Real.pi : ℂ) * w ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) hw
  have hs := (Complex.hasSum_sinh ((Real.pi : ℂ)*w)).div_const ((Real.pi : ℂ)*w)
  have he (n : ℕ) :
      (((Real.pi : ℂ)*w)^(2*n+1) / ((2*n+1).factorial : ℂ)) /
        ((Real.pi : ℂ)*w) =
      (Real.pi : ℂ)^(2*n) * (w^2)^n / ((2*n+1).factorial : ℂ) := by
    rw [pow_succ, mul_div_right_comm, mul_div_cancel_right₀ _ hp, mul_pow]
    congr 2
    rw [pow_mul]
  simp_rw [he] at hs
  exact hs

theorem laguerre_fredholm_series_sqrt (w : ℂ) (hw : w ≠ 0) :
    laguerreFredholmSeries (w^2) = Complex.sinh ((Real.pi : ℂ)*w) /
      ((Real.pi : ℂ)*w) :=
  (laguerre_fredholm_series_hasSum_sqrt w hw).tsum_eq

theorem laguerre_fredholm_product_tendsto_sqrt (w : ℂ) (hw : w ≠ 0) :
    Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N, (1 + w^2 / ((n : ℂ)+1)^2))
      atTop (𝓝 (Complex.sinh ((Real.pi : ℂ)*w) / ((Real.pi : ℂ)*w))) := by
  have hp : (Real.pi : ℂ) * (w * Complex.I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (mul_ne_zero hw Complex.I_ne_zero)
  have ht := (Complex.tendsto_euler_sin_prod (w*Complex.I)).div_const
    ((Real.pi : ℂ)*(w*Complex.I))
  have he (n : ℕ) : (1 : ℂ) - (w*Complex.I)^2 / ((n : ℂ)+1)^2 =
      1 + w^2 / ((n : ℂ)+1)^2 := by rw [mul_pow, Complex.I_sq]; ring
  simp_rw [he, mul_div_cancel_left₀ _ hp] at ht
  convert ht using 1
  rw [← mul_assoc, Complex.sin_mul_I]
  rw [mul_div_mul_right _ _ Complex.I_ne_zero]

/-- Convergence is proved for the determinants of the actual operator compressions. -/
theorem laguerre_fredholm_approx_tendsto (z : ℂ) :
    Tendsto (laguerreFredholmApprox z) atTop (𝓝 (laguerreFredholmSeries z)) := by
  change Tendsto (fun N => laguerreFredholmApprox z N) _ _
  simp_rw [laguerre_fredholm_approx_product]
  by_cases hz : z = 0
  · subst z
    simp [laguerre_fredholm_series_zero]
  · obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z (by norm_num : 0 < (2 : ℕ))
    have hw0 : w ≠ 0 := by intro h; simp [h] at hw; exact hz hw.symm
    subst z
    simpa only [laguerre_fredholm_approx_product, laguerre_fredholm_series_sqrt w hw0]
      using laguerre_fredholm_product_tendsto_sqrt w hw0

/-- The canonical Fredholm determinant is the limit of native finite compression determinants. -/
def laguerreFredholmDeterminant (z : ℂ) : ℂ :=
  limUnder atTop (laguerreFredholmApprox z)

theorem laguerre_fredholm_determinant_series (z : ℂ) :
    laguerreFredholmDeterminant z = laguerreFredholmSeries z :=
  (laguerre_fredholm_approx_tendsto z).limUnder_eq

theorem laguerre_fredholm_determinant_zero : laguerreFredholmDeterminant 0 = 1 := by
  rw [laguerre_fredholm_determinant_series, laguerre_fredholm_series_zero]

theorem laguerre_fredholm_determinant_sqrt (w : ℂ) (hw : w ≠ 0) :
    laguerreFredholmDeterminant (w^2) = Complex.sinh ((Real.pi : ℂ)*w) /
      ((Real.pi : ℂ)*w) := by
  rw [laguerre_fredholm_determinant_series, laguerre_fredholm_series_sqrt w hw]

theorem laguerre_fredholm_series_summable (z : ℂ) :
    Summable (fun n : ℕ => (Real.pi : ℂ)^(2*n) * z^n / ((2*n+1).factorial : ℂ)) := by
  by_cases hz : z = 0
  · subst z
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [zero_pow hn]
  · obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z (by norm_num : 0 < (2 : ℕ))
    have hw0 : w ≠ 0 := by intro h; simp [h] at hw; exact hz hw.symm
    subst z
    exact (laguerre_fredholm_series_hasSum_sqrt w hw0).summable

theorem laguerre_fredholm_determinant_entire (z : ℂ) :
    AnalyticAt ℂ laguerreFredholmDeterminant z := by
  let c : ℕ → ℂ := fun n => (Real.pi : ℂ)^(2*n) / ((2*n+1).factorial : ℂ)
  let p := FormalMultilinearSeries.ofScalars ℂ c
  have hr : p.radius = ⊤ := by
    apply p.radius_eq_top_of_summable_norm
    intro r
    have hs := (laguerre_fredholm_series_summable ((r : ℝ) : ℂ)).norm
    convert hs using 1
    funext n
    simp only [p, FormalMultilinearSeries.ofScalars_norm, c, norm_div, norm_mul,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg]
    ring
  have he : laguerreFredholmDeterminant = p.sum := by
    funext x
    rw [laguerre_fredholm_determinant_series]
    change laguerreFredholmSeries x = FormalMultilinearSeries.ofScalarsSum c x
    rw [FormalMultilinearSeries.ofScalars_sum_eq]
    apply tsum_congr
    intro n
    simp only [c, smul_eq_mul]
    ring
  rw [he]
  exact (p.hasFPowerSeriesOnBall (by rw [hr]; exact bot_lt_top)).analyticAt_of_mem
    (by simp [hr])

theorem laguerre_fredholm_determinant_zeros (z : ℂ) :
    laguerreFredholmDeterminant z = 0 ↔ ∃ k : ℤ, k ≠ 0 ∧ z = -(k : ℂ)^2 := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  constructor
  · intro hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, laguerre_fredholm_determinant_zero] at hz
      exact one_ne_zero hz
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z (by norm_num : 0 < (2 : ℕ))
    have hw0 : w ≠ 0 := by intro h; simp [h] at hw; exact hz0 hw.symm
    rw [← hw, laguerre_fredholm_determinant_sqrt w hw0] at hz
    have hsinh : Complex.sinh ((Real.pi : ℂ)*w) = 0 :=
      (div_eq_zero_iff).mp hz |>.resolve_right (mul_ne_zero hp hw0)
    have hsin : Complex.sin ((Real.pi : ℂ)*(w*Complex.I)) = 0 := by
      rw [← mul_assoc, Complex.sin_mul_I, hsinh, zero_mul]
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hsin
    have he : w*Complex.I = (k : ℂ) := by
      apply mul_left_cancel₀ hp
      simpa only [mul_comm (k : ℂ) (Real.pi : ℂ)] using hk
    have hk0 : k ≠ 0 := by
      intro h
      simp [h, mul_eq_zero, hw0, Complex.I_ne_zero] at he
    refine ⟨k, hk0, ?_⟩
    rw [← hw, ← he, mul_pow, Complex.I_sq]
    ring
  · rintro ⟨k, hk, rfl⟩
    have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have he : (-(k : ℂ)^2) = ((k : ℂ)*Complex.I)^2 := by
      rw [mul_pow, Complex.I_sq]; ring
    rw [he, laguerre_fredholm_determinant_sqrt _ (mul_ne_zero hk0 Complex.I_ne_zero)]
    have hs : Complex.sinh ((Real.pi : ℂ)*((k : ℂ)*Complex.I)) = 0 := by
      have hh : Complex.sin (((Real.pi : ℂ)*((k : ℂ)*Complex.I))*Complex.I) = 0 := by
        apply Complex.sin_eq_zero_iff.mpr
        refine ⟨-k, ?_⟩
        push_cast
        calc
          _ = (Real.pi : ℂ)*(k : ℂ)*(Complex.I*Complex.I) := by ring
          _ = -(k : ℂ)*(Real.pi : ℂ) := by rw [Complex.I_mul_I]; ring
      rw [Complex.sin_mul_I, mul_eq_zero] at hh
      exact hh.resolve_right Complex.I_ne_zero
    rw [hs, zero_div]

theorem laguerre_fredholm_determinant_sinh (w : ℂ) :
    laguerreFredholmDeterminant (w^2) * ((Real.pi : ℂ)*w) =
      Complex.sinh ((Real.pi : ℂ)*w) := by
  by_cases hw : w = 0
  · simp [hw]
  · rw [laguerre_fredholm_determinant_sqrt w hw, div_mul_cancel₀]
    exact mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) hw

/-- Every zero has multiplicity one: the derivative is nonzero there. -/
theorem laguerre_fredholm_determinant_simple_zeros (z : ℂ)
    (hz : laguerreFredholmDeterminant z = 0) :
    deriv laguerreFredholmDeterminant z ≠ 0 := by
  intro hd0
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, laguerre_fredholm_determinant_zero] at hz
    exact one_ne_zero hz
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z (by norm_num : 0 < (2 : ℕ))
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw; exact hz0 hw.symm
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hD := (laguerre_fredholm_determinant_entire z).differentiableAt.hasDerivAt
  rw [hd0, ← hw] at hD
  have hL := (hD.comp w ((hasDerivAt_id w).pow 2)).mul
    ((hasDerivAt_id w).const_mul (Real.pi : ℂ))
  have hR := (Complex.hasDerivAt_sinh ((Real.pi : ℂ)*w)).comp w
    ((hasDerivAt_id w).const_mul (Real.pi : ℂ))
  have he : (fun w : ℂ => laguerreFredholmDeterminant (w^2) * ((Real.pi : ℂ)*w)) =
      (fun w : ℂ => Complex.sinh ((Real.pi : ℂ)*w)) :=
    funext laguerre_fredholm_determinant_sinh
  change HasDerivAt (fun w : ℂ => laguerreFredholmDeterminant (w^2) * ((Real.pi : ℂ)*w))
    _ w at hL
  rw [he] at hL
  have hd := hL.unique hR
  simp only [Function.comp_apply, id_eq, zero_mul, hw, hz, zero_add, mul_one] at hd
  have hc : Complex.cosh ((Real.pi : ℂ)*w) = 0 :=
    (mul_eq_zero.mp hd.symm).resolve_right hp
  have hs : Complex.sinh ((Real.pi : ℂ)*w) = 0 := by
    rw [← laguerre_fredholm_determinant_sinh, hw, hz, zero_mul]
  have hh := Complex.cosh_sq_sub_sinh_sq ((Real.pi : ℂ)*w)
  simp [hc, hs] at hh

end
end Sigma



