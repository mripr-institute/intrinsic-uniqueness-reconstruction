import SigmaRealTreesBorel

namespace Sigma
noncomputable section
open PowerSeries
open scoped BigOperators

theorem tree_coefficient_X_mul (F : PowerSeries ℝ) (n : ℕ) :
    coeff ℝ (n + 1) (X * F) = coeff ℝ n F := by
  simp [Nat.add_comm]

theorem tree_coeff_mul_nonnegative (F G : PowerSeries ℝ)
    (hF : ∀ n, 0 ≤ coeff ℝ n F) (hG : ∀ n, 0 ≤ coeff ℝ n G) :
    ∀ n, 0 ≤ coeff ℝ n (F * G) := by
  intro n
  rw [coeff_mul]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hF p.1) (hG p.2)

theorem tree_coeff_pow_nonnegative (F : PowerSeries ℝ) (hF : ∀ n, 0 ≤ coeff ℝ n F)
    (k : ℕ) : ∀ n, 0 ≤ coeff ℝ n (F ^ k) := by
  induction k with
  | zero => intro n; simp only [pow_zero, coeff_one]; split_ifs <;> norm_num
  | succ k ih => rw [pow_succ]; exact tree_coeff_mul_nonnegative _ _ ih hF

theorem tree_exp_partial_nonnegative (F : PowerSeries ℝ)
    (hF : ∀ n, 0 ≤ coeff ℝ n F) (m : ℕ) :
    ∀ n, 0 ≤ coeff ℝ n (treeExpPartial ℝ F m) := by
  intro n
  simp only [treeExpPartial, map_sum, coeff_C_mul]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (by positivity)
    (tree_coeff_pow_nonnegative F hF j n)

/-- Finite polynomial iteration; no random-tree interpretation is assumed. -/
def borelPolynomialApprox (N : ℕ) : ℕ → Polynomial ℝ
  | 0 => 0
  | m + 1 => Polynomial.C (Real.exp (-1)) * Polynomial.X *
      ∑ j ∈ Finset.range (N + 1), Polynomial.C ((j.factorial : ℝ)⁻¹) *
        borelPolynomialApprox N m ^ j

theorem borel_polynomial_approx_coe (N m : ℕ) :
    (borelPolynomialApprox N (m + 1) : PowerSeries ℝ) =
      C ℝ (Real.exp (-1)) * X *
        treeExpPartial ℝ (borelPolynomialApprox N m : PowerSeries ℝ) (N + 1) := by
  simp only [borelPolynomialApprox, Polynomial.coe_mul, Polynomial.coe_C,
    Polynomial.coe_X, treeExpPartial]
  congr 1
  change Polynomial.coeToPowerSeries.ringHom
    (∑ j ∈ Finset.range (N + 1), Polynomial.C ((j.factorial : ℝ)⁻¹) *
      borelPolynomialApprox N m ^ j) = _
  rw [map_sum]
  simp

theorem borel_polynomial_approx_nonnegative (N m : ℕ) :
    ∀ n, 0 ≤ coeff ℝ n (borelPolynomialApprox N m : PowerSeries ℝ) := by
  induction m with
  | zero => intro n; simp [borelPolynomialApprox]
  | succ m ih =>
    rw [borel_polynomial_approx_coe]
    apply tree_coeff_mul_nonnegative
    · intro n
      simp only [coeff_C_mul, coeff_X]
      split_ifs <;> positivity
    · exact tree_exp_partial_nonnegative _ ih _

theorem borel_polynomial_approx_constant (N m : ℕ) :
    constantCoeff ℝ (borelPolynomialApprox N m : PowerSeries ℝ) = 0 := by
  cases m with
  | zero => simp [borelPolynomialApprox]
  | succ m => rw [borel_polynomial_approx_coe]; simp

theorem borel_polynomial_approx_coefficients (N m n : ℕ) (hnm : n ≤ m) (hnN : n ≤ N) :
    coeff ℝ n (borelPolynomialApprox N m : PowerSeries ℝ) = borelCoefficient n := by
  induction m generalizing n with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    simp [borelPolynomialApprox, borel_coefficient_zero]
  | succ m ih =>
    cases n with
    | zero => simpa only [coeff_zero_eq_constantCoeff_apply, borel_coefficient_zero] using
        borel_polynomial_approx_constant N (m + 1)
    | succ n =>
      rw [borel_polynomial_approx_coe]
      have hc : coeff ℝ (n + 1) borelSeries =
          Real.exp (-1) * coeff ℝ n (treeExp ℝ borelSeries) := by
        have h := congrArg (coeff ℝ (n + 1)) borel_series_fixed_point
        simpa only [mul_assoc, coeff_C_mul, tree_coefficient_X_mul] using h
      change _ = coeff ℝ (n + 1) borelSeries
      rw [hc, mul_assoc, coeff_C_mul]
      simp only [tree_coefficient_X_mul]
      rw [tree_exp_partial_coeff ℝ _ (borel_polynomial_approx_constant N m) n (N + 1) (by omega)]
      congr 1
      apply tree_exp_coeff_congr ℝ
      intro j hj
      exact ih j (by omega) (by omega)

theorem borel_polynomial_approx_value (N m : ℕ) :
    0 ≤ (borelPolynomialApprox N m).eval 1 ∧ (borelPolynomialApprox N m).eval 1 ≤ 1 := by
  induction m with
  | zero => simp [borelPolynomialApprox]
  | succ m ih =>
    have hv : (borelPolynomialApprox N (m + 1)).eval 1 =
        Real.exp (-1) * ∑ j ∈ Finset.range (N + 1),
          (borelPolynomialApprox N m).eval 1 ^ j / (j.factorial : ℝ) := by
      simp only [borelPolynomialApprox, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, mul_one, Polynomial.eval_finset_sum, Polynomial.eval_pow]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      simp only [div_eq_mul_inv, mul_comm]
    rw [hv]
    constructor
    · exact mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun j _ =>
        div_nonneg (pow_nonneg ih.1 _) (by positivity))
    · calc
        _ ≤ Real.exp (-1) * Real.exp ((borelPolynomialApprox N m).eval 1) :=
          mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg ih.1 (N + 1)) (Real.exp_pos _).le
        _ ≤ Real.exp (-1) * Real.exp 1 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ih.2) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; norm_num

theorem nonnegative_polynomial_partial_mass (P : Polynomial ℝ)
    (hP : ∀ n, 0 ≤ P.coeff n) (N : ℕ) :
    ∑ n ∈ Finset.range N, P.coeff n ≤ P.eval 1 := by
  have hdeg : P.natDegree < N + P.natDegree + 1 := by omega
  rw [Polynomial.eval_eq_sum_range' hdeg]
  simp only [one_pow, mul_one]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun n _ _ => hP n)

theorem borel_coefficient_partial_mass (N : ℕ) :
    ∑ n ∈ Finset.range N, borelCoefficient n ≤ 1 := by
  have he : (∑ n ∈ Finset.range N, borelCoefficient n) =
      ∑ n ∈ Finset.range N, (borelPolynomialApprox N N).coeff n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnn : n ≤ N := (Finset.mem_range.mp hn).le
    simpa using (borel_polynomial_approx_coefficients N N n hnn hnn).symm
  rw [he]
  exact (nonnegative_polynomial_partial_mass _
    (fun n => by simpa using borel_polynomial_approx_nonnegative N N n) N).trans
      (borel_polynomial_approx_value N N).2

theorem borel_coefficients_summable : Summable borelCoefficient :=
  summable_of_sum_range_le borel_coefficient_nonnegative borel_coefficient_partial_mass

theorem borel_total_mass_le_one : (∑' n, borelCoefficient n) ≤ 1 :=
  Real.tsum_le_of_sum_range_le borel_coefficient_nonnegative borel_coefficient_partial_mass

end
end Sigma
