import SigmaOpDeterminantFredholm
import SigmaProbEulerProduct
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

namespace Sigma
noncomputable section
open Filter
open scoped Topology BigOperators

/-- Finite-dimensional Hilbert--Schmidt regularization, applied to actual compressed resolvents. -/
def laguerreRegularizedApprox (z : ℂ) (N : ℕ) : ℂ :=
  let M := hilbertCompressionMatrix laguerreHilbertBasis
    (laguerreResolvent 1 (by norm_num)) N
  (1 + z • M).det * Complex.exp (-z * M.trace)

theorem laguerre_regularized_approx_product (z : ℂ) (N : ℕ) :
    laguerreRegularizedApprox z N = ∏ n ∈ Finset.range N,
      ((1 + z / ((n : ℂ)+1)) * Complex.exp (-z / ((n : ℂ)+1))) := by
  classical
  unfold laguerreRegularizedApprox
  rw [hilbert_compression_matrix_diagonal _ _ _
    (laguerre_resolvent_basis_action 1 (by norm_num))]
  dsimp only
  have hm : (1 + z • Matrix.diagonal (fun i : Fin N =>
      (((i : ℕ) : ℂ) + ((1 : ℝ) : ℂ))⁻¹)) =
      Matrix.diagonal (fun i : Fin N => 1 + z / (((i : ℕ) : ℂ) + 1)) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [Matrix.diagonal_apply, div_eq_mul_inv]
    · simp [Matrix.diagonal_apply, h]
  rw [hm, Matrix.det_diagonal, Matrix.trace_diagonal]
  simp only [Complex.ofReal_one]
  rw [Fin.prod_univ_eq_prod_range (fun n : ℕ => 1 + z / ((n : ℂ)+1)) N,
    Fin.sum_univ_eq_sum_range (fun n : ℕ => ((n : ℂ)+1)⁻¹) N,
    Finset.mul_sum, Complex.exp_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro n hn
  simp only [div_eq_mul_inv]

/-- The regularized determinant is defined by the finite-dimensional regularizations. -/
def laguerreRegularizedDeterminant (z : ℂ) : ℂ :=
  limUnder atTop (laguerreRegularizedApprox z)

theorem laguerre_regularized_approx_real (x : ℝ) (hx : -1 < x) (N : ℕ) :
    laguerreRegularizedApprox (x : ℂ) N =
      (Real.exp (-∑ n ∈ Finset.range N, eulerLogGammaTerm (-x) n) : ℂ) := by
  rw [laguerre_regularized_approx_product, ← Finset.sum_neg_distrib, Real.exp_sum]
  rw [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro n hn
  have hp : 0 < 1 + x / ((n : ℝ)+1) := by
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hd : 0 < (n : ℝ)+1 := by positivity
    have hh : -(1 : ℝ) < x / ((n : ℝ)+1) := (lt_div_iff₀ hd).mpr (by nlinarith)
    linarith
  have he : -eulerLogGammaTerm (-x) n =
      Real.log (1+x/((n : ℝ)+1))-x/((n : ℝ)+1) := by
    unfold eulerLogGammaTerm
    simp only [neg_div, sub_neg_eq_add]
    ring
  rw [he, Real.exp_sub, Real.exp_log hp]
  push_cast
  rw [neg_div, Complex.exp_neg]
  ring

theorem laguerre_regularized_approx_tendsto_real (x : ℝ) (hx : -1 < x) :
    Tendsto (laguerreRegularizedApprox (x : ℂ)) atTop
      (𝓝 ((Real.exp (-Real.eulerMascheroniConstant*x) / Real.Gamma (1+x) : ℝ) : ℂ)) := by
  have hs := (log_gamma_euler_product (-x) (by linarith)).tendsto_sum_nat
  have ht := Complex.continuous_ofReal.tendsto _ |>.comp
    (Real.continuous_exp.tendsto _ |>.comp hs.neg)
  have he : Real.exp (-(Real.log (Real.Gamma (1 - -x)) -
      Real.eulerMascheroniConstant * -x)) =
      Real.exp (-Real.eulerMascheroniConstant*x) / Real.Gamma (1+x) := by
    have hp : 0 < Real.Gamma (1+x) := Real.Gamma_pos_of_pos (by linarith)
    rw [show 1 - -x = 1+x by ring]
    rw [show -(Real.log (Real.Gamma (1+x)) - Real.eulerMascheroniConstant * -x) =
      -Real.eulerMascheroniConstant*x - Real.log (Real.Gamma (1+x)) by ring]
    rw [Real.exp_sub, Real.exp_log hp]
  rw [he] at ht
  convert ht using 1
  funext N
  exact laguerre_regularized_approx_real x hx N

/-- The Gamma normalization follows from the proved Euler log-Gamma expansion. -/
theorem laguerre_regularized_determinant_real (x : ℝ) (hx : -1 < x) :
    laguerreRegularizedDeterminant (x : ℂ) =
      ((Real.exp (-Real.eulerMascheroniConstant*x) / Real.Gamma (1+x) : ℝ) : ℂ) :=
  (laguerre_regularized_approx_tendsto_real x hx).limUnder_eq

theorem laguerre_regularized_determinant_zero : laguerreRegularizedDeterminant 0 = 1 := by
  simpa using laguerre_regularized_determinant_real 0 (by norm_num)

theorem laguerre_regularized_approx_gamma_factor (z : ℂ) (N : ℕ) :
    laguerreRegularizedApprox z N =
      ((∏ n ∈ Finset.range N, (1+z+(n : ℂ))) / (N.factorial : ℂ)) *
        Complex.exp (-z * (harmonic N : ℂ)) := by
  rw [laguerre_regularized_approx_product, Finset.prod_mul_distrib]
  have he (n : ℕ) : 1 + z / ((n : ℂ)+1) = (1+z+(n : ℂ))/((n : ℂ)+1) := by
    have hn : (n : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp
    ring
  simp_rw [he, neg_div, div_eq_mul_inv]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have hf : (∏ n ∈ Finset.range N, ((n : ℂ)+1)) = (N.factorial : ℂ) := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial N
  rw [hf]
  congr 1
  rw [← Complex.exp_sum]
  simp_rw [← neg_mul]
  rw [← Finset.mul_sum]
  congr 2
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Nat.cast_add,
    Nat.cast_one]
  push_cast
  rfl

theorem complex_gamma_sequence_inv_tendsto (s : ℂ) :
    Tendsto (fun n : ℕ => (Complex.GammaSeq s n)⁻¹) atTop (𝓝 (Complex.Gamma s)⁻¹) := by
  by_cases h : Complex.Gamma s = 0
  · obtain ⟨k, hk⟩ := (Complex.Gamma_eq_zero_iff s).mp h
    rw [h, inv_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    symm
    simp only [Complex.GammaSeq]
    have hp : (∏ j ∈ Finset.range (n+1), (s+(j : ℂ))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : k < n+1))
      simp [hk]
    rw [hp, div_zero, inv_zero]
  · exact (Complex.GammaSeq_tendsto_Gamma s).inv₀ h

theorem laguerre_regularized_approx_gamma_sequence (z : ℂ) (N : ℕ) (hN : N ≠ 0) :
    laguerreRegularizedApprox z (N+1) =
      ((N : ℂ)/((N : ℂ)+1)) *
        Complex.exp (z * ((Real.log N : ℝ) - (harmonic (N+1) : ℝ))) *
          (Complex.GammaSeq (1+z) N)⁻¹ := by
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hn1 : (N : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  have hnf : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  have hpow : (N : ℂ) ^ (1+z) ≠ 0 := by rw [Complex.cpow_def_of_ne_zero hn]; exact Complex.exp_ne_zero _
  rw [laguerre_regularized_approx_gamma_factor, Complex.GammaSeq, inv_div,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hexp : Complex.exp (z * ((Real.log N : ℝ) - (harmonic (N+1) : ℝ))) =
      ((N : ℂ) ^ (1+z) / (N : ℂ)) * Complex.exp (-z * (harmonic (N+1) : ℂ)) := by
    rw [Complex.cpow_add _ _ hn, Complex.cpow_one, mul_div_cancel_left₀ _ hn,
      Complex.cpow_def_of_ne_zero hn, ← Complex.exp_add]
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg N)]
    push_cast
    congr 1
    ring
  rw [hexp]
  field_simp
  ring

theorem laguerre_regularized_approx_tendsto (z : ℂ) :
    Tendsto (laguerreRegularizedApprox z) atTop
      (𝓝 (Complex.exp (-(Real.eulerMascheroniConstant : ℂ)*z) / Complex.Gamma (1+z))) := by
  have hh := Complex.continuous_ofReal.tendsto _ |>.comp harmonic_log_slope_tendsto
  have he := Complex.continuous_exp.tendsto _ |>.comp (hh.const_mul z)
  have ht := ((tendsto_natCast_div_add_atTop (1 : ℂ)).mul he).mul
    (complex_gamma_sequence_inv_tendsto (1+z))
  have heq : Complex.exp (z * ((-Real.eulerMascheroniConstant : ℝ) : ℂ)) *
      (Complex.Gamma (1+z))⁻¹ =
      Complex.exp (-(Real.eulerMascheroniConstant : ℂ)*z) / Complex.Gamma (1+z) := by
    push_cast
    rw [mul_comm z, div_eq_mul_inv]
  simp only [one_mul, heq] at ht
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with N hN
  simpa only [Function.comp_apply, Complex.ofReal_sub] using
    (laguerre_regularized_approx_gamma_sequence z N hN).symm

/-- The complex Gamma formula, including its zeros at the Gamma poles. -/
theorem laguerre_regularized_determinant_gamma (z : ℂ) :
    laguerreRegularizedDeterminant z =
      Complex.exp (-(Real.eulerMascheroniConstant : ℂ)*z) / Complex.Gamma (1+z) :=
  (laguerre_regularized_approx_tendsto z).limUnder_eq

theorem laguerre_regularized_determinant_entire (z : ℂ) :
    AnalyticAt ℂ laguerreRegularizedDeterminant z := by
  have he : laguerreRegularizedDeterminant = fun z : ℂ =>
      Complex.exp (-(Real.eulerMascheroniConstant : ℂ)*z) * (Complex.Gamma (1+z))⁻¹ := by
    funext x
    rw [laguerre_regularized_determinant_gamma, div_eq_mul_inv]
  rw [he]
  apply Differentiable.analyticAt
  exact (Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id)).mul
    (Complex.differentiable_one_div_Gamma.comp ((differentiable_const _).add differentiable_id))

theorem laguerre_regularized_determinant_zeros (z : ℂ) :
    laguerreRegularizedDeterminant z = 0 ↔ ∃ n : ℕ, z = -((n : ℂ)+1) := by
  rw [laguerre_regularized_determinant_gamma, div_eq_zero_iff,
    or_iff_right (Complex.exp_ne_zero _), Complex.Gamma_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    linear_combination hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]
    ring

theorem complex_reciprocal_gamma_deriv_recurrence (s : ℂ) :
    deriv (fun x : ℂ => (Complex.Gamma x)⁻¹) s = (Complex.Gamma (s+1))⁻¹ +
      s * deriv (fun x : ℂ => (Complex.Gamma x)⁻¹) (s+1) := by
  have hg := ((Complex.differentiable_one_div_Gamma (s+1)).hasDerivAt).comp s
    ((hasDerivAt_id s).add_const 1)
  have hf := (hasDerivAt_id s).mul hg
  have he : (fun x : ℂ => x * (Complex.Gamma (x+1))⁻¹) =
      (fun x : ℂ => (Complex.Gamma x)⁻¹) :=
    funext (fun x => (Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one x).symm)
  change HasDerivAt (fun x : ℂ => x * (Complex.Gamma (x+1))⁻¹) _ s at hf
  rw [he] at hf
  simpa only [one_mul, mul_one] using hf.deriv

theorem complex_reciprocal_gamma_simple_zeros (n : ℕ) :
    deriv (fun x : ℂ => (Complex.Gamma x)⁻¹) (-(n : ℂ)) ≠ 0 := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, neg_zero, complex_reciprocal_gamma_deriv_recurrence]
    simp [Complex.Gamma_one]
  | succ n ih =>
    rw [complex_reciprocal_gamma_deriv_recurrence]
    have he : (-(↑(n+1) : ℂ))+1 = -(n : ℂ) := by push_cast; ring
    rw [show (-(↑(n+1) : ℂ))+1 = -(n : ℂ) from he,
      Complex.Gamma_neg_nat_eq_zero, inv_zero, zero_add]
    apply mul_ne_zero _ ih
    exact neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero n)

theorem laguerre_regularized_determinant_simple_zeros (z : ℂ)
    (hz : laguerreRegularizedDeterminant z = 0) :
    deriv laguerreRegularizedDeterminant z ≠ 0 := by
  obtain ⟨n, hn⟩ := (laguerre_regularized_determinant_zeros z).mp hz
  have hs : 1+z = -(n : ℂ) := by rw [hn]; ring
  have he := (Complex.hasDerivAt_exp (-(Real.eulerMascheroniConstant : ℂ)*z)).comp z
    ((hasDerivAt_id z).const_mul (-(Real.eulerMascheroniConstant : ℂ)))
  have hg := ((Complex.differentiable_one_div_Gamma (1+z)).hasDerivAt).comp z
    ((hasDerivAt_id z).const_add 1)
  have hd := he.mul hg
  have hfun : (fun z : ℂ => Complex.exp (-(Real.eulerMascheroniConstant : ℂ)*z) *
      (Complex.Gamma (1+z))⁻¹) = laguerreRegularizedDeterminant := by
    funext x
    rw [laguerre_regularized_determinant_gamma, div_eq_mul_inv]
  change HasDerivAt (fun z : ℂ => Complex.exp (-(Real.eulerMascheroniConstant : ℂ)*z) *
      (Complex.Gamma (1+z))⁻¹) _ z at hd
  rw [hfun] at hd
  rw [hd.deriv]
  simp only [Function.comp_apply, id_eq, hs, Complex.Gamma_neg_nat_eq_zero, inv_zero,
    mul_zero, zero_add, mul_one]
  exact mul_ne_zero (Complex.exp_ne_zero _) (complex_reciprocal_gamma_simple_zeros n)

end
end Sigma



