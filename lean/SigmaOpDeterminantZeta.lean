import SigmaOpLaguerreResolventTrace
import SigmaOpZetaTrace
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace Sigma
noncomputable section
open Filter
open scoped Topology BigOperators

/-- Number of initial terms removed from the circle-normalized Hurwitz continuation. -/
def laguerreHurwitzShift (a : ℝ) : ℕ := ⌈a⌉₊ - 1

/-- Representative of a positive shift in the interval `(0,1]`. -/
def laguerreHurwitzBase (a : ℝ) : ℝ := a - (laguerreHurwitzShift a : ℝ)

theorem laguerre_hurwitz_shift_parameters (a : ℝ) (ha : 0 < a) :
    0 < laguerreHurwitzBase a ∧ laguerreHurwitzBase a ≤ 1 ∧
      laguerreHurwitzBase a + (laguerreHurwitzShift a : ℝ) = a := by
  let k := laguerreHurwitzShift a
  have hc : 0 < ⌈a⌉₊ := Nat.ceil_pos.mpr ha
  have hk : k+1 = ⌈a⌉₊ := by dsimp [k, laguerreHurwitzShift]; omega
  have hlt : (k : ℝ) < a := Nat.lt_ceil.mp (by omega : k < ⌈a⌉₊)
  have hle := Nat.le_ceil a
  have hkr : (k : ℝ)+1 = (⌈a⌉₊ : ℝ) := by exact_mod_cast hk
  change 0 < a-(k : ℝ) ∧ a-(k : ℝ) ≤ 1 ∧ a-(k : ℝ)+(k : ℝ) = a
  exact ⟨by linarith, by linarith, by ring⟩

/-- The meromorphic continuation of the native shifted spectral series. The finite
correction is necessary because Mathlib's Hurwitz parameter lives on `ℝ/ℤ`. -/
def laguerreHurwitzZeta (a : ℝ) (s : ℂ) : ℂ :=
  HurwitzZeta.hurwitzZeta (laguerreHurwitzBase a) s -
    ∑ n ∈ Finset.range (laguerreHurwitzShift a),
      1 / ((n : ℂ)+(laguerreHurwitzBase a : ℂ))^s

theorem laguerre_hurwitz_zeta_hasSum (a : ℝ) (ha : 0 < a) (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ)+(a : ℂ))^s) (laguerreHurwitzZeta a s) := by
  obtain ⟨hb, hb1, hba⟩ := laguerre_hurwitz_shift_parameters a ha
  have h := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ⟨hb.le, hb1⟩ hs
  have ht := (hasSum_nat_add_iff' (laguerreHurwitzShift a)).mpr h
  convert ht using 1
  funext n
  congr 2
  have he := congrArg (fun x : ℝ => (x : ℂ)) hba
  push_cast at he ⊢
  linear_combination -he

theorem laguerre_hurwitz_zeta_differentiableAt (a : ℝ) (ha : 0 < a) (s : ℂ)
    (hs : s ≠ 1) : DifferentiableAt ℂ (laguerreHurwitzZeta a) s := by
  have hb := (laguerre_hurwitz_shift_parameters a ha).1
  apply (HurwitzZeta.differentiableAt_hurwitzZeta _ hs).sub
  apply DifferentiableAt.sum
  intro n hn
  have hn0 : (n : ℂ)+(laguerreHurwitzBase a : ℂ) ≠ 0 := by
    have hp : 0 < (n : ℝ)+laguerreHurwitzBase a := by positivity
    exact_mod_cast hp.ne'
  exact (differentiableAt_const _).div (differentiableAt_id.const_cpow
    (Or.inl hn0)) (by rw [Complex.cpow_def_of_ne_zero hn0]; exact Complex.exp_ne_zero _)

theorem laguerre_hurwitz_zeta_regular_zero (a : ℝ) (ha : 0 < a) :
    DifferentiableAt ℂ (laguerreHurwitzZeta a) 0 :=
  laguerre_hurwitz_zeta_differentiableAt a ha 0 zero_ne_one

/-- Zeta regularization uses the derivative of the actual meromorphic continuation. -/
def laguerreZetaDeterminant (a : ℝ) : ℂ :=
  Complex.exp (-deriv (laguerreHurwitzZeta a) 0)

theorem laguerre_zeta_determinant_ne_zero (a : ℝ) : laguerreZetaDeterminant a ≠ 0 :=
  Complex.exp_ne_zero _

theorem laguerre_hurwitz_zeta_one (s : ℂ) : laguerreHurwitzZeta 1 s = riemannZeta s := by
  simp [laguerreHurwitzZeta, laguerreHurwitzBase, laguerreHurwitzShift,
    AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero]

theorem laguerre_zeta_determinant_one :
    laguerreZetaDeterminant 1 = Complex.exp (-deriv riemannZeta 0) := by
  unfold laguerreZetaDeterminant
  rw [show laguerreHurwitzZeta 1 = riemannZeta from funext laguerre_hurwitz_zeta_one]

theorem laguerre_hurwitz_zeta_deriv_zero (a : ℝ) (ha : 0 < a) :
    deriv (laguerreHurwitzZeta a) 0 =
      deriv (HurwitzZeta.hurwitzZeta (laguerreHurwitzBase a)) 0 +
        ∑ n ∈ Finset.range (laguerreHurwitzShift a),
          Complex.log ((n : ℂ)+(laguerreHurwitzBase a : ℂ)) := by
  have hb := (laguerre_hurwitz_shift_parameters a ha).1
  have hd (n : ℕ) : HasDerivAt
      (fun s : ℂ => 1 / ((n : ℂ)+(laguerreHurwitzBase a : ℂ))^s)
      (-Complex.log ((n : ℂ)+(laguerreHurwitzBase a : ℂ))) 0 := by
    have hn : (n : ℂ)+(laguerreHurwitzBase a : ℂ) ≠ 0 := by
      have hp : 0 < (n : ℝ)+laguerreHurwitzBase a := by positivity
      exact_mod_cast hp.ne'
    have h := (hasDerivAt_const (0 : ℂ) (1 : ℂ)).div
      ((hasDerivAt_id (0 : ℂ)).const_cpow (Or.inl hn)) (by simp)
    simpa using h
  have hsum := HasDerivAt.sum (u := Finset.range (laguerreHurwitzShift a))
    (fun n _ => hd n)
  have hh := (HurwitzZeta.differentiableAt_hurwitzZeta (laguerreHurwitzBase a)
    (s := (0 : ℂ)) zero_ne_one).hasDerivAt.sub hsum
  simpa only [laguerreHurwitzZeta, Finset.sum_neg_distrib, sub_neg_eq_add] using hh.deriv

theorem laguerre_zeta_determinant_shift_correction (a : ℝ) (ha : 0 < a) :
    laguerreZetaDeterminant a =
      Complex.exp (-deriv (HurwitzZeta.hurwitzZeta (laguerreHurwitzBase a)) 0) /
        ∏ n ∈ Finset.range (laguerreHurwitzShift a),
          ((n : ℂ)+(laguerreHurwitzBase a : ℂ)) := by
  rw [laguerreZetaDeterminant, laguerre_hurwitz_zeta_deriv_zero a ha,
    neg_add, Complex.exp_add]
  simp_rw [Complex.exp_neg]
  rw [Complex.exp_sum]
  have hb := (laguerre_hurwitz_shift_parameters a ha).1
  have hn (n : ℕ) : (n : ℂ)+(laguerreHurwitzBase a : ℂ) ≠ 0 := by
    have hp : 0 < (n : ℝ)+laguerreHurwitzBase a := by positivity
    exact_mod_cast hp.ne'
  simp only [Complex.exp_log (hn _), div_eq_mul_inv]

def laguerreShiftedZetaMultiplier (a : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  1 / ((n : ℂ)+(a : ℂ))^s

theorem laguerre_shifted_zeta_multiplier_norm (a : ℝ) (ha : 0 < a) (s : ℂ) (n : ℕ) :
    ‖laguerreShiftedZetaMultiplier a s n‖ = 1 / ((n : ℝ)+a)^s.re := by
  have hp : 0 < (n : ℝ)+a := by positivity
  rw [laguerreShiftedZetaMultiplier, norm_div, norm_one, Complex.norm_eq_abs]
  have he : (n : ℂ)+(a : ℂ) = (((n : ℝ)+a : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.abs_cpow_eq_rpow_re_of_pos hp]

theorem laguerre_shifted_zeta_multiplier_summable_iff (a : ℝ) (ha : 0 < a) (s : ℂ) :
    Summable (fun n => ‖laguerreShiftedZetaMultiplier a s n‖) ↔ 1 < s.re := by
  simp_rw [laguerre_shifted_zeta_multiplier_norm a ha]
  exact operator_shifted_real_eigenvalue_summable_iff a s.re ha

/-- The actual maximal spectral complex power `(A+a)^(-s)` on weighted L². -/
def laguerreShiftedZetaOperator (a : ℝ) (s : ℂ) :
    LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert :=
  integerBasisMultiplier laguerreHilbertBasis (laguerreShiftedZetaMultiplier a s)

private theorem shifted_zeta_multiplier_bound (a : ℝ) (ha : 0 < a) (s : ℂ)
    (hs : 1 < s.re) (n : ℕ) :
    ‖laguerreShiftedZetaMultiplier a s n‖ ≤ ∑' k, ‖laguerreShiftedZetaMultiplier a s k‖ :=
  le_tsum ((laguerre_shifted_zeta_multiplier_summable_iff a ha s).mpr hs) n
    (fun _ _ => norm_nonneg _)

def laguerreShiftedZetaBoundedOperator (a : ℝ) (ha : 0 < a) (s : ℂ) (hs : 1 < s.re) :
    LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert :=
  integerBasisBoundedMultiplier laguerreHilbertBasis (laguerreShiftedZetaMultiplier a s)
    (∑' k, ‖laguerreShiftedZetaMultiplier a s k‖) (tsum_nonneg (fun _ => norm_nonneg _))
    (shifted_zeta_multiplier_bound a ha s hs)

theorem laguerre_shifted_zeta_bounded_basis_action (a : ℝ) (ha : 0 < a) (s : ℂ)
    (hs : 1 < s.re) (n : ℕ) :
    laguerreShiftedZetaBoundedOperator a ha s hs (laguerreHilbertBasis n) =
      laguerreShiftedZetaMultiplier a s n • laguerreHilbertBasis n :=
  integer_basis_bounded_multiplier_basis_action _ _ _ _ _ _

theorem laguerre_shifted_zeta_bounded_nuclear (a : ℝ) (ha : 0 < a) (s : ℂ)
    (hs : 1 < s.re) : IsNuclearOperator (laguerreShiftedZetaBoundedOperator a ha s hs) :=
  diagonal_operator_nuclear_of_summable laguerreHilbertBasis _ _
    (laguerre_shifted_zeta_bounded_basis_action a ha s hs)
    ((laguerre_shifted_zeta_multiplier_summable_iff a ha s).mpr hs)

theorem laguerre_shifted_zeta_bounded_eq (a : ℝ) (ha : 0 < a) (s : ℂ) (hs : 1 < s.re) :
    laguerreShiftedZetaOperator a s =
      (laguerreShiftedZetaBoundedOperator a ha s hs).toLinearMap.toPMap ⊤ :=
  integer_basis_bounded_multiplier_eq _ _ _ _ _

/-- The continued function agrees with the genuine nuclear trace on its convergence half-plane. -/
theorem laguerre_shifted_zeta_trace (a : ℝ) (ha : 0 < a) (s : ℂ) (hs : 1 < s.re) :
    nuclearTrace (laguerreShiftedZetaBoundedOperator a ha s hs)
      (laguerre_shifted_zeta_bounded_nuclear a ha s hs) = laguerreHurwitzZeta a s := by
  rw [diagonal_operator_nuclear_trace laguerreHilbertBasis _ _
    (laguerre_shifted_zeta_bounded_basis_action a ha s hs)]
  exact (laguerre_hurwitz_zeta_hasSum a ha s hs).tsum_eq

end
end Sigma

