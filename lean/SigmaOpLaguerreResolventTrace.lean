import SigmaOpLaguerreResolvent
import SigmaOpDiagonalNuclear
import SigmaOpSpectral

namespace Sigma
noncomputable section

/-- An operator is Hilbert--Schmidt when its squared basis-image norms sum
in an orthonormal basis. -/
def IsHilbertSchmidtOperator {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (T : H →L[ℂ] H) : Prop :=
  ∃ b : HilbertBasis ℕ ℂ H, Summable (fun n => ‖T (b n)‖ ^ 2)

/-- The actual first resolvent is diagonal in the Laguerre Hilbert basis. -/
theorem laguerre_resolvent_basis_action (α : ℝ) (hα : 0 < α) (n : ℕ) :
    laguerreResolvent α hα (laguerreHilbertBasis n) =
      ((n : ℂ) + (α : ℂ))⁻¹ • laguerreHilbertBasis n := by
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext k
  rw [laguerre_resolvent_coordinate, map_smul, laguerreHilbertBasis.repr_self]
  change ((k : ℂ) + (α : ℂ))⁻¹ * markedIntegerEigenvector n k =
    ((n : ℂ) + (α : ℂ))⁻¹ * markedIntegerEigenvector n k
  by_cases h : k = n
  · subst k
    rfl
  · simp [markedIntegerEigenvector, lp.single_apply_ne, h]

theorem laguerre_resolvent_not_nuclear (α : ℝ) (hα : 0 < α) :
    ¬ IsNuclearOperator (laguerreResolvent α hα) := by
  intro hn
  have hs := (diagonal_operator_nuclear_iff laguerreHilbertBasis
    (laguerreResolvent α hα) (fun n : ℕ => ((n : ℂ) + (α : ℂ))⁻¹)
    (laguerre_resolvent_basis_action α hα)).mp hn
  have hs' : Summable (fun n : ℕ => 1 / ((n : ℝ) + α)) := by
    convert hs using 1
    funext n
    rw [norm_inv, ← Complex.ofReal_natCast n, ← Complex.ofReal_add, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (n : ℝ) + α)]
    ring
  exact operator_first_resolvent_eigenvalues_not_summable α hα hs'

theorem laguerre_resolvent_hilbert_schmidt (α : ℝ) (hα : 0 < α) :
    IsHilbertSchmidtOperator (laguerreResolvent α hα) := by
  refine ⟨laguerreHilbertBasis, ?_⟩
  convert operator_squared_resolvent_eigenvalues_summable α hα using 1
  funext n
  rw [laguerre_resolvent_basis_action, norm_smul,
    laguerreHilbertBasis.orthonormal.1 n, mul_one, norm_inv,
    ← Complex.ofReal_natCast n, ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (n : ℝ) + α)]
  simp only [one_div, inv_pow]

/-- The square of the actual first resolvent, on the weighted Hilbert space. -/
def laguerreSquaredResolvent (α : ℝ) (hα : 0 < α) :
    LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert :=
  (laguerreResolvent α hα).comp (laguerreResolvent α hα)

theorem laguerre_squared_resolvent_basis_action (α : ℝ) (hα : 0 < α) (n : ℕ) :
    laguerreSquaredResolvent α hα (laguerreHilbertBasis n) =
      (((n : ℂ) + (α : ℂ))⁻¹ ^ 2) • laguerreHilbertBasis n := by
  simp only [laguerreSquaredResolvent, ContinuousLinearMap.comp_apply,
    laguerre_resolvent_basis_action, map_smul, smul_smul, pow_two]

theorem laguerre_squared_resolvent_nuclear (α : ℝ) (hα : 0 < α) :
    IsNuclearOperator (laguerreSquaredResolvent α hα) := by
  apply (diagonal_operator_nuclear_iff laguerreHilbertBasis
    (laguerreSquaredResolvent α hα)
    (fun n : ℕ => ((n : ℂ) + (α : ℂ))⁻¹ ^ 2)
    (laguerre_squared_resolvent_basis_action α hα)).mpr
  convert operator_squared_resolvent_eigenvalues_summable α hα using 1
  funext n
  rw [norm_pow, norm_inv, ← Complex.ofReal_natCast n, ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (n : ℝ) + α)]
  simp only [one_div, inv_pow]

theorem laguerre_squared_resolvent_trace (α : ℝ) (hα : 0 < α) :
    nuclearTrace (laguerreSquaredResolvent α hα)
      (laguerre_squared_resolvent_nuclear α hα) =
      ∑' n : ℕ, (1 / ((n : ℂ) + (α : ℂ))) ^ 2 := by
  simpa only [one_div] using diagonal_operator_nuclear_trace laguerreHilbertBasis
    (laguerreSquaredResolvent α hα)
    (fun n : ℕ => ((n : ℂ) + (α : ℂ))⁻¹ ^ 2)
    (laguerre_squared_resolvent_basis_action α hα)
    (laguerre_squared_resolvent_nuclear α hα)

private theorem resolvent_difference_abs_summable (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) :
    Summable (fun n : ℕ => |((n : ℝ) + α)⁻¹ - ((n : ℝ) + β)⁻¹|) := by
  have hm : 0 < min α β := lt_min hα hβ
  have hs := (operator_squared_resolvent_eigenvalues_summable (min α β) hm).mul_left
    |β - α|
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ hs
  intro n
  have ha : 0 < (n : ℝ) + α := by positivity
  have hb : 0 < (n : ℝ) + β := by positivity
  have hc : 0 < (n : ℝ) + min α β := by positivity
  have hden : ((n : ℝ) + min α β) ^ 2 ≤
      ((n : ℝ) + α) * ((n : ℝ) + β) := by
    have hma : min α β ≤ α := min_le_left _ _
    have hmb : min α β ≤ β := min_le_right _ _
    nlinarith [mul_nonneg (show 0 ≤ ((n : ℝ) + α) - ((n : ℝ) + min α β) by linarith)
      (show 0 ≤ ((n : ℝ) + β) - ((n : ℝ) + min α β) by linarith)]
  have hinv : 1 / (((n : ℝ) + α) * ((n : ℝ) + β)) ≤
      1 / (((n : ℝ) + min α β) ^ 2) :=
    one_div_le_one_div_of_le (by positivity) hden
  have hdiff : ((n : ℝ) + α)⁻¹ - ((n : ℝ) + β)⁻¹ =
      (β - α) / (((n : ℝ) + α) * ((n : ℝ) + β)) := by
    field_simp [ha.ne', hb.ne']
  rw [hdiff, abs_div, abs_of_pos (mul_pos ha hb), div_eq_mul_inv]
  simpa only [one_div] using mul_le_mul_of_nonneg_left hinv (abs_nonneg _)

theorem laguerre_resolvent_difference_basis_action (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    (laguerreResolvent α hα - laguerreResolvent β hβ) (laguerreHilbertBasis n) =
      (((((n : ℝ) + α)⁻¹ - ((n : ℝ) + β)⁻¹) : ℝ) : ℂ) •
        laguerreHilbertBasis n := by
    rw [ContinuousLinearMap.sub_apply, laguerre_resolvent_basis_action,
      laguerre_resolvent_basis_action, ← sub_smul]
    congr 1
    push_cast
    ring

theorem laguerre_resolvent_difference_nuclear (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) :
    IsNuclearOperator (laguerreResolvent α hα - laguerreResolvent β hβ) := by
  apply (diagonal_operator_nuclear_iff laguerreHilbertBasis _ _
    (laguerre_resolvent_difference_basis_action α β hα hβ)).mpr
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    resolvent_difference_abs_summable α β hα hβ

theorem laguerre_resolvent_difference_trace (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) :
    nuclearTrace (laguerreResolvent α hα - laguerreResolvent β hβ)
      (laguerre_resolvent_difference_nuclear α β hα hβ) =
      ∑' n : ℕ, (((((n : ℝ) + α)⁻¹ - ((n : ℝ) + β)⁻¹) : ℝ) : ℂ) := by
  exact diagonal_operator_nuclear_trace laguerreHilbertBasis _ _
    (laguerre_resolvent_difference_basis_action α β hα hβ)
    (laguerre_resolvent_difference_nuclear α β hα hβ)

end
end Sigma
