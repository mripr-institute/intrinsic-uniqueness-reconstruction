import SigmaOpLaguerreSpectral

namespace Sigma
noncomputable section
open Set Filter
open scoped ENNReal NNReal Topology

theorem marked_l2_square_summable (x : MarkedIntegerHilbert) : Summable (fun n => ‖x n‖^2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    x.property.summable (by norm_num : 0 < (2:ℝ≥0∞).toReal)

theorem marked_l2_norm_square (x : MarkedIntegerHilbert) :
    ‖x‖^2 = ∑' n, ‖x n‖^2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) x

theorem marked_bounded_multiplier_mem (b : ℕ → ℝ) (C : ℝ)
    (hb : ∀ n, |b n| ≤ C) (x : MarkedIntegerHilbert) :
    Memℓp (fun n => (b n:ℂ) * x n) 2 := by
  have hbound (n : ℕ) : ‖(b n:ℂ)*x n‖^2 ≤ C^2*‖x n‖^2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact hb n
  have hs := Summable.of_nonneg_of_le (fun n => sq_nonneg ‖(b n:ℂ)*x n‖)
    hbound ((marked_l2_square_summable x).mul_left (C^2))
  apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs

def markedBoundedDiagonalLinear (b : ℕ → ℝ) (C : ℝ) (hb : ∀ n, |b n| ≤ C) :
    MarkedIntegerHilbert →ₗ[ℂ] MarkedIntegerHilbert where
  toFun x := ⟨fun n => (b n:ℂ)*x n, marked_bounded_multiplier_mem b C hb x⟩
  map_add' x y := by
    apply lp.ext
    funext n
    change (b n:ℂ)*(x n+y n) = (b n:ℂ)*x n+(b n:ℂ)*y n
    ring
  map_smul' c x := by
    apply lp.ext
    funext n
    change (b n:ℂ)*(c*x n) = c*((b n:ℂ)*x n)
    ring

theorem marked_bounded_diagonal_norm (b : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n, |b n| ≤ C) (x : MarkedIntegerHilbert) :
    ‖markedBoundedDiagonalLinear b C hb x‖ ≤ C*‖x‖ := by
  have hh : ‖markedBoundedDiagonalLinear b C hb x‖^2 ≤ (C*‖x‖)^2 := by
    rw [marked_l2_norm_square, mul_pow, marked_l2_norm_square, ← tsum_mul_left]
    apply tsum_le_tsum _
      (marked_l2_square_summable (markedBoundedDiagonalLinear b C hb x))
      ((marked_l2_square_summable x).mul_left (C^2))
    intro n
    change ‖(b n:ℂ)*x n‖^2 ≤ C^2*‖x n‖^2
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact hb n
  nlinarith [norm_nonneg (markedBoundedDiagonalLinear b C hb x),
    mul_nonneg hC (norm_nonneg x)]

def markedBoundedDiagonal (b : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, |b n| ≤ C) :
    MarkedIntegerHilbert →L[ℂ] MarkedIntegerHilbert :=
  (markedBoundedDiagonalLinear b C hb).mkContinuous C (marked_bounded_diagonal_norm b C hC hb)

/-- A genuine bounded operator on the original weighted complex L² space. -/
def laguerreBoundedDiagonal (b : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, |b n| ≤ C) :
    LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert :=
  laguerreHilbertBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((markedBoundedDiagonal b C hC hb).comp
      laguerreHilbertBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem laguerre_bounded_diagonal_coordinate (b : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n, |b n| ≤ C) (x : LaguerreWeightedHilbert) (n : ℕ) :
    laguerreHilbertBasis.repr (laguerreBoundedDiagonal b C hC hb x) n =
      (b n:ℂ)*laguerreHilbertBasis.repr x n := by
  change laguerreHilbertBasis.repr (laguerreHilbertBasis.repr.symm _) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem laguerre_bounded_diagonal_norm (b : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n, |b n| ≤ C) (x : LaguerreWeightedHilbert) :
    ‖laguerreBoundedDiagonal b C hC hb x‖ ≤ C*‖x‖ := by
  change ‖laguerreHilbertBasis.repr.symm (markedBoundedDiagonal b C hC hb
    (laguerreHilbertBasis.repr x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using
    marked_bounded_diagonal_norm b C hC hb (laguerreHilbertBasis.repr x)

theorem laguerre_resolvent_coefficient_bound (α : ℝ) (hα : 0 < α) (n : ℕ) :
    |((n:ℝ)+α)⁻¹| ≤ α⁻¹ := by
  rw [abs_of_pos (inv_pos.2 (by positivity : 0 < (n:ℝ)+α))]
  exact inv_anti₀ hα (le_add_of_nonneg_left (Nat.cast_nonneg n))

def laguerreResolvent (α : ℝ) (hα : 0 < α) :
    LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert :=
  laguerreBoundedDiagonal (fun n => ((n:ℝ)+α)⁻¹) α⁻¹ (inv_nonneg.mpr hα.le)
    (laguerre_resolvent_coefficient_bound α hα)

theorem laguerre_resolvent_coordinate (α : ℝ) (hα : 0 < α)
    (x : LaguerreWeightedHilbert) (n : ℕ) :
    laguerreHilbertBasis.repr (laguerreResolvent α hα x) n =
      ((n:ℂ)+(α:ℂ))⁻¹*laguerreHilbertBasis.repr x n := by
  rw [laguerreResolvent, laguerre_bounded_diagonal_coordinate]
  push_cast
  rfl

theorem laguerre_resolvent_norm (α : ℝ) (hα : 0 < α) (x : LaguerreWeightedHilbert) :
    ‖laguerreResolvent α hα x‖ ≤ α⁻¹*‖x‖ :=
  laguerre_bounded_diagonal_norm _ _ _ _ _

theorem laguerre_resolvent_denominator_ne_zero (α : ℝ) (hα : 0 < α) (n : ℕ) :
    (n:ℂ)+(α:ℂ) ≠ 0 := by
  exact_mod_cast (show (n:ℝ)+α ≠ 0 from (by positivity : 0 < (n:ℝ)+α).ne')

/-- Resolvent outputs lie in the actual unbounded operator domain. -/
theorem laguerre_resolvent_mem_domain (α : ℝ) (hα : 0 < α) (x : LaguerreWeightedHilbert) :
    laguerreResolvent α hα x ∈ (laguerreSpectralOperator id).domain := by
  change Memℓp (fun n : ℕ => ((n:ℝ):ℂ)*laguerreHilbertBasis.repr (laguerreResolvent α hα x) n) 2
  have he : (fun n : ℕ => ((n:ℝ):ℂ)*laguerreHilbertBasis.repr (laguerreResolvent α hα x) n) =
      fun n => laguerreHilbertBasis.repr (x-(α:ℂ) • laguerreResolvent α hα x) n := by
    funext n
    rw [map_sub, map_smul, laguerre_resolvent_coordinate]
    simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      laguerre_resolvent_coordinate]
    change (n:ℂ)*(((n:ℂ)+(α:ℂ))⁻¹*laguerreHilbertBasis.repr x n) =
      laguerreHilbertBasis.repr x n - (α:ℂ)*(((n:ℂ)+(α:ℂ))⁻¹*laguerreHilbertBasis.repr x n)
    field_simp [laguerre_resolvent_denominator_ne_zero α hα n]
    ring
  rw [he]
  exact (laguerreHilbertBasis.repr (x-(α:ℂ) • laguerreResolvent α hα x)).property

theorem laguerre_resolvent_generator_action (α : ℝ) (hα : 0 < α) (x : LaguerreWeightedHilbert) :
    laguerreSpectralOperator id ⟨laguerreResolvent α hα x, laguerre_resolvent_mem_domain α hα x⟩ =
      x-(α:ℂ) • laguerreResolvent α hα x := by
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext n
  rw [laguerre_spectral_coordinate, map_sub, map_smul, laguerre_resolvent_coordinate]
  simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    laguerre_resolvent_coordinate]
  change (n:ℂ)*(((n:ℂ)+(α:ℂ))⁻¹*laguerreHilbertBasis.repr x n) =
    laguerreHilbertBasis.repr x n-(α:ℂ)*(((n:ℂ)+(α:ℂ))⁻¹*laguerreHilbertBasis.repr x n)
  field_simp [laguerre_resolvent_denominator_ne_zero α hα n]
  ring

theorem laguerre_resolvent_right_inverse (α : ℝ) (hα : 0 < α) (x : LaguerreWeightedHilbert) :
    laguerreSpectralOperator id ⟨laguerreResolvent α hα x, laguerre_resolvent_mem_domain α hα x⟩ +
      (α:ℂ) • laguerreResolvent α hα x = x := by
  rw [laguerre_resolvent_generator_action]
  exact sub_add_cancel _ _

theorem laguerre_resolvent_left_inverse (α : ℝ) (hα : 0 < α)
    (x : (laguerreSpectralOperator id).domain) :
    laguerreResolvent α hα (laguerreSpectralOperator id x + (α:ℂ) • x.val) = x.val := by
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext n
  rw [laguerre_resolvent_coordinate, map_add, map_smul]
  change ((n:ℂ)+(α:ℂ))⁻¹ * (laguerreHilbertBasis.repr (laguerreSpectralOperator id x) n +
    (α:ℂ)*laguerreHilbertBasis.repr x.val n) = laguerreHilbertBasis.repr x.val n
  rw [laguerre_spectral_coordinate]
  change ((n:ℂ)+(α:ℂ))⁻¹ * ((n:ℂ)*laguerreHilbertBasis.repr x.val n +
    (α:ℂ)*laguerreHilbertBasis.repr x.val n) = _
  field_simp [laguerre_resolvent_denominator_ne_zero α hα n]
  ring

/-- A complete resolvent recovers precisely the domain, not just its finite
eigenvector span. Together with the action identity this recovers the generator. -/
theorem laguerre_resolvent_range (α : ℝ) (hα : 0 < α) :
    Set.range (laguerreResolvent α hα) = ((laguerreSpectralOperator id).domain : Set _) := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact laguerre_resolvent_mem_domain α hα y
  · intro hx
    exact ⟨laguerreSpectralOperator id ⟨x,hx⟩+(α:ℂ) • x,
      laguerre_resolvent_left_inverse α hα ⟨x,hx⟩⟩

theorem laguerre_resolvent_injective (α : ℝ) (hα : 0 < α) :
    Function.Injective (laguerreResolvent α hα) := by
  intro x y h
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext n
  have he := congrArg (fun z : LaguerreWeightedHilbert => laguerreHilbertBasis.repr z n) h
  dsimp only at he
  rw [laguerre_resolvent_coordinate, laguerre_resolvent_coordinate] at he
  exact mul_left_cancel₀ (inv_ne_zero (laguerre_resolvent_denominator_ne_zero α hα n)) he

theorem laguerre_resolvent_operator_norm (α : ℝ) (hα : 0 < α) :
    ‖laguerreResolvent α hα‖ ≤ α⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hα.le) (laguerre_resolvent_norm α hα)

theorem laguerre_resolvent_identity (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    laguerreResolvent α hα-laguerreResolvent β hβ =
      ((β-α:ℝ):ℂ) • ((laguerreResolvent α hα).comp (laguerreResolvent β hβ)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext n
  change laguerreHilbertBasis.repr (laguerreResolvent α hα x-laguerreResolvent β hβ x) n =
    laguerreHilbertBasis.repr (((β-α:ℝ):ℂ) • laguerreResolvent α hα (laguerreResolvent β hβ x)) n
  rw [map_sub, map_smul]
  simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, laguerre_resolvent_coordinate, Complex.ofReal_sub,
    smul_eq_mul]
  field_simp [laguerre_resolvent_denominator_ne_zero α hα n,
    laguerre_resolvent_denominator_ne_zero β hβ n]
  ring

end
end Sigma
