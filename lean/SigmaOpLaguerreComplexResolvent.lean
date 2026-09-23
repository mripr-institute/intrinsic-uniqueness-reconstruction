import SigmaOpLaguerreResolvent
import SigmaOpLaguerreEigenvalues

namespace Sigma
noncomputable section
open Set Filter
open scoped ENNReal NNReal Topology

theorem marked_complex_multiplier_mem (b : ℕ → ℂ) (C : ℝ)
    (hb : ∀ n, ‖b n‖ ≤ C) (x : MarkedIntegerHilbert) :
    Memℓp (fun n => b n*x n) 2 := by
  have hbound (n : ℕ) : ‖b n*x n‖^2 ≤ C^2*‖x n‖^2 := by
    rw [norm_mul, mul_pow]
    gcongr
    exact hb n
  have hs := Summable.of_nonneg_of_le (fun n => sq_nonneg ‖b n*x n‖)
    hbound ((marked_l2_square_summable x).mul_left (C^2))
  apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs

def markedComplexDiagonalLinear (b : ℕ → ℂ) (C : ℝ) (hb : ∀ n, ‖b n‖ ≤ C) :
    MarkedIntegerHilbert →ₗ[ℂ] MarkedIntegerHilbert where
  toFun x := ⟨fun n => b n*x n, marked_complex_multiplier_mem b C hb x⟩
  map_add' x y := by
    apply lp.ext
    funext n
    change b n*(x n+y n) = b n*x n+b n*y n
    ring
  map_smul' c x := by
    apply lp.ext
    funext n
    change b n*(c*x n) = c*(b n*x n)
    ring

theorem marked_complex_diagonal_norm (b : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n, ‖b n‖ ≤ C) (x : MarkedIntegerHilbert) :
    ‖markedComplexDiagonalLinear b C hb x‖ ≤ C*‖x‖ := by
  have hh : ‖markedComplexDiagonalLinear b C hb x‖^2 ≤ (C*‖x‖)^2 := by
    rw [marked_l2_norm_square, mul_pow, marked_l2_norm_square, ← tsum_mul_left]
    apply tsum_le_tsum _ (marked_l2_square_summable (markedComplexDiagonalLinear b C hb x))
      ((marked_l2_square_summable x).mul_left (C^2))
    intro n
    change ‖b n*x n‖^2 ≤ C^2*‖x n‖^2
    rw [norm_mul, mul_pow]
    gcongr
    exact hb n
  nlinarith [norm_nonneg (markedComplexDiagonalLinear b C hb x),
    mul_nonneg hC (norm_nonneg x)]

def laguerreComplexDiagonal (b : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n, ‖b n‖ ≤ C) : LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert :=
  laguerreHilbertBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((markedComplexDiagonalLinear b C hb).mkContinuous C
      (marked_complex_diagonal_norm b C hC hb)).comp
      laguerreHilbertBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem laguerre_complex_diagonal_coordinate (b : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n, ‖b n‖ ≤ C) (x : LaguerreWeightedHilbert) (n : ℕ) :
    laguerreHilbertBasis.repr (laguerreComplexDiagonal b C hC hb x) n =
      b n*laguerreHilbertBasis.repr x n := by
  change laguerreHilbertBasis.repr (laguerreHilbertBasis.repr.symm _) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem complex_integer_reciprocal_bounded (lam : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖((n:ℂ)-lam)⁻¹‖ ≤ C := by
  obtain ⟨N, hN⟩ := exists_nat_gt (‖lam‖+1)
  refine ⟨1+∑ k ∈ Finset.range N, ‖((k:ℂ)-lam)⁻¹‖, by positivity, ?_⟩
  intro n
  by_cases hn : n < N
  · have hs := Finset.single_le_sum (f := fun k : ℕ => ‖((k:ℂ)-lam)⁻¹‖)
      (fun k _ => norm_nonneg _) (Finset.mem_range.mpr hn)
    linarith
  · have hlarge : 1 ≤ ‖(n:ℂ)-lam‖ := by
      have hnat : (N:ℝ) ≤ n := Nat.cast_le.mpr (Nat.le_of_not_gt hn)
      have htri := norm_sub_norm_le (n:ℂ) lam
      simp only [Complex.norm_natCast] at htri
      linarith
    have hinv : ‖((n:ℂ)-lam)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hlarge
    exact hinv.trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))

def laguerreComplexResolvent (lam : ℂ) :
    LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert :=
  laguerreComplexDiagonal (fun n => ((n:ℂ)-lam)⁻¹)
    (complex_integer_reciprocal_bounded lam).choose
    (complex_integer_reciprocal_bounded lam).choose_spec.1
    (complex_integer_reciprocal_bounded lam).choose_spec.2

theorem laguerre_complex_resolvent_coordinate (lam : ℂ)
    (x : LaguerreWeightedHilbert) (n : ℕ) :
    laguerreHilbertBasis.repr (laguerreComplexResolvent lam x) n =
      ((n:ℂ)-lam)⁻¹*laguerreHilbertBasis.repr x n :=
  laguerre_complex_diagonal_coordinate _ _ _ _ _ _

/-- The standard resolvent condition for an unbounded operator: an everywhere
defined bounded linear inverse of `A - lam I`, with values in the full domain.
The pinned Mathlib has no unbounded-operator spectrum definition. -/
def HasBoundedUnboundedResolvent {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (lam : ℂ) : Prop :=
  ∃ R : H →L[ℂ] H, ∃ hdom : ∀ x, R x ∈ A.domain,
    (∀ x, A ⟨R x, hdom x⟩ - lam • R x = x) ∧
    (∀ x : A.domain, R (A x-lam • x.val) = x.val)

def unboundedOperatorSpectrum {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  {lam | ¬ HasBoundedUnboundedResolvent A lam}

theorem laguerre_complex_resolvent_mem_domain (lam : ℂ)
    (hlam : ∀ n : ℕ, lam ≠ (n:ℂ)) (x : LaguerreWeightedHilbert) :
    laguerreComplexResolvent lam x ∈ (laguerreSpectralOperator id).domain := by
  change Memℓp (fun n : ℕ => ((n:ℝ):ℂ)*laguerreHilbertBasis.repr (laguerreComplexResolvent lam x) n) 2
  have he : (fun n : ℕ => ((n:ℝ):ℂ)*laguerreHilbertBasis.repr (laguerreComplexResolvent lam x) n) =
      fun n => laguerreHilbertBasis.repr (x+lam • laguerreComplexResolvent lam x) n := by
    funext n
    rw [map_add, map_smul, laguerre_complex_resolvent_coordinate]
    simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      laguerre_complex_resolvent_coordinate]
    push_cast
    field_simp [sub_ne_zero.mpr (hlam n).symm]
    ring
  rw [he]
  exact (laguerreHilbertBasis.repr (x+lam • laguerreComplexResolvent lam x)).property

theorem laguerre_complex_resolvent_generator_action (lam : ℂ)
    (hlam : ∀ n : ℕ, lam ≠ (n:ℂ)) (x : LaguerreWeightedHilbert) :
    laguerreSpectralOperator id ⟨laguerreComplexResolvent lam x,
      laguerre_complex_resolvent_mem_domain lam hlam x⟩ = x+lam • laguerreComplexResolvent lam x := by
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext n
  rw [laguerre_spectral_coordinate, map_add, map_smul, laguerre_complex_resolvent_coordinate]
  simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    laguerre_complex_resolvent_coordinate, id_eq]
  push_cast
  field_simp [sub_ne_zero.mpr (hlam n).symm]
  ring

theorem laguerre_complex_resolvent_left_inverse (lam : ℂ)
    (hlam : ∀ n : ℕ, lam ≠ (n:ℂ)) (x : (laguerreSpectralOperator id).domain) :
    laguerreComplexResolvent lam (laguerreSpectralOperator id x-lam • x.val) = x.val := by
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext n
  rw [laguerre_complex_resolvent_coordinate, map_sub, map_smul]
  simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    laguerre_spectral_coordinate, id_eq]
  push_cast
  field_simp [sub_ne_zero.mpr (hlam n).symm]
  ring

theorem laguerre_has_complex_resolvent (lam : ℂ) (hlam : ∀ n : ℕ, lam ≠ (n:ℂ)) :
    HasBoundedUnboundedResolvent (laguerreSpectralOperator id) lam := by
  refine ⟨laguerreComplexResolvent lam, laguerre_complex_resolvent_mem_domain lam hlam, ?_,
    laguerre_complex_resolvent_left_inverse lam hlam⟩
  intro x
  rw [laguerre_complex_resolvent_generator_action lam hlam x]
  exact add_sub_cancel_right _ _

theorem bounded_unbounded_resolvent_excludes_eigenvalue {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] (A : H →ₗ.[ℂ] H) (lam : ℂ)
    (hR : HasBoundedUnboundedResolvent A lam)
    (x : A.domain) (hx : A x = lam • x.val) : x.val = 0 := by
  obtain ⟨R, _, _, hi⟩ := hR
  have h := hi x
  rw [hx, sub_self, map_zero] at h
  exact h.symm

/-- Exact full complex resolvent set, not merely the point spectrum. -/
theorem laguerre_full_resolvent_set (lam : ℂ) :
    HasBoundedUnboundedResolvent (laguerreSpectralOperator id) lam ↔
      ∀ n : ℕ, lam ≠ (n:ℂ) := by
  constructor
  · intro h n hn
    subst lam
    exact laguerreHilbertBasis.orthonormal.ne_zero n
      (bounded_unbounded_resolvent_excludes_eigenvalue _ _ h
        ⟨laguerreHilbertBasis n, laguerre_basis_mem_spectral_domain id n⟩
        (laguerre_spectral_basis_action id n))
  · exact laguerre_has_complex_resolvent lam

theorem laguerre_full_spectrum_exact :
    unboundedOperatorSpectrum (laguerreSpectralOperator id) = Set.range (fun n : ℕ => (n:ℂ)) := by
  ext lam
  simp only [unboundedOperatorSpectrum, Set.mem_setOf_eq, laguerre_full_resolvent_set,
    Set.mem_range]
  push_neg
  exact exists_congr (fun n => eq_comm)

end
end Sigma
