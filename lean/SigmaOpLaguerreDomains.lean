import SigmaOpLaguerreSpectral

namespace Sigma
noncomputable section
open scoped ENNReal ComplexConjugate

/-- Coefficients are taken in the proved normalized Laguerre Hilbert basis. -/
def laguerreCoefficient (x : LaguerreWeightedHilbert) (n : ℕ) : ℂ :=
  laguerreHilbertBasis.repr x n

theorem laguerre_spectral_domain_iff (f : ℝ → ℝ) (x : LaguerreWeightedHilbert) :
    x ∈ (laguerreSpectralOperator f).domain ↔
      Summable (fun n : ℕ => (f n)^2 * ‖laguerreCoefficient x n‖^2) := by
  change Memℓp (fun n : ℕ => (f n : ℂ) * laguerreCoefficient x n) 2 ↔ _
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]

theorem laguerre_integer_domain_iff (x : LaguerreWeightedHilbert) :
    x ∈ (laguerreSpectralOperator id).domain ↔
      Summable (fun n : ℕ => (n : ℝ)^2 * ‖laguerreCoefficient x n‖^2) :=
  laguerre_spectral_domain_iff id x

theorem laguerre_square_root_domain_iff (x : LaguerreWeightedHilbert) :
    x ∈ (laguerreSpectralOperator Real.sqrt).domain ↔
      Summable (fun n : ℕ => (n : ℝ) * ‖laguerreCoefficient x n‖^2) := by
  rw [laguerre_spectral_domain_iff]
  simp only [Real.sq_sqrt (Nat.cast_nonneg _)]

/-- The action is an actual convergent Hilbert-space series. -/
theorem laguerre_spectral_action_hasSum (f : ℝ → ℝ)
    (x : (laguerreSpectralOperator f).domain) :
    HasSum (fun n : ℕ => ((f n : ℂ) * laguerreCoefficient x.val n) •
      laguerreHilbertBasis n) (laguerreSpectralOperator f x) := by
  simpa only [laguerre_spectral_coordinate, laguerreCoefficient] using
    laguerreHilbertBasis.hasSum_repr (laguerreSpectralOperator f x)

theorem laguerre_integer_action_hasSum (x : (laguerreSpectralOperator id).domain) :
    HasSum (fun n : ℕ => ((n : ℂ) * laguerreCoefficient x.val n) •
      laguerreHilbertBasis n) (laguerreSpectralOperator id x) := by
  simpa using laguerre_spectral_action_hasSum id x

theorem laguerre_spectral_norm_sq (f : ℝ → ℝ)
    (x : (laguerreSpectralOperator f).domain) :
    ‖laguerreSpectralOperator f x‖^2 =
      ∑' n : ℕ, (f n)^2 * ‖laguerreCoefficient x.val n‖^2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (laguerreHilbertBasis.repr (laguerreSpectralOperator f x))
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    LinearIsometryEquiv.norm_map, laguerre_spectral_coordinate, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, laguerreCoefficient] using h

/-- The spectral square-root energy is the exact weighted coefficient sum.
Its identification with the closed differential energy is a separate bridge. -/
theorem laguerre_square_root_energy
    (x : (laguerreSpectralOperator Real.sqrt).domain) :
    ‖laguerreSpectralOperator Real.sqrt x‖^2 =
      ∑' n : ℕ, (n : ℝ) * ‖laguerreCoefficient x.val n‖^2 := by
  rw [laguerre_spectral_norm_sq]
  simp only [Real.sq_sqrt (Nat.cast_nonneg _)]

theorem laguerre_integer_domain_le_square_root :
    (laguerreSpectralOperator id).domain ≤
      (laguerreSpectralOperator Real.sqrt).domain := by
  intro x hx
  rw [laguerre_square_root_domain_iff]
  apply Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => ?_) ((laguerre_integer_domain_iff x).mp hx)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have h : (n : ℝ) ≤ (n : ℝ)^2 := by
    rcases n with _ | n
    · norm_num
    · have hn : 1 ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      nlinarith
  exact h

/-- The square of the spectral square root has exactly the integer operator's
domain, including the zero mode. -/
theorem laguerre_square_root_image_domain_iff
    (x : (laguerreSpectralOperator Real.sqrt).domain) :
    laguerreSpectralOperator Real.sqrt x ∈ (laguerreSpectralOperator Real.sqrt).domain ↔
      x.val ∈ (laguerreSpectralOperator id).domain := by
  rw [laguerre_square_root_domain_iff, laguerre_integer_domain_iff]
  simp only [laguerreCoefficient, laguerre_spectral_coordinate, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    Real.sq_sqrt (Nat.cast_nonneg _), ← mul_assoc, ← pow_two]

theorem laguerre_square_root_squared
    (x : (laguerreSpectralOperator id).domain) :
    laguerreSpectralOperator Real.sqrt
      ⟨laguerreSpectralOperator Real.sqrt
        ⟨x.val, laguerre_integer_domain_le_square_root x.property⟩,
       (laguerre_square_root_image_domain_iff _).mpr x.property⟩ =
      laguerreSpectralOperator id x := by
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext n
  simp only [laguerre_spectral_coordinate, id_eq, ← mul_assoc,
    ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]

theorem laguerre_spectral_inner (f : ℝ → ℝ)
    (x : (laguerreSpectralOperator f).domain) :
    @inner ℂ LaguerreWeightedHilbert _ x.val (laguerreSpectralOperator f x) =
      ((∑' n : ℕ, f n * ‖laguerreCoefficient x.val n‖^2 : ℝ) : ℂ) := by
  rw [← laguerreHilbertBasis.repr.inner_map_map, lp.inner_eq_tsum, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [laguerre_spectral_coordinate]
  simp only [RCLike.inner_apply, Complex.ofReal_mul, laguerreCoefficient]
  rw [mul_left_comm, Complex.conj_mul']
  rw [Complex.ofReal_pow]

theorem laguerre_spectral_nonnegative (f : ℝ → ℝ)
    (hf : ∀ n : ℕ, 0 ≤ f n) (x : (laguerreSpectralOperator f).domain) :
    0 ≤ (@inner ℂ LaguerreWeightedHilbert _ x.val (laguerreSpectralOperator f x)).re := by
  rw [laguerre_spectral_inner, Complex.ofReal_re]
  exact tsum_nonneg fun n => mul_nonneg (hf n) (sq_nonneg _)

theorem laguerre_square_root_nonnegative
    (x : (laguerreSpectralOperator Real.sqrt).domain) :
    0 ≤ (@inner ℂ LaguerreWeightedHilbert _ x.val
      (laguerreSpectralOperator Real.sqrt x)).re :=
  laguerre_spectral_nonnegative Real.sqrt (fun _ => Real.sqrt_nonneg _) x

theorem laguerre_integer_inner_energy (x : (laguerreSpectralOperator id).domain) :
    @inner ℂ LaguerreWeightedHilbert _ x.val (laguerreSpectralOperator id x) =
      ((‖laguerreSpectralOperator Real.sqrt
        ⟨x.val, laguerre_integer_domain_le_square_root x.property⟩‖^2 : ℝ) : ℂ) := by
  rw [laguerre_spectral_inner, laguerre_square_root_energy]
  rfl

end
end Sigma
