import SigmaOpGammaShapeThreeSpectral
import SigmaOpHeatTrace
import SigmaOpDeterminantCanonical
import SigmaOpDeterminantZeta

namespace Sigma
noncomputable section
open Filter
open scoped Topology BigOperators
set_option maxHeartbeats 800000

/-- A small bridge from the standard nuclear criterion to an arbitrary maximal
spectral multiplier; in particular, this handles every unbounded parameter. -/
theorem integer_basis_multiplier_nuclear_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℂ) :
    IsNuclearPartialOperator (integerBasisMultiplier b f) ↔ Summable (fun n => ‖f n‖) := by
  constructor
  · rintro ⟨T, hT, he⟩
    have hact (n : ℕ) : T (b n) = f n • b n := by
      have hv := he.le.2 (x := ⟨b n, integer_basis_mem_multiplier_domain b f n⟩)
        (y := ⟨b n, Submodule.mem_top⟩) rfl
      exact hv.symm.trans (integer_basis_multiplier_basis_action b f n)
    exact (diagonal_operator_nuclear_iff b T f hact).mp hT
  · intro hf
    let C : ℝ := ∑' n, ‖f n‖
    have hC : 0 ≤ C := tsum_nonneg (fun _ => norm_nonneg _)
    have hb (n : ℕ) : ‖f n‖ ≤ C := le_tsum hf n (fun _ _ => norm_nonneg _)
    refine ⟨integerBasisBoundedMultiplier b f C hC hb, ?_,
      integer_basis_bounded_multiplier_eq b f C hC hb⟩
    exact diagonal_operator_nuclear_of_summable b _ f
      (integer_basis_bounded_multiplier_basis_action b f C hC hb) hf

def isometryConjugateOperator
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) : K →L[ℂ] K :=
  U.toLinearIsometry.toContinuousLinearMap.comp
    (T.comp U.symm.toLinearIsometry.toContinuousLinearMap)

theorem isometry_conjugate_comp
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H ≃ₗᵢ[ℂ] K) (S T : H →L[ℂ] H) :
    (isometryConjugateOperator U S).comp (isometryConjugateOperator U T) =
      isometryConjugateOperator U (S.comp T) := by
  apply ContinuousLinearMap.ext
  intro x
  change U (S (U.symm (U (T (U.symm x))))) = U (S (T (U.symm x)))
  rw [U.symm_apply_apply]

theorem isometry_conjugate_compression_matrix
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H ≃ₗᵢ[ℂ] K) (b : HilbertBasis ℕ ℂ H) (c : HilbertBasis ℕ ℂ K)
    (hU : ∀ n, U (b n) = c n) (T : H →L[ℂ] H) (N : ℕ) :
    hilbertCompressionMatrix c (isometryConjugateOperator U T) N =
      hilbertCompressionMatrix b T N := by
  ext i j
  have hj : U.symm (c j) = b j := by rw [←hU, U.symm_apply_apply]
  change @inner ℂ K _ (c i) (U (T (U.symm (c j)))) = @inner ℂ H _ (b i) (T (b j))
  rw [hj, ←hU, U.inner_map_map]

theorem isometry_conjugate_resolvent
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H ≃ₗᵢ[ℂ] K) (A : H →ₗ.[ℂ] H) (B : K →ₗ.[ℂ] K)
    (hd : ∀ x : H, U x ∈ B.domain ↔ x ∈ A.domain)
    (hact : ∀ x : A.domain,
      U (A x) = B ⟨U x.val, (hd x.val).mpr x.property⟩)
    (a : ℂ) (R : H →L[ℂ] H) (hR : OpIsResolvent A a R) :
    OpIsResolvent B a (isometryConjugateOperator U R) := by
  have hmem (x : K) : isometryConjugateOperator U R x ∈ B.domain :=
    (hd _).mpr (hR.image_mem _)
  refine ⟨hmem, ?_, ?_⟩
  · intro x
    have h := congrArg U (hR.right_inverse (U.symm x))
    rw [map_add, map_smul, U.apply_symm_apply, hact] at h
    exact h
  · intro x
    have hx : U.symm x.val ∈ A.domain := (hd _).mp (by
      simpa only [U.apply_symm_apply] using x.property)
    have hA := hact ⟨U.symm x.val, hx⟩
    simp only [U.apply_symm_apply] at hA
    change U (R (U.symm (B x + a • x.val))) = x.val
    rw [←hA, map_add, map_smul, U.symm_apply_apply, hR.left_inverse, U.apply_symm_apply]

/-- Transport of an actual bounded operator between the two native weighted spaces. -/
def gammaShapeConjugateOperator
    (T : LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert) :
    GammaShapeThreeWeightedHilbert →L[ℂ] GammaShapeThreeWeightedHilbert :=
  isometryConjugateOperator gammaShapeUnitary T

theorem gamma_shape_conjugate_apply
    (T : LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert)
    (x : GammaShapeThreeWeightedHilbert) :
    gammaShapeConjugateOperator T x = gammaShapeUnitary (T (gammaShapeUnitary.symm x)) := rfl

theorem gamma_shape_unitary_symm_basis (n : ℕ) :
    gammaShapeUnitary.symm (gammaShapeThreeHilbertBasis n) = laguerreHilbertBasis n := by
  apply gammaShapeUnitary.injective
  rw [gammaShapeUnitary.apply_symm_apply, gamma_shape_unitary_basis]

theorem gamma_shape_conjugate_basis_action
    (T : LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert)
    (f : ℕ → ℂ) (hT : ∀ n, T (laguerreHilbertBasis n) = f n • laguerreHilbertBasis n)
    (n : ℕ) : gammaShapeConjugateOperator T (gammaShapeThreeHilbertBasis n) =
      f n • gammaShapeThreeHilbertBasis n := by
  rw [gamma_shape_conjugate_apply, gamma_shape_unitary_symm_basis, hT, map_smul,
    gamma_shape_unitary_basis]

theorem gamma_shape_conjugate_nuclear_iff
    (T : LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert)
    (f : ℕ → ℂ) (hT : ∀ n, T (laguerreHilbertBasis n) = f n • laguerreHilbertBasis n) :
    IsNuclearOperator (gammaShapeConjugateOperator T) ↔ IsNuclearOperator T := by
  rw [diagonal_operator_nuclear_iff gammaShapeThreeHilbertBasis _ f
    (gamma_shape_conjugate_basis_action T f hT),
    diagonal_operator_nuclear_iff laguerreHilbertBasis T f hT]

theorem gamma_shape_conjugate_nuclear_trace
    (T : LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert)
    (f : ℕ → ℂ) (hT : ∀ n, T (laguerreHilbertBasis n) = f n • laguerreHilbertBasis n)
    (hN : IsNuclearOperator T) :
    nuclearTrace (gammaShapeConjugateOperator T)
      ((gamma_shape_conjugate_nuclear_iff T f hT).mpr hN) = nuclearTrace T hN := by
  rw [diagonal_operator_nuclear_trace gammaShapeThreeHilbertBasis _ f
    (gamma_shape_conjugate_basis_action T f hT),
    diagonal_operator_nuclear_trace laguerreHilbertBasis T f hT]

/-- The actual two-sided positive-shift inverse, transported with its full domain. -/
def gammaShapeThreeResolvent (a : ℝ) (ha : 0 < a) :
    GammaShapeThreeWeightedHilbert →L[ℂ] GammaShapeThreeWeightedHilbert :=
  gammaShapeConjugateOperator (laguerreResolvent a ha)

theorem gamma_shape_three_resolvent_basis_action (a : ℝ) (ha : 0 < a) (n : ℕ) :
    gammaShapeThreeResolvent a ha (gammaShapeThreeHilbertBasis n) =
      ((n : ℂ)+(a : ℂ))⁻¹ • gammaShapeThreeHilbertBasis n :=
  gamma_shape_conjugate_basis_action _ _ (laguerre_resolvent_basis_action a ha) n

theorem gamma_shape_three_resolvent_image_mem (a : ℝ) (ha : 0 < a)
    (x : GammaShapeThreeWeightedHilbert) :
    gammaShapeThreeResolvent a ha x ∈ gammaShapeThreeSpectralOperator.domain := by
  change gammaShapeUnitary (laguerreResolvent a ha (gammaShapeUnitary.symm x)) ∈ _
  exact (gamma_shape_unitary_spectral_domain_iff _).mpr
    ((laguerre_canonical_positive_shift_resolvent a ha).image_mem _)

theorem gamma_shape_three_resolvent (a : ℝ) (ha : 0 < a) :
    OpIsResolvent gammaShapeThreeSpectralOperator (a : ℂ) (gammaShapeThreeResolvent a ha) :=
  isometry_conjugate_resolvent gammaShapeUnitary laguerreCanonicalOperator
    gammaShapeThreeSpectralOperator gamma_shape_unitary_spectral_domain_iff
    gamma_shape_unitary_spectral_action a (laguerreResolvent a ha)
    (laguerre_canonical_positive_shift_resolvent a ha)

theorem gamma_shape_three_resolvent_not_nuclear (a : ℝ) (ha : 0 < a) :
    ¬ IsNuclearOperator (gammaShapeThreeResolvent a ha) := by
  intro hn
  exact laguerre_resolvent_not_nuclear a ha
    ((gamma_shape_conjugate_nuclear_iff _ _ (laguerre_resolvent_basis_action a ha)).mp hn)

theorem gamma_shape_three_resolvent_hilbert_schmidt (a : ℝ) (ha : 0 < a) :
    IsHilbertSchmidtOperator (gammaShapeThreeResolvent a ha) := by
  refine ⟨gammaShapeThreeHilbertBasis, ?_⟩
  convert operator_squared_resolvent_eigenvalues_summable a ha using 1
  funext n
  rw [gamma_shape_three_resolvent_basis_action, norm_smul,
    gammaShapeThreeHilbertBasis.orthonormal.1 n, mul_one, norm_inv,
    ← Complex.ofReal_natCast n, ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (n : ℝ)+a)]
  simp only [one_div, inv_pow]

def gammaShapeThreeSquaredResolvent (a : ℝ) (ha : 0 < a) :
    GammaShapeThreeWeightedHilbert →L[ℂ] GammaShapeThreeWeightedHilbert :=
  (gammaShapeThreeResolvent a ha).comp (gammaShapeThreeResolvent a ha)

theorem gamma_shape_three_squared_resolvent_conjugate (a : ℝ) (ha : 0 < a) :
    gammaShapeThreeSquaredResolvent a ha =
      gammaShapeConjugateOperator (laguerreSquaredResolvent a ha) :=
  isometry_conjugate_comp gammaShapeUnitary _ _

theorem gamma_shape_three_squared_resolvent_basis_action (a : ℝ) (ha : 0 < a) (n : ℕ) :
    gammaShapeThreeSquaredResolvent a ha (gammaShapeThreeHilbertBasis n) =
      (((n : ℂ)+(a : ℂ))⁻¹ ^ 2) • gammaShapeThreeHilbertBasis n := by
  rw [gamma_shape_three_squared_resolvent_conjugate]
  exact gamma_shape_conjugate_basis_action _ _ (laguerre_squared_resolvent_basis_action a ha) n

theorem gamma_shape_three_squared_resolvent_nuclear (a : ℝ) (ha : 0 < a) :
    IsNuclearOperator (gammaShapeThreeSquaredResolvent a ha) := by
  rw [gamma_shape_three_squared_resolvent_conjugate,
    gamma_shape_conjugate_nuclear_iff _ _ (laguerre_squared_resolvent_basis_action a ha)]
  exact laguerre_squared_resolvent_nuclear a ha

theorem gamma_shape_three_squared_resolvent_trace (a : ℝ) (ha : 0 < a) :
    nuclearTrace (gammaShapeThreeSquaredResolvent a ha)
      (gamma_shape_three_squared_resolvent_nuclear a ha) =
      nuclearTrace (laguerreSquaredResolvent a ha)
        (laguerre_squared_resolvent_nuclear a ha) := by
  rw [diagonal_operator_nuclear_trace gammaShapeThreeHilbertBasis _ _
    (gamma_shape_three_squared_resolvent_basis_action a ha), laguerre_squared_resolvent_trace]
  simp only [one_div]

theorem gamma_shape_three_resolvent_difference_basis_action (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    (gammaShapeThreeResolvent a ha - gammaShapeThreeResolvent b hb)
      (gammaShapeThreeHilbertBasis n) =
      (((((n : ℝ)+a)⁻¹ - ((n : ℝ)+b)⁻¹) : ℝ) : ℂ) • gammaShapeThreeHilbertBasis n := by
  rw [ContinuousLinearMap.sub_apply, gamma_shape_three_resolvent_basis_action,
    gamma_shape_three_resolvent_basis_action, ← sub_smul]
  congr 1
  push_cast
  ring

theorem gamma_shape_three_resolvent_difference_nuclear (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    IsNuclearOperator (gammaShapeThreeResolvent a ha - gammaShapeThreeResolvent b hb) := by
  apply (diagonal_operator_nuclear_iff gammaShapeThreeHilbertBasis _ _
    (gamma_shape_three_resolvent_difference_basis_action a b ha hb)).mpr
  exact (diagonal_operator_nuclear_iff laguerreHilbertBasis _ _
    (laguerre_resolvent_difference_basis_action a b ha hb)).mp
    (laguerre_resolvent_difference_nuclear a b ha hb)

theorem gamma_shape_three_resolvent_difference_trace (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    nuclearTrace (gammaShapeThreeResolvent a ha - gammaShapeThreeResolvent b hb)
      (gamma_shape_three_resolvent_difference_nuclear a b ha hb) =
      nuclearTrace (laguerreResolvent a ha - laguerreResolvent b hb)
        (laguerre_resolvent_difference_nuclear a b ha hb) := by
  rw [diagonal_operator_nuclear_trace gammaShapeThreeHilbertBasis _ _
    (gamma_shape_three_resolvent_difference_basis_action a b ha hb),
    laguerre_resolvent_difference_trace]

theorem gamma_shape_three_complex_heat_trace :
    (∀ τ : ℂ, IsNuclearPartialOperator (integerHeatOperator gammaShapeThreeHilbertBasis τ) ↔
      0 < τ.re) ∧
    (∀ (τ : ℂ) (hτ : 0 < τ.re),
      nuclearTrace (integerHeatBoundedOperator gammaShapeThreeHilbertBasis τ hτ.le)
        (integer_heat_bounded_nuclear gammaShapeThreeHilbertBasis τ hτ) =
      nuclearTrace (integerHeatBoundedOperator laguerreHilbertBasis τ hτ.le)
        (integer_heat_bounded_nuclear laguerreHilbertBasis τ hτ)) := by
  refine ⟨integer_heat_operator_nuclear_iff gammaShapeThreeHilbertBasis, ?_⟩
  intro τ hτ
  rw [integer_heat_operator_trace _ τ hτ, integer_heat_operator_trace _ τ hτ]

theorem gamma_shape_three_unit_shift_zeta_trace :
    (∀ s : ℂ, IsNuclearPartialOperator (integerZetaOperator gammaShapeThreeHilbertBasis s) ↔
      1 < s.re) ∧
    (∀ (s : ℂ) (hs : 1 < s.re),
      nuclearTrace (integerZetaBoundedOperator gammaShapeThreeHilbertBasis s (le_trans zero_le_one hs.le))
        (integer_zeta_bounded_nuclear gammaShapeThreeHilbertBasis s hs) =
      nuclearTrace (integerZetaBoundedOperator laguerreHilbertBasis s (le_trans zero_le_one hs.le))
        (integer_zeta_bounded_nuclear laguerreHilbertBasis s hs)) := by
  refine ⟨integer_zeta_operator_nuclear_iff gammaShapeThreeHilbertBasis, ?_⟩
  intro s hs
  rw [integer_zeta_operator_trace _ s hs, integer_zeta_operator_trace _ s hs]

/-- Maximal shifted complex powers of the actual shape-three realization. -/
def gammaShapeThreeShiftedZetaOperator (a : ℝ) (s : ℂ) :
    GammaShapeThreeWeightedHilbert →ₗ.[ℂ] GammaShapeThreeWeightedHilbert :=
  integerBasisMultiplier gammaShapeThreeHilbertBasis (laguerreShiftedZetaMultiplier a s)

def gammaShapeThreeShiftedZetaBoundedOperator (a : ℝ) (ha : 0 < a) (s : ℂ)
    (hs : 1 < s.re) :
    GammaShapeThreeWeightedHilbert →L[ℂ] GammaShapeThreeWeightedHilbert :=
  integerBasisBoundedMultiplier gammaShapeThreeHilbertBasis (laguerreShiftedZetaMultiplier a s)
    (∑' k, ‖laguerreShiftedZetaMultiplier a s k‖) (tsum_nonneg (fun _ => norm_nonneg _))
    (fun n => le_tsum ((laguerre_shifted_zeta_multiplier_summable_iff a ha s).mpr hs)
      n (fun _ _ => norm_nonneg _))

theorem gamma_shape_three_shifted_zeta_bounded_basis_action (a : ℝ) (ha : 0 < a)
    (s : ℂ) (hs : 1 < s.re) (n : ℕ) :
    gammaShapeThreeShiftedZetaBoundedOperator a ha s hs (gammaShapeThreeHilbertBasis n) =
      laguerreShiftedZetaMultiplier a s n • gammaShapeThreeHilbertBasis n :=
  integer_basis_bounded_multiplier_basis_action _ _ _ _ _ _

theorem gamma_shape_three_shifted_zeta_bounded_nuclear (a : ℝ) (ha : 0 < a)
    (s : ℂ) (hs : 1 < s.re) :
    IsNuclearOperator (gammaShapeThreeShiftedZetaBoundedOperator a ha s hs) :=
  diagonal_operator_nuclear_of_summable gammaShapeThreeHilbertBasis _ _
    (gamma_shape_three_shifted_zeta_bounded_basis_action a ha s hs)
    ((laguerre_shifted_zeta_multiplier_summable_iff a ha s).mpr hs)

theorem gamma_shape_three_shifted_zeta_bounded_eq (a : ℝ) (ha : 0 < a)
    (s : ℂ) (hs : 1 < s.re) :
    gammaShapeThreeShiftedZetaOperator a s =
      (gammaShapeThreeShiftedZetaBoundedOperator a ha s hs).toLinearMap.toPMap ⊤ :=
  integer_basis_bounded_multiplier_eq _ _ _ _ _

/-- The exact half-plane also excludes unbounded maximal powers. -/
theorem gamma_shape_three_shifted_zeta_nuclear_iff (a : ℝ) (ha : 0 < a) (s : ℂ) :
    IsNuclearPartialOperator (gammaShapeThreeShiftedZetaOperator a s) ↔ 1 < s.re := by
  rw [gammaShapeThreeShiftedZetaOperator, integer_basis_multiplier_nuclear_iff]
  exact laguerre_shifted_zeta_multiplier_summable_iff a ha s

theorem gamma_shape_shifted_zeta_nuclear_range (a : ℝ) (ha : 0 < a) (s : ℂ) :
    (IsNuclearPartialOperator (laguerreShiftedZetaOperator a s) ↔ 1 < s.re) ∧
    (IsNuclearPartialOperator (gammaShapeThreeShiftedZetaOperator a s) ↔ 1 < s.re) := by
  refine ⟨?_, gamma_shape_three_shifted_zeta_nuclear_iff a ha s⟩
  rw [laguerreShiftedZetaOperator, integer_basis_multiplier_nuclear_iff]
  exact laguerre_shifted_zeta_multiplier_summable_iff a ha s

theorem gamma_shape_three_shifted_zeta_trace (a : ℝ) (ha : 0 < a)
    (s : ℂ) (hs : 1 < s.re) :
    nuclearTrace (gammaShapeThreeShiftedZetaBoundedOperator a ha s hs)
      (gamma_shape_three_shifted_zeta_bounded_nuclear a ha s hs) =
      nuclearTrace (laguerreShiftedZetaBoundedOperator a ha s hs)
        (laguerre_shifted_zeta_bounded_nuclear a ha s hs) := by
  rw [diagonal_operator_nuclear_trace gammaShapeThreeHilbertBasis _ _
    (gamma_shape_three_shifted_zeta_bounded_basis_action a ha s hs),
    laguerre_shifted_zeta_trace a ha s hs]
  exact (laguerre_hurwitz_zeta_hasSum a ha s hs).tsum_eq

/-- Unitary conjugacy of every maximal multiplier includes its full domain. -/
theorem gamma_shape_three_multiplier_domain_iff (f : ℕ → ℂ) (x : LaguerreWeightedHilbert) :
    gammaShapeUnitary x ∈ (integerBasisMultiplier gammaShapeThreeHilbertBasis f).domain ↔
      x ∈ (integerBasisMultiplier laguerreHilbertBasis f).domain :=
  integer_basis_unitary_domain_iff _ _ _ x

theorem gamma_shape_three_multiplier_action (f : ℕ → ℂ)
    (x : (integerBasisMultiplier laguerreHilbertBasis f).domain) :
    gammaShapeUnitary (integerBasisMultiplier laguerreHilbertBasis f x) =
      integerBasisMultiplier gammaShapeThreeHilbertBasis f
        ⟨gammaShapeUnitary x.val, (gamma_shape_three_multiplier_domain_iff f x.val).mpr x.property⟩ :=
  integer_basis_unitary_multiplier_action _ _ _ x

theorem gamma_shape_conjugate_compression_matrix
    (T : LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert) (N : ℕ) :
    hilbertCompressionMatrix gammaShapeThreeHilbertBasis (gammaShapeConjugateOperator T) N =
      hilbertCompressionMatrix laguerreHilbertBasis T N :=
  isometry_conjugate_compression_matrix gammaShapeUnitary _ _ gamma_shape_unitary_basis T N

/-- Ordinary determinants of compressions of the actual squared resolvent. -/
def gammaShapeThreeFredholmApprox (z : ℂ) (N : ℕ) : ℂ :=
  (1 + z • hilbertCompressionMatrix gammaShapeThreeHilbertBasis
    (gammaShapeThreeSquaredResolvent 1 (by norm_num)) N).det

theorem gamma_shape_three_fredholm_approx (z : ℂ) (N : ℕ) :
    gammaShapeThreeFredholmApprox z N = laguerreFredholmApprox z N := by
  rw [gammaShapeThreeFredholmApprox, gamma_shape_three_squared_resolvent_conjugate,
    gamma_shape_conjugate_compression_matrix]
  rfl

def gammaShapeThreeFredholmDeterminant (z : ℂ) : ℂ :=
  limUnder atTop (gammaShapeThreeFredholmApprox z)

theorem gamma_shape_three_fredholm_determinant (z : ℂ) :
    gammaShapeThreeFredholmDeterminant z = laguerreFredholmDeterminant z :=
  congrArg (limUnder atTop) (funext (gamma_shape_three_fredholm_approx z))

/-- The same det-times-exponential finite-compression regularization of the
actual first resolvent, without changing its convention. -/
def gammaShapeThreeRegularizedApprox (z : ℂ) (N : ℕ) : ℂ :=
  let M := hilbertCompressionMatrix gammaShapeThreeHilbertBasis
    (gammaShapeThreeResolvent 1 (by norm_num)) N
  (1 + z • M).det * Complex.exp (-z * M.trace)

theorem gamma_shape_three_regularized_approx (z : ℂ) (N : ℕ) :
    gammaShapeThreeRegularizedApprox z N = laguerreRegularizedApprox z N := by
  unfold gammaShapeThreeRegularizedApprox laguerreRegularizedApprox gammaShapeThreeResolvent
  rw [gamma_shape_conjugate_compression_matrix]

def gammaShapeThreeRegularizedDeterminant (z : ℂ) : ℂ :=
  limUnder atTop (gammaShapeThreeRegularizedApprox z)

theorem gamma_shape_three_regularized_determinant (z : ℂ) :
    gammaShapeThreeRegularizedDeterminant z = laguerreRegularizedDeterminant z :=
  congrArg (limUnder atTop) (funext (gamma_shape_three_regularized_approx z))

/-- The continued zeta function is identified by the genuine shifted traces
above; its derivative gives the same zeta regularization for every positive shift. -/
def gammaShapeThreeZetaDeterminant (a : ℝ) : ℂ :=
  Complex.exp (-deriv (laguerreHurwitzZeta a) 0)

theorem gamma_shape_three_zeta_determinant (a : ℝ) :
    gammaShapeThreeZetaDeterminant a = laguerreZetaDeterminant a := rfl

/-- The common continuation is attached to both genuine traces, is regular
at zero, and yields the same zeta-regularized determinant. -/
theorem gamma_shape_three_zeta_regularization (a : ℝ) (ha : 0 < a) :
    (∀ (s : ℂ) (hs : 1 < s.re),
      nuclearTrace (gammaShapeThreeShiftedZetaBoundedOperator a ha s hs)
        (gamma_shape_three_shifted_zeta_bounded_nuclear a ha s hs) = laguerreHurwitzZeta a s) ∧
    DifferentiableAt ℂ (laguerreHurwitzZeta a) 0 ∧
    gammaShapeThreeZetaDeterminant a = laguerreZetaDeterminant a := by
  refine ⟨?_, laguerre_hurwitz_zeta_regular_zero a ha, gamma_shape_three_zeta_determinant a⟩
  intro s hs
  rw [gamma_shape_three_shifted_zeta_trace a ha s hs, laguerre_shifted_zeta_trace a ha s hs]

end
end Sigma
