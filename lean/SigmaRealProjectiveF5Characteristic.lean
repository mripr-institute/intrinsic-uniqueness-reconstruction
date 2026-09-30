import SigmaRealProjectiveSquareNativeTensor
import SigmaThomNativeTheory

namespace Sigma
noncomputable section

/-- In a rational ring, a square-one element with square-zero reduced part is
one. This is the algebraic step in the RP² Chern-character calculation. -/
theorem rational_square_one_of_square_zero {A : Type*} [CommRing A] [Algebra ℚ A]
    (x : A) (hsq : x ^ 2 = 1) (hreduced : (x - 1) ^ 2 = 0) : x = 1 := by
  have htwo : (2 : A) * (x - 1) = 0 := by
    calc
      (2 : A) * (x - 1) = (x ^ 2 - 1) - (x - 1) ^ 2 := by ring
      _ = 0 := by rw [hsq, hreduced]; ring
  have hhalf : algebraMap ℚ A (1 / 2) * (2 : A) = 1 := by
    rw [← map_ofNat (algebraMap ℚ A) 2, ← map_mul]
    norm_num
  have hzero : x - 1 = 0 := by
    calc
      x - 1 = (algebraMap ℚ A (1 / 2) * (2 : A)) * (x - 1) := by rw [hhalf, one_mul]
      _ = algebraMap ℚ A (1 / 2) * ((2 : A) * (x - 1)) := by ring
      _ = 0 := by rw [htwo, mul_zero]
  exact sub_eq_zero.mp hzero

/-- An additive invariant valued in a cancellative monoid detects inequality
after stabilization by any object. The actual determinant obstruction and
native K⁰ relation are developed in the later projective modules. -/
theorem not_stably_equivalent_of_cancellative_invariant
    {M N : Type*} [AddCommMonoid M] [AddCancelCommMonoid N]
    (δ : M →+ N) {a b : M} (hδ : δ a ≠ δ b) :
    ¬ ∃ e : M, a + e = b + e := by
  rintro ⟨e, he⟩
  apply hδ
  apply add_right_cancel (b := δ e)
  simpa only [map_add] using congrArg δ he

/-- A conditional algebraic helper with explicit RP² inputs: the K-class
of the complexified line squares to one, and its rational reduced Chern
character has square zero. The later SigmaRealProjectiveRationalCharacteristic
module proves the rational conclusion from native additive two-torsion,
without either of these RP²-specific assumptions. -/
theorem real_projective_chern_character_of_square_and_reduced_square_zero
    (T : SuppliedComplexThomTheory)
    (hsquare : (T.bundleClass realProjectiveComplexLine) ^ 2 = 1)
    (hreduced :
      (T.chBase realProjectiveComplexLine.base
        (T.bundleClass realProjectiveComplexLine) - 1) ^ 2 = 0) :
    T.chBase realProjectiveComplexLine.base
      (T.bundleClass realProjectiveComplexLine) = 1 := by
  have hcharsquare :
      (T.chBase realProjectiveComplexLine.base
        (T.bundleClass realProjectiveComplexLine)) ^ 2 = 1 := by
    rw [← map_pow, hsquare, map_one]
  exact rational_square_one_of_square_zero _ hcharsquare hreduced

/-- A candidate vector-bundle isomorphism over the fixed RP² base between
the complexified tautological line and its actual tensor square. -/
structure RealProjectiveComplexLineTensorSquareIsomorphism where
  totalHomeomorph : realProjectiveComplexCore.TotalSpace ≃ₜ
    RealProjectiveComplexTensorSquareTotalSpace
  fiberEquiv : ∀ p : RealProjectivePlane,
    realProjectiveComplexCore.Fiber p ≃ₗ[ℂ]
      RealProjectiveComplexTensorSquareFiber p
  total_apply : ∀ (p : RealProjectivePlane) (z : realProjectiveComplexCore.Fiber p),
    totalHomeomorph ⟨p, z⟩ = ⟨p, fiberEquiv p z⟩

private def realProjectiveTensorSquareFiberFinOneEquiv (p : RealProjectivePlane) :
    RealProjectiveComplexTensorSquareFiber p ≃ₗ[ℂ] (Fin 1 → ℂ) :=
  (real_projective_complex_tensor_square_native_trivialization_fiberwise_linear p).choose

private theorem real_projective_tensor_square_fiber_fin_one_apply
    (p : RealProjectivePlane) (w : RealProjectiveComplexTensorSquareFiber p) :
    realProjectiveComplexTensorSquareFinOneHomeomorph ⟨p, w⟩ =
      (p, realProjectiveTensorSquareFiberFinOneEquiv p w) :=
  (real_projective_complex_tensor_square_native_trivialization_fiberwise_linear p).choose_spec w

/-- The nontrivial complexified line cannot be isomorphic over the fixed base
to its trivial native tensor square. -/
theorem real_projective_complex_line_not_isomorphic_tensor_square :
    ¬ Nonempty RealProjectiveComplexLineTensorSquareIsomorphism := by
  rintro ⟨I⟩
  apply real_projective_complex_bundle_not_trivial
  refine ⟨{
    totalHomeomorph := I.totalHomeomorph.trans
      realProjectiveComplexTensorSquareFinOneHomeomorph
    fiberEquiv := fun p => (I.fiberEquiv p).trans
      (realProjectiveTensorSquareFiberFinOneEquiv p)
    total_apply := ?_ }⟩
  intro p z
  change realProjectiveComplexTensorSquareFinOneHomeomorph
    (I.totalHomeomorph ⟨p, z⟩) = _
  rw [I.total_apply, real_projective_tensor_square_fiber_fin_one_apply]
  rfl

/-- The fixed-base witness follows once the supplied K-class and rational
cohomology inputs identify both Chern characters with one. The native bundle
inequivalence is unconditional. -/
theorem real_projective_fixed_base_rational_characteristic_witness_of_inputs
    (T : SuppliedComplexThomTheory)
    (hsquare : (T.bundleClass realProjectiveComplexLine) ^ 2 = 1)
    (hreduced :
      (T.chBase realProjectiveComplexLine.base
        (T.bundleClass realProjectiveComplexLine) - 1) ^ 2 = 0)
    (htensor : T.chBase realProjectiveComplexTensorSquareNativeBundle.base
      (T.bundleClass realProjectiveComplexTensorSquareNativeBundle) = 1) :
    T.chBase realProjectiveComplexLine.base
      (T.bundleClass realProjectiveComplexLine) =
        T.chBase realProjectiveComplexTensorSquareNativeBundle.base
          (T.bundleClass realProjectiveComplexTensorSquareNativeBundle) ∧
      ¬ Nonempty RealProjectiveComplexLineTensorSquareIsomorphism := by
  constructor
  · rw [real_projective_chern_character_of_square_and_reduced_square_zero
      T hsquare hreduced, htensor]
  · exact real_projective_complex_line_not_isomorphic_tensor_square

end
end Sigma
