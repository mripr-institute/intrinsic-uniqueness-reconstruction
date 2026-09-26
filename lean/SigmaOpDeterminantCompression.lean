import SigmaOpDeterminantPaper
import SigmaOpDeterminantUniform

namespace Sigma
noncomputable section
open scoped Topology BigOperators Classical
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual compression to an arbitrary finite orthonormal spectral subspace. -/
def determinantCompression (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) (F : Finset ι) :
    Matrix F F ℂ := fun i j => @inner ℂ H _ (b i) (T (b j))

def nativeDeterminantCompression (reg : Bool) (b : HilbertBasis ι ℂ H)
    (R : H →L[ℂ] H) (F : Finset ι) (z : ℂ) : ℂ := by
  classical
  exact if reg then
    (1+z • determinantCompression b R F).det *
      Complex.exp (-z * (determinantCompression b R F).trace)
  else (1+z • determinantCompression b (R^2) F).det

omit [CompleteSpace H] in
theorem determinant_compression_diagonal (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    (f : ι → ℂ) (hT : ∀ i, T (b i) = f i • b i) (F : Finset ι) :
    determinantCompression b T F = Matrix.diagonal (fun i : F => f i) := by
  classical
  ext i j
  simp only [determinantCompression, hT, inner_smul_right]
  rw [← b.repr_apply_apply, b.repr_self]
  by_cases h : i = j
  · subst j
    simp [Matrix.diagonal_apply, lp.single_apply_self]
  · have hij : (i : ι) ≠ (j : ι) := fun he => h (Subtype.ext he)
    simp [Matrix.diagonal_apply, h, lp.single_apply_ne _ _ _ hij]

theorem native_determinant_compression_product (reg : Bool)
    (b : HilbertBasis ι ℂ H) (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (hR : OpIsResolvent A 1 R)
    (hdom : ∀ i, b i ∈ A.domain)
    (ha : ∀ i, A ⟨b i, hdom i⟩ = (lam i : ℂ) • b i)
    (F : Finset ι) (z : ℂ) :
    nativeDeterminantCompression reg b R F z =
      ∏ i ∈ F, determinantFactor reg (z*shiftedDeterminantCoefficient reg (lam i)) := by
  classical
  have hfirst := determinant_compression_diagonal b R
    (fun i => (((1+lam i)⁻¹ : ℝ) : ℂ))
    (fun i => positive_shift_resolvent_eigenvector A R hR ⟨b i, hdom i⟩ _ (hlam i) (ha i)) F
  have hsecond := determinant_compression_diagonal b (R^2)
    (fun i => ((((1+lam i)⁻¹)^2 : ℝ) : ℂ))
    (fun i => positive_shift_resolvent_power_eigenvector A R hR ⟨b i, hdom i⟩ _ (hlam i) (ha i) 2) F
  have hmatrix (f : F → ℂ) : 1+z • Matrix.diagonal f = Matrix.diagonal (fun i => 1+z*f i) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
  cases reg
  · simp only [nativeDeterminantCompression, Bool.false_eq_true, if_false, hsecond, hmatrix,
      Matrix.det_diagonal, determinantFactor, shiftedDeterminantCoefficient]
    simpa only using (Finset.prod_coe_sort F (fun i =>
      1 + z * ((((1+lam i)⁻¹)^2 : ℝ) : ℂ)))
  · simp only [nativeDeterminantCompression, if_true, hfirst, hmatrix, Matrix.det_diagonal,
      Matrix.trace_diagonal, determinantFactor, shiftedDeterminantCoefficient]
    rw [Finset.mul_sum, Complex.exp_sum, ← Finset.prod_mul_distrib]
    simp only [neg_mul]
    simpa only using (Finset.prod_coe_sort F (fun i =>
      (1 + z * (((1+lam i)⁻¹ : ℝ) : ℂ)) * Complex.exp (-(z * (((1+lam i)⁻¹ : ℝ) : ℂ)))))

/-- Every complete spectral basis gives the same native determinant as the
locally uniform limit of actual finite-dimensional compression determinants. -/
theorem native_determinant_compressions_locally_uniform
    {A : H →ₗ.[ℂ] H} (hA : NativeShiftedDeterminantClass A) (reg : Bool)
    (b : HilbertBasis ι ℂ H) (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hdom : ∀ i, b i ∈ A.domain)
    (ha : ∀ i, A ⟨b i, hdom i⟩ = (lam i : ℂ) • b i) :
    TendstoLocallyUniformly (nativeDeterminantCompression reg b hA.resolvent)
      (nativeShiftedDeterminant hA reg) Filter.atTop := by
  rw [native_shifted_determinant_eq_spectral hA reg b lam hlam hdom ha]
  change TendstoLocallyUniformly (fun F z => nativeDeterminantCompression reg b hA.resolvent F z) _ _
  simp_rw [native_determinant_compression_product reg b lam hlam A hA.resolvent hA.inverse hdom ha]
  exact spectral_determinant_locally_uniform reg _
    (native_shifted_determinant_summable reg b lam hlam A hA.resolvent hA.inverse hdom ha hA.nuclear_square)

end
end Sigma
