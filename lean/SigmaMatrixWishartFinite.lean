import SigmaMatrixGaussianLikelihood

namespace Sigma
noncomputable section
open MeasureTheory Set Matrix Filter
open scoped ENNReal NNReal
variable {n : Type*} [Fintype n] [DecidableEq n]

def matrixWishartPrecision (X Θ : Matrix n n ℝ) : Matrix n n ℝ := X⁻¹ - (2:ℝ) • Θ

theorem matrix_wishart_precision_trace (X Θ W : Matrix n n ℝ) :
    trace (matrixWishartPrecision X Θ * W) = trace (X⁻¹*W) - 2*trace (Θ*W) := by
  simp [matrixWishartPrecision, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub,
    Matrix.trace_smul]

theorem matrix_gaussian_sample_density_continuous (m : ℕ) (X : Matrix n n ℝ) :
    Continuous (matrixGaussianSampleDensity m X) := by
  unfold matrixGaussianSampleDensity
  apply continuous_finset_prod
  intro j _
  exact (matrix_gaussian_pdf_continuous X).comp (continuous_apply j)

omit [DecidableEq n] in
theorem matrix_trace_product_continuous (Θ : Matrix n n ℝ) :
    Continuous (fun W : Matrix n n ℝ => trace (Θ*W)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  fun_prop

def matrixWishartExponentialMoment (m : ℕ) (X : Matrix n n ℝ) (hX : X.PosDef)
    (Θ : Matrix n n ℝ) : ℝ≥0∞ :=
  ∫⁻ W, ENNReal.ofReal (Real.exp (trace (Θ*W))) ∂matrixWishartMeasure m X hX

theorem matrix_wishart_moment_on_samples (m : ℕ) (X : Matrix n n ℝ) (hX : X.PosDef)
    (Θ : Matrix n n ℝ) :
    matrixWishartExponentialMoment m X hX Θ =
      ∫⁻ Z, ENNReal.ofReal (Real.exp (trace (Θ*matrixSampleScatter Z)))
        ∂matrixGaussianSampleMeasure m X hX := by
  unfold matrixWishartExponentialMoment matrixWishartMeasure
  exact lintegral_map (matrix_trace_product_continuous Θ).rexp.measurable.ennreal_ofReal
    (matrix_sample_scatter_continuous m).measurable

theorem matrix_gaussian_sample_precision_tilt (m : ℕ) (X Θ : Matrix n n ℝ)
    (hX : X.PosDef) (hP : (matrixWishartPrecision X Θ).PosDef)
    (Z : Fin m → n → ℝ) :
    matrixGaussianSampleDensity m X Z * Real.exp (trace (Θ*matrixSampleScatter Z)) =
      Real.exp ((m:ℝ)/2*(Real.log (matrixWishartPrecision X Θ)⁻¹.det - Real.log X.det)) *
        matrixGaussianSampleDensity m (matrixWishartPrecision X Θ)⁻¹ Z := by
  have hdet : IsUnit (matrixWishartPrecision X Θ).det := isUnit_iff_ne_zero.mpr hP.det_pos.ne'
  have hlog : Real.log (matrixGaussianSampleDensity m X Z) + trace (Θ*matrixSampleScatter Z) =
      (m:ℝ)/2*(Real.log (matrixWishartPrecision X Θ)⁻¹.det - Real.log X.det) +
        Real.log (matrixGaussianSampleDensity m (matrixWishartPrecision X Θ)⁻¹ Z) := by
    rw [matrix_gaussian_sample_log_density m X hX,
      matrix_gaussian_sample_log_density m (matrixWishartPrecision X Θ)⁻¹ hP.inv,
      Matrix.nonsing_inv_nonsing_inv _ hdet, matrix_wishart_precision_trace]
    ring
  rw [← Real.exp_log (matrix_gaussian_sample_density_positive m X hX Z), ← Real.exp_add,
    ← Real.exp_log (matrix_gaussian_sample_density_positive m _ hP.inv Z), ← Real.exp_add, hlog]

/-- Actual extended expectation on the full positive-definite precision domain. -/
theorem matrix_wishart_moment_precision (m : ℕ) (X Θ : Matrix n n ℝ)
    (hX : X.PosDef) (hP : (matrixWishartPrecision X Θ).PosDef) :
    matrixWishartExponentialMoment m X hX Θ =
      ENNReal.ofReal (Real.exp ((m:ℝ)/2*
        (Real.log (matrixWishartPrecision X Θ)⁻¹.det - Real.log X.det))) := by
  rw [matrix_wishart_moment_on_samples, matrix_gaussian_sample_measure_density]
  have hg : Measurable (fun Z : Fin m → n → ℝ =>
      ENNReal.ofReal (Real.exp (trace (Θ*matrixSampleScatter Z)))) :=
    ((matrix_trace_product_continuous Θ).comp
      (matrix_sample_scatter_continuous m)).rexp.measurable.ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _
    (matrix_gaussian_sample_density_continuous m X).measurable.ennreal_ofReal hg]
  have he : (fun Z : Fin m → n → ℝ =>
      ENNReal.ofReal (matrixGaussianSampleDensity m X Z) *
        ENNReal.ofReal (Real.exp (trace (Θ*matrixSampleScatter Z)))) =
      fun Z => ENNReal.ofReal (Real.exp ((m:ℝ)/2*
        (Real.log (matrixWishartPrecision X Θ)⁻¹.det - Real.log X.det))) *
        ENNReal.ofReal (matrixGaussianSampleDensity m (matrixWishartPrecision X Θ)⁻¹ Z) := by
    ext Z
    rw [← ENNReal.ofReal_mul (matrix_gaussian_sample_density_positive m X hX Z).le,
      matrix_gaussian_sample_precision_tilt m X Θ hX hP,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
  change (∫⁻ Z, ENNReal.ofReal (matrixGaussianSampleDensity m X Z) *
    ENNReal.ofReal (Real.exp (trace (Θ*matrixSampleScatter Z)))) = _
  rw [he, lintegral_const_mul _
    (matrix_gaussian_sample_density_continuous m (matrixWishartPrecision X Θ)⁻¹).measurable.ennreal_ofReal]
  have hi : (∫⁻ Z, ENNReal.ofReal (matrixGaussianSampleDensity m (matrixWishartPrecision X Θ)⁻¹ Z)) = 1 := by
    have hh := measure_univ (μ := matrixGaussianSampleMeasure m (matrixWishartPrecision X Θ)⁻¹ hP.inv)
    rw [matrix_gaussian_sample_measure_density, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] at hh
    exact hh
  rw [hi, mul_one]

/-- The exact matrix appearing in the paper's Wishart transform domain. -/
def matrixWishartDomain (X Θ : Matrix n n ℝ) (hX : X.PosDef) : Matrix n n ℝ :=
  1 - (2:ℝ) • (hX.posSemidef.sqrt * Θ * hX.posSemidef.sqrt)

theorem matrix_wishart_domain_congruence (X Θ : Matrix n n ℝ) (hX : X.PosDef) :
    matrixWishartDomain X Θ hX =
      hX.posSemidef.sqrt * matrixWishartPrecision X Θ * hX.posSemidef.sqrt := by
  let Q := hX.posSemidef.sqrt
  have hQd := (Matrix.isUnit_iff_isUnit_det Q).mp (sqrt_positive_definite_isUnit X hX)
  have hsq : Q*Q = X := hX.posSemidef.sqrt_mul_self
  have hw : Q*X⁻¹*Q = 1 := by
    rw [← hsq, Matrix.mul_inv_rev, ← Matrix.mul_assoc Q Q⁻¹,
      Matrix.mul_nonsing_inv Q hQd, Matrix.one_mul, Matrix.nonsing_inv_mul Q hQd]
  change 1-(2:ℝ) • (Q*Θ*Q) = Q*(X⁻¹-(2:ℝ) • Θ)*Q
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hw]

theorem matrix_wishart_domain_positive_iff (X Θ : Matrix n n ℝ) (hX : X.PosDef) :
    (matrixWishartDomain X Θ hX).PosDef ↔ (matrixWishartPrecision X Θ).PosDef := by
  let Q := hX.posSemidef.sqrt
  have hQ := sqrt_positive_definite_isUnit X hX
  have hQd := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have hQt : Qᴴ = Q := hX.posSemidef.posSemidef_sqrt.isHermitian.eq
  have hQit : Q⁻¹ᴴ = Q⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hQt]
  rw [matrix_wishart_domain_congruence]
  change (Q*matrixWishartPrecision X Θ*Q).PosDef ↔ _
  constructor
  · intro h
    have hh := positive_definite_congruence _ Q⁻¹ h (Matrix.isUnit_nonsing_inv_iff.mpr hQ)
    rw [hQit] at hh
    have he : Q⁻¹*(Q*matrixWishartPrecision X Θ*Q)*Q⁻¹ = matrixWishartPrecision X Θ := by
      calc
        _ = (Q⁻¹*Q)*matrixWishartPrecision X Θ*(Q*Q⁻¹) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [Matrix.nonsing_inv_mul Q hQd, Matrix.mul_nonsing_inv Q hQd]; simp
    rwa [he] at hh
  · intro h
    have hh := positive_definite_congruence _ Q h hQ
    rwa [hQt] at hh

theorem matrix_wishart_domain_determinant (X Θ : Matrix n n ℝ) (hX : X.PosDef) :
    (matrixWishartDomain X Θ hX).det = X.det * (matrixWishartPrecision X Θ).det := by
  rw [matrix_wishart_domain_congruence, Matrix.det_mul, Matrix.det_mul]
  have h := congrArg Matrix.det hX.posSemidef.sqrt_mul_self
  rw [Matrix.det_mul] at h
  rw [← h]
  ring

/-- The finite Wishart MGF with exactly the displayed symmetric-square-root
domain matrix; no scalarized substitute for the actual expectation is used. -/
theorem matrix_wishart_moment_finite (m : ℕ) (X Θ : Matrix n n ℝ) (hX : X.PosDef)
    (hB : (matrixWishartDomain X Θ hX).PosDef) :
    matrixWishartExponentialMoment m X hX Θ =
      ENNReal.ofReal ((matrixWishartDomain X Θ hX).det ^ (-(m:ℝ)/2)) := by
  have hP := (matrix_wishart_domain_positive_iff X Θ hX).mp hB
  rw [matrix_wishart_moment_precision m X Θ hX hP,
    Real.rpow_def_of_pos hB.det_pos, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.log_inv,
    matrix_wishart_domain_determinant, Real.log_mul hX.det_pos.ne' hP.det_pos.ne']
  congr 2
  ring

end
end Sigma
