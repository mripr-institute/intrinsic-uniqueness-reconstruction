import SigmaMatrixGaussianMoments
import SigmaMatrixGaussianLikelihood

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped BigOperators ENNReal NNReal
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem matrix_gaussian_log_likelihood_ratio (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) (x : n → ℝ) :
    Real.log (matrixGaussianPDF X x / matrixGaussianPDF Y x) =
      (1/2 : ℝ)*(Real.log Y.det - Real.log X.det) +
      (1/2 : ℝ)*(dotProduct x (Y⁻¹ *ᵥ x) - dotProduct x (X⁻¹ *ᵥ x)) := by
  rw [Real.log_div (matrix_gaussian_pdf_pos X hX x).ne' (matrix_gaussian_pdf_pos Y hY x).ne',
    matrix_gaussian_log_density X hX, matrix_gaussian_log_density Y hY]
  ring

theorem matrix_gaussian_log_rn_derivative (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    (fun x => Real.log (((matrixGaussianMeasure X hX).rnDeriv (matrixGaussianMeasure Y hY) x).toReal))
      =ᵐ[matrixGaussianMeasure X hX] (fun x =>
        (1/2 : ℝ)*(Real.log Y.det - Real.log X.det) +
        (1/2 : ℝ)*(dotProduct x (Y⁻¹ *ᵥ x) - dotProduct x (X⁻¹ *ᵥ x))) := by
  have hh := rn_derivative_positive_densities volume (matrixGaussianPDF X) (matrixGaussianPDF Y)
    (matrix_gaussian_pdf_continuous X).measurable (matrix_gaussian_pdf_continuous Y).measurable
    (Eventually.of_forall fun x => (matrix_gaussian_pdf_pos X hX x).le)
    (Eventually.of_forall fun x => matrix_gaussian_pdf_pos Y hY x)
  rw [←matrix_gaussian_measure_density X hX, ←matrix_gaussian_measure_density Y hY] at hh
  filter_upwards [hh] with x hx
  rw [hx,matrix_gaussian_log_likelihood_ratio X Y hX hY]

theorem matrix_gaussian_relative_entropy_integrable (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    Integrable (fun x => Real.log (((matrixGaussianMeasure X hX).rnDeriv
      (matrixGaussianMeasure Y hY) x).toReal)) (matrixGaussianMeasure X hX) := by
  apply ((integrable_const ((1/2 : ℝ)*(Real.log Y.det - Real.log X.det))).add
    (((matrix_gaussian_quadratic_integrable X Y⁻¹ hX).sub
      (matrix_gaussian_quadratic_integrable X X⁻¹ hX)).const_mul (1/2 : ℝ))).congr
  exact (matrix_gaussian_log_rn_derivative X Y hX hY).symm

theorem matrix_gaussian_mutual_absolute_continuity (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    matrixGaussianMeasure X hX ≪ matrixGaussianMeasure Y hY ∧
      matrixGaussianMeasure Y hY ≪ matrixGaussianMeasure X hX := by
  rw [matrix_gaussian_measure_density X hX,matrix_gaussian_measure_density Y hY]
  exact ⟨positive_density_absolute_continuity _ _ _
      (matrix_gaussian_pdf_continuous Y).measurable (Eventually.of_forall fun x => matrix_gaussian_pdf_pos Y hY x),
    positive_density_absolute_continuity _ _ _
      (matrix_gaussian_pdf_continuous X).measurable (Eventually.of_forall fun x => matrix_gaussian_pdf_pos X hX x)⟩

/-- Actual multivariate Gaussian relative entropy, with the covariance order
`X || Y` matching the paper's oriented matrix divergence `D(X,Y)`. -/
theorem matrix_gaussian_relative_entropy (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    finiteRelativeEntropy (matrixGaussianMeasure X hX) (matrixGaussianMeasure Y hY) =
      (1/2 : ℝ)*matrixDivergence X Y := by
  have hi : Integrable (fun x : n → ℝ =>
      dotProduct x (Y⁻¹ *ᵥ x) - dotProduct x (X⁻¹ *ᵥ x)) (matrixGaussianMeasure X hX) :=
    (matrix_gaussian_quadratic_integrable X Y⁻¹ hX).sub
      (matrix_gaussian_quadratic_integrable X X⁻¹ hX)
  rw [finiteRelativeEntropy,integral_congr_ae (matrix_gaussian_log_rn_derivative X Y hX hY),
    integral_add (integrable_const _) (hi.const_mul _),
    integral_const,integral_mul_left,
    integral_sub (matrix_gaussian_quadratic_integrable X Y⁻¹ hX)
      (matrix_gaussian_quadratic_integrable X X⁻¹ hX),
    matrix_gaussian_quadratic_mean, matrix_gaussian_quadratic_mean,
    Matrix.nonsing_inv_mul X (isUnit_iff_ne_zero.mpr hX.det_pos.ne'),Matrix.trace_one]
  simp only [measure_univ,ENNReal.one_toReal,one_smul]
  unfold matrixDivergence
  rw [Matrix.det_mul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv,
    Real.log_mul (inv_ne_zero hY.det_pos.ne') hX.det_pos.ne',Real.log_inv]
  ring

theorem finite_iid_coordinate_integrable {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (f : E → ℝ) (hf : Integrable f μ) (i : ι) :
    Integrable (fun x : ι → E => f (x i)) (Measure.pi (fun _ : ι => μ)) := by
  letI : MeasureSpace E := ⟨μ⟩
  letI : IsProbabilityMeasure (volume : Measure E) := inferInstanceAs (IsProbabilityMeasure μ)
  have hi := Integrable.fintype_prod (fun k : ι => show
      Integrable (fun t : E => if k=i then f t else 1) from by
        by_cases hk : k=i
        · simpa only [if_pos hk] using hf
        · simp [hk])
  simpa using hi

theorem finite_iid_coordinate_integral {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (f : E → ℝ) (i : ι) :
    (∫ x : ι → E, f (x i) ∂Measure.pi (fun _ : ι => μ)) = ∫ t, f t ∂μ := by
  letI : MeasureSpace E := ⟨μ⟩
  letI : IsProbabilityMeasure (volume : Measure E) := inferInstanceAs (IsProbabilityMeasure μ)
  have hi := integral_fintype_prod_eq_prod ι (fun k t => if k=i then f t else 1)
  change (∫ x : ι → E, ∏ k, (if k=i then f (x k) else 1) ∂Measure.pi (fun _ : ι => μ)) =
    ∏ k : ι, ∫ t : E, (if k=i then f t else 1) ∂μ at hi
  have he (k : ι) : (∫ t : E, (if k=i then f t else 1) ∂μ) =
      if k=i then (∫ t, f t ∂μ) else 1 := by
    by_cases hk : k=i <;> simp [hk]
  simp only [he] at hi
  simpa using hi

theorem matrix_gaussian_log_density_ratio_integrable (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    Integrable (fun x => Real.log (matrixGaussianPDF X x / matrixGaussianPDF Y x))
      (matrixGaussianMeasure X hX) := by
  simp only [matrix_gaussian_log_likelihood_ratio X Y hX hY]
  exact (integrable_const _).add (((matrix_gaussian_quadratic_integrable X Y⁻¹ hX).sub
    (matrix_gaussian_quadratic_integrable X X⁻¹ hX)).const_mul _)

theorem matrix_gaussian_density_ratio_integral (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    (∫ x, Real.log (matrixGaussianPDF X x / matrixGaussianPDF Y x) ∂matrixGaussianMeasure X hX) =
      finiteRelativeEntropy (matrixGaussianMeasure X hX) (matrixGaussianMeasure Y hY) := by
  rw [finiteRelativeEntropy, integral_congr_ae (matrix_gaussian_log_rn_derivative X Y hX hY)]
  simp only [matrix_gaussian_log_likelihood_ratio X Y hX hY]

theorem matrix_gaussian_sample_log_rn_derivative (m : ℕ) (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    (fun Z => Real.log (((matrixGaussianSampleMeasure m X hX).rnDeriv
      (matrixGaussianSampleMeasure m Y hY) Z).toReal)) =ᵐ[matrixGaussianSampleMeasure m X hX]
      (fun Z => ∑ j : Fin m, Real.log (matrixGaussianPDF X (Z j) / matrixGaussianPDF Y (Z j))) := by
  have hm (A : Matrix n n ℝ) : Measurable (matrixGaussianSampleDensity m A) := by
    unfold matrixGaussianSampleDensity
    exact (continuous_finset_prod _ fun j _ =>
      (matrix_gaussian_pdf_continuous A).comp (continuous_apply j)).measurable
  have hh := rn_derivative_positive_densities volume (matrixGaussianSampleDensity m X)
    (matrixGaussianSampleDensity m Y) (hm X) (hm Y)
    (Eventually.of_forall fun Z => (matrix_gaussian_sample_density_positive m X hX Z).le)
    (Eventually.of_forall fun Z => matrix_gaussian_sample_density_positive m Y hY Z)
  rw [←matrix_gaussian_sample_measure_density m X hX,
    ←matrix_gaussian_sample_measure_density m Y hY] at hh
  filter_upwards [hh] with Z hZ
  rw [hZ,Real.log_div (matrix_gaussian_sample_density_positive m X hX Z).ne'
    (matrix_gaussian_sample_density_positive m Y hY Z).ne']
  unfold matrixGaussianSampleDensity
  rw [finite_iid_log_density _ (matrix_gaussian_pdf_pos X hX),
    finite_iid_log_density _ (matrix_gaussian_pdf_pos Y hY), ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact (Real.log_div (matrix_gaussian_pdf_pos X hX (Z j)).ne'
    (matrix_gaussian_pdf_pos Y hY (Z j)).ne').symm

theorem matrix_gaussian_sample_relative_entropy_integrable (m : ℕ) (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    Integrable (fun Z => Real.log (((matrixGaussianSampleMeasure m X hX).rnDeriv
      (matrixGaussianSampleMeasure m Y hY) Z).toReal)) (matrixGaussianSampleMeasure m X hX) := by
  have hi : Integrable (fun Z => ∑ j : Fin m,
      Real.log (matrixGaussianPDF X (Z j) / matrixGaussianPDF Y (Z j)))
      (matrixGaussianSampleMeasure m X hX) :=
    integrable_finset_sum _ fun j _ => finite_iid_coordinate_integrable _ _
      (matrix_gaussian_log_density_ratio_integrable X Y hX hY) j
  exact hi.congr (matrix_gaussian_sample_log_rn_derivative m X Y hX hY).symm

/-- The entropy of actual independent Gaussian samples is additive, including
the empty product; no likelihood-only proxy is used. -/
theorem matrix_gaussian_sample_relative_entropy (m : ℕ) (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    finiteRelativeEntropy (matrixGaussianSampleMeasure m X hX) (matrixGaussianSampleMeasure m Y hY) =
      (m : ℝ) * finiteRelativeEntropy (matrixGaussianMeasure X hX) (matrixGaussianMeasure Y hY) := by
  rw [finiteRelativeEntropy,integral_congr_ae (matrix_gaussian_sample_log_rn_derivative m X Y hX hY)]
  change (∫ Z : Fin m → n → ℝ, ∑ j : Fin m,
    Real.log (matrixGaussianPDF X (Z j) / matrixGaussianPDF Y (Z j))
      ∂Measure.pi (fun _ : Fin m => matrixGaussianMeasure X hX)) = _
  rw [integral_finset_sum _ (fun j _ => finite_iid_coordinate_integrable _ _
    (matrix_gaussian_log_density_ratio_integrable X Y hX hY) j)]
  have he (j : Fin m) := finite_iid_coordinate_integral (matrixGaussianMeasure X hX)
    (fun x => Real.log (matrixGaussianPDF X x / matrixGaussianPDF Y x)) j
  simp only [he,matrix_gaussian_density_ratio_integral X Y hX hY,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem matrix_gaussian_sample_relative_entropy_divergence (m : ℕ) (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    finiteRelativeEntropy (matrixGaussianSampleMeasure m X hX) (matrixGaussianSampleMeasure m Y hY) =
      (m : ℝ)/2 * matrixDivergence X Y := by
  rw [matrix_gaussian_sample_relative_entropy,matrix_gaussian_relative_entropy]
  ring

theorem matrix_gaussian_sample_mutual_absolute_continuity (m : ℕ) (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    matrixGaussianSampleMeasure m X hX ≪ matrixGaussianSampleMeasure m Y hY ∧
      matrixGaussianSampleMeasure m Y hY ≪ matrixGaussianSampleMeasure m X hX := by
  have hm (A : Matrix n n ℝ) : Measurable (matrixGaussianSampleDensity m A) := by
    unfold matrixGaussianSampleDensity
    exact (continuous_finset_prod _ fun j _ =>
      (matrix_gaussian_pdf_continuous A).comp (continuous_apply j)).measurable
  rw [matrix_gaussian_sample_measure_density m X hX,matrix_gaussian_sample_measure_density m Y hY]
  exact ⟨positive_density_absolute_continuity _ _ _ (hm Y)
      (Eventually.of_forall fun Z => matrix_gaussian_sample_density_positive m Y hY Z),
    positive_density_absolute_continuity _ _ _ (hm X)
      (Eventually.of_forall fun Z => matrix_gaussian_sample_density_positive m X hX Z)⟩

end
end Sigma
