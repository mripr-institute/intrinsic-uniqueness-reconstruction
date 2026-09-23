import SigmaStatisticSufficiency
import SigmaMatrixWishartFinite

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set
open scoped ENNReal ComplexOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

def matrixScatterDensityTilt (m : ℕ) (X Y W : Matrix n n ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp
    (matrixScatterNegLogLikelihood m W Y - matrixScatterNegLogLikelihood m W X))

theorem matrix_scatter_density_tilt_measurable (m : ℕ) (X Y : Matrix n n ℝ) :
    Measurable (matrixScatterDensityTilt m X Y) := by
  have hc (P : Matrix n n ℝ) : Continuous (fun W => matrixScatterNegLogLikelihood m W P) :=
    continuous_const.add (continuous_const.mul (matrix_trace_product_continuous P⁻¹))
  exact ((hc Y).sub (hc X)).rexp.measurable.ennreal_ofReal

theorem matrix_gaussian_sample_density_tilt (m : ℕ) (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) (Z : Fin m → n → ℝ) :
    ENNReal.ofReal (matrixGaussianSampleDensity m Y Z) *
      matrixScatterDensityTilt m X Y (matrixSampleScatter Z) =
        ENNReal.ofReal (matrixGaussianSampleDensity m X Z) := by
  rw [matrixScatterDensityTilt, ← ENNReal.ofReal_mul
    (matrix_gaussian_sample_density_positive m Y hY Z).le]
  congr 1
  rw [matrix_gaussian_sample_density_factorization m Y hY,
    matrix_gaussian_sample_density_factorization m X hX]
  simp only [← Real.exp_add]
  congr 1
  ring

theorem matrix_gaussian_sample_measure_tilt (m : ℕ) (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    matrixGaussianSampleMeasure m X hX =
      (matrixGaussianSampleMeasure m Y hY).withDensity
        (fun Z => matrixScatterDensityTilt m X Y (matrixSampleScatter Z)) := by
  have hm : Measurable (fun Z : Fin m → n → ℝ =>
      matrixScatterDensityTilt m X Y (matrixSampleScatter Z)) :=
    (matrix_scatter_density_tilt_measurable m X Y).comp
      (matrix_sample_scatter_continuous m).measurable
  rw [matrix_gaussian_sample_measure_density m X hX,
    matrix_gaussian_sample_measure_density m Y hY,
    ← withDensity_mul volume (matrix_gaussian_sample_density_continuous m Y).measurable.ennreal_ofReal
      hm]
  congr 1
  funext Z
  exact (matrix_gaussian_sample_density_tilt m X Y hX hY Z).symm

/-- Statistical sufficiency of the actual scatter: one parameter-independent
Markov kernel is a regular conditional law of the entire Gaussian sample
given its scatter, simultaneously for every positive-definite covariance. -/
theorem matrix_gaussian_scatter_sufficient (m : ℕ) :
    HasCommonStatisticKernel
      (fun X : {X : Matrix n n ℝ // X.PosDef} => matrixGaussianSampleMeasure m X.val X.property)
      matrixSampleScatter := by
  have h := common_statistic_kernel_of_tilts
    (matrixGaussianSampleMeasure m (1 : Matrix n n ℝ) Matrix.PosDef.one)
    matrixSampleScatter (matrix_sample_scatter_continuous m).measurable
    (fun X : {X : Matrix n n ℝ // X.PosDef} => matrixScatterDensityTilt m X.val 1)
    (fun X => matrix_scatter_density_tilt_measurable m X.val 1)
  have he : (fun X : {X : Matrix n n ℝ // X.PosDef} =>
      (matrixGaussianSampleMeasure m (1 : Matrix n n ℝ) Matrix.PosDef.one).withDensity
        (fun Z => matrixScatterDensityTilt m X.val 1 (matrixSampleScatter Z))) =
      fun X : {X : Matrix n n ℝ // X.PosDef} => matrixGaussianSampleMeasure m X.val X.property := by
    funext X
    exact (matrix_gaussian_sample_measure_tilt m X.val 1 X.property Matrix.PosDef.one).symm
  rw [he] at h
  exact h

end
end Sigma
