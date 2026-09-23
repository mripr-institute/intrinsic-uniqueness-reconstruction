import SigmaMatrixLikelihood
import SigmaMatrixGaussianProduct
import SigmaMatrixGaussianMeasure

namespace Sigma
noncomputable section
open MeasureTheory Set Matrix Filter
open scoped ENNReal NNReal

/-- The quadratic term of the genuine sample density is the trace against the
actual outer-product scatter, for every finite sample including the empty one. -/
theorem matrix_sample_quadratic_trace {n : Type*} [Fintype n] [DecidableEq n]
    {m : ℕ} (P : Matrix n n ℝ) (Z : Fin m → n → ℝ) :
    (∑ j, dotProduct (Z j) (P *ᵥ Z j)) = trace (P * matrixSampleScatter Z) := by
  simp only [matrixSampleScatter, Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec,
    Matrix.of_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

variable {n : Type*} [Fintype n] [DecidableEq n]

instance matrix_real_measurable_space : MeasurableSpace (Matrix n n ℝ) :=
  inferInstanceAs (MeasurableSpace (n → n → ℝ))

instance matrix_real_borel_space : BorelSpace (Matrix n n ℝ) :=
  inferInstanceAs (BorelSpace (n → n → ℝ))

/-- The likelihood density of the actual iid sampling model. -/
def matrixGaussianSampleDensity (m : ℕ) (X : Matrix n n ℝ) (Z : Fin m → n → ℝ) : ℝ :=
  ∏ j, matrixGaussianPDF X (Z j)

def matrixGaussianSampleMeasure (m : ℕ) (X : Matrix n n ℝ) (hX : X.PosDef) :
    Measure (Fin m → n → ℝ) := Measure.pi (fun _ => matrixGaussianMeasure X hX)

instance matrix_gaussian_sample_probability (m : ℕ) (X : Matrix n n ℝ) (hX : X.PosDef) :
    IsProbabilityMeasure (matrixGaussianSampleMeasure m X hX) := by
  unfold matrixGaussianSampleMeasure
  infer_instance

theorem matrix_gaussian_sample_density_positive (m : ℕ) (X : Matrix n n ℝ) (hX : X.PosDef)
    (Z : Fin m → n → ℝ) : 0 < matrixGaussianSampleDensity m X Z :=
  Finset.prod_pos (fun j _ => matrix_gaussian_pdf_pos X hX (Z j))

theorem matrix_gaussian_sample_measure_density (m : ℕ) (X : Matrix n n ℝ) (hX : X.PosDef) :
    matrixGaussianSampleMeasure m X hX =
      volume.withDensity (fun Z => ENNReal.ofReal (matrixGaussianSampleDensity m X Z)) := by
  unfold matrixGaussianSampleMeasure matrixGaussianSampleDensity
  simp_rw [matrix_gaussian_measure_density X hX]
  exact finite_iid_density_measure (matrixGaussianPDF X) (matrix_gaussian_pdf_integrable X hX)
    (fun x => (matrix_gaussian_pdf_pos X hX x).le)

/-- The displayed log-likelihood, with its explicit parameter-independent
normalization constant, is derived from the native iid Gaussian density. -/
theorem matrix_gaussian_sample_log_density (m : ℕ) (X : Matrix n n ℝ) (hX : X.PosDef)
    (Z : Fin m → n → ℝ) :
    Real.log (matrixGaussianSampleDensity m X Z) =
      -(m:ℝ)/2*Real.log X.det - (1/2:ℝ)*trace (X⁻¹ * matrixSampleScatter Z) -
        (m:ℝ)*(Fintype.card n:ℝ)/2*Real.log (2*Real.pi) := by
  unfold matrixGaussianSampleDensity
  rw [finite_iid_log_density _ (matrix_gaussian_pdf_pos X hX)]
  simp_rw [matrix_gaussian_log_density X hX, Finset.sum_sub_distrib,
    ← Finset.mul_sum, matrix_sample_quadratic_trace]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem matrix_gaussian_sample_log_objective (m : ℕ) (X : Matrix n n ℝ) (hX : X.PosDef)
    (Z : Fin m → n → ℝ) :
    -Real.log (matrixGaussianSampleDensity m X Z) =
      matrixScatterNegLogLikelihood m (matrixSampleScatter Z) X +
        (m:ℝ)*(Fintype.card n:ℝ)/2*Real.log (2*Real.pi) := by
  rw [matrix_gaussian_sample_log_density m X hX]
  unfold matrixScatterNegLogLikelihood
  ring

omit [Fintype n] [DecidableEq n] in
theorem matrix_sample_scatter_continuous (m : ℕ) :
    Continuous (matrixSampleScatter : (Fin m → n → ℝ) → Matrix n n ℝ) := by
  unfold matrixSampleScatter Matrix.vecMulVec
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  simp only [Matrix.sum_apply, Matrix.of_apply]
  fun_prop

/-- The Wishart measure is the actual scatter pushforward of the supplied
Gaussian iid model; this definition makes no transform or sufficiency claim. -/
def matrixWishartMeasure (m : ℕ) (X : Matrix n n ℝ) (hX : X.PosDef) : Measure (Matrix n n ℝ) :=
  (matrixGaussianSampleMeasure m X hX).map matrixSampleScatter

instance matrix_wishart_probability (m : ℕ) (X : Matrix n n ℝ) (hX : X.PosDef) :
    IsProbabilityMeasure (matrixWishartMeasure m X hX) :=
  isProbabilityMeasure_map (matrix_sample_scatter_continuous m).measurable.aemeasurable

theorem matrix_gaussian_iid_joint_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : ℕ) (X : Matrix n n ℝ) (hX : X.PosDef)
    (Z : Fin m → Ω → n → ℝ) (hZ : ∀ j, Measurable (Z j))
    (hind : ProbabilityTheory.iIndepFun (fun _ => inferInstance) Z μ)
    (hlaw : ∀ j, μ.map (Z j) = matrixGaussianMeasure X hX) :
    μ.map (fun ω j => Z j ω) = matrixGaussianSampleMeasure m X hX :=
  finite_independent_joint_law μ (matrixGaussianMeasure X hX) Z hZ hind hlaw

theorem matrix_gaussian_iid_scatter_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : ℕ) (X : Matrix n n ℝ) (hX : X.PosDef)
    (Z : Fin m → Ω → n → ℝ) (hZ : ∀ j, Measurable (Z j))
    (hind : ProbabilityTheory.iIndepFun (fun _ => inferInstance) Z μ)
    (hlaw : ∀ j, μ.map (Z j) = matrixGaussianMeasure X hX) :
    μ.map (fun ω => matrixSampleScatter (fun j => Z j ω)) = matrixWishartMeasure m X hX := by
  rw [matrixWishartMeasure, ← matrix_gaussian_iid_joint_law μ m X hX Z hZ hind hlaw,
    Measure.map_map (matrix_sample_scatter_continuous m).measurable (measurable_pi_lambda _ hZ)]
  rfl

theorem matrix_gaussian_log_likelihood_gap {m : ℕ} (hm : 0<m) (Z : Fin m → n → ℝ)
    (X : Matrix n n ℝ) (hC : (matrixSampleCovariance Z).PosDef) (hX : X.PosDef) :
    -Real.log (matrixGaussianSampleDensity m X Z) -
      (-Real.log (matrixGaussianSampleDensity m (matrixSampleCovariance Z) Z)) =
        (m:ℝ)/2*matrixDivergence (matrixSampleCovariance Z) X := by
  rw [matrix_gaussian_sample_log_objective m X hX,
    matrix_gaussian_sample_log_objective m (matrixSampleCovariance Z) hC]
  have h := matrix_sample_likelihood_gap hm Z X hC hX
  linarith

/-- Pointwise factorization of the actual sampling density through scatter. -/
theorem matrix_gaussian_sample_density_factorization (m : ℕ) (X : Matrix n n ℝ)
    (hX : X.PosDef) (Z : Fin m → n → ℝ) :
    matrixGaussianSampleDensity m X Z =
      Real.exp (-matrixScatterNegLogLikelihood m (matrixSampleScatter Z) X) *
        Real.exp (-(m:ℝ)*(Fintype.card n:ℝ)/2*Real.log (2*Real.pi)) := by
  rw [← Real.exp_add, ← Real.exp_log (matrix_gaussian_sample_density_positive m X hX Z)]
  congr 1
  have h := matrix_gaussian_sample_log_objective m X hX Z
  linarith

theorem matrix_gaussian_sample_density_eq_of_scatter_eq (m : ℕ) (X : Matrix n n ℝ)
    (hX : X.PosDef) (Z Y : Fin m → n → ℝ)
    (h : matrixSampleScatter Z = matrixSampleScatter Y) :
    matrixGaussianSampleDensity m X Z = matrixGaussianSampleDensity m X Y := by
  rw [matrix_gaussian_sample_density_factorization m X hX,
    matrix_gaussian_sample_density_factorization m X hX, h]

theorem matrix_gaussian_sample_density_le_iff (m : ℕ) (Z : Fin m → n → ℝ)
    (X Y : Matrix n n ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    matrixGaussianSampleDensity m X Z ≤ matrixGaussianSampleDensity m Y Z ↔
      matrixScatterNegLogLikelihood m (matrixSampleScatter Z) Y ≤
        matrixScatterNegLogLikelihood m (matrixSampleScatter Z) X := by
  rw [← Real.log_le_log_iff (matrix_gaussian_sample_density_positive m X hX Z)
    (matrix_gaussian_sample_density_positive m Y hY Z)]
  have hx := matrix_gaussian_sample_log_objective m X hX Z
  have hy := matrix_gaussian_sample_log_objective m Y hY Z
  constructor <;> intro h <;> linarith

/-- The MLE is now a maximizer of the actual iid Gaussian density, rather than
only a minimizer of an independently supplied deterministic objective. -/
theorem matrix_gaussian_sample_unique_mle {m : ℕ} (hm : 0<m) (Z : Fin m → n → ℝ)
    (hC : (matrixSampleCovariance Z).PosDef) :
    ∃! X : Matrix n n ℝ, X.PosDef ∧ ∀ Y : Matrix n n ℝ, Y.PosDef →
      matrixGaussianSampleDensity m Y Z ≤ matrixGaussianSampleDensity m X Z := by
  have hmin (Y : Matrix n n ℝ) (hY : Y.PosDef) :
      matrixScatterNegLogLikelihood m (matrixSampleScatter Z) (matrixSampleCovariance Z) ≤
        matrixScatterNegLogLikelihood m (matrixSampleScatter Z) Y := by
    rw [matrix_scatter_likelihood_covariance m hm, matrix_scatter_likelihood_covariance m hm]
    exact matrix_covariance_likelihood_minimum m (matrixSampleCovariance Z) Y hC hY
  refine ⟨matrixSampleCovariance Z, ⟨hC, fun Y hY => ?_⟩, ?_⟩
  · exact (matrix_gaussian_sample_density_le_iff m Z Y (matrixSampleCovariance Z) hY hC).mpr
      (hmin Y hY)
  · rintro X ⟨hX, hmax⟩
    have hle := (matrix_gaussian_sample_density_le_iff m Z (matrixSampleCovariance Z) X hC hX).mp
      (hmax _ hC)
    have he := le_antisymm hle (hmin X hX)
    rw [matrix_scatter_likelihood_covariance m hm, matrix_scatter_likelihood_covariance m hm] at he
    exact (matrix_covariance_likelihood_equality_iff m hm (matrixSampleCovariance Z) X hC hX).mp he

theorem matrix_gaussian_singular_sample_no_mle {m : ℕ} (hm : 0<m) (Z : Fin m → n → ℝ)
    (hs : (matrixSampleCovariance Z).det = 0) :
    ¬∃ X : Matrix n n ℝ, X.PosDef ∧ ∀ Y : Matrix n n ℝ, Y.PosDef →
      matrixGaussianSampleDensity m Y Z ≤ matrixGaussianSampleDensity m X Z := by
  rintro ⟨X,hX,hmax⟩
  apply matrix_singular_sample_no_mle hm Z hs
  exact ⟨X,hX,fun Y hY => (matrix_gaussian_sample_density_le_iff m Z Y X hY hX).mp (hmax Y hY)⟩

end
end Sigma
