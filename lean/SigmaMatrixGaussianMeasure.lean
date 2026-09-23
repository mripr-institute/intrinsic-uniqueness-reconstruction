import SigmaProbGaussianEntropy
import SigmaMatrixSymmetrization
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import SigmaMatrixGaussianProduct

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped BigOperators ENNReal NNReal
variable {n : Type*} [Fintype n]

def standardMatrixGaussianPDF (x : n → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal 0 1 (x i)

theorem standard_matrix_gaussian_pdf_pos (x : n → ℝ) :
    0 < standardMatrixGaussianPDF x := by
  apply Finset.prod_pos
  intro i hi
  exact gaussianPDFReal_pos _ _ _ (by norm_num)

theorem standard_matrix_gaussian_pdf_continuous :
    Continuous (standardMatrixGaussianPDF : (n → ℝ) → ℝ) := by
  unfold standardMatrixGaussianPDF
  unfold gaussianPDFReal
  fun_prop

theorem standard_matrix_gaussian_pdf_integral :
    (∫ x : n → ℝ, standardMatrixGaussianPDF x) = 1 := by
  change (∫ x : n → ℝ, ∏ i, gaussianPDFReal 0 1 (x i)) = 1
  rw [integral_fintype_prod_eq_prod]
  simp only [integral_gaussianPDFReal_eq_one 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    Finset.prod_const_one]

theorem standard_matrix_gaussian_pdf_integrable :
    Integrable (standardMatrixGaussianPDF : (n → ℝ) → ℝ) :=
  Integrable.of_integral_ne_zero (by rw [standard_matrix_gaussian_pdf_integral]; norm_num)

def standardMatrixGaussianMeasure (n : Type*) [Fintype n] : Measure (n → ℝ) :=
  volume.withDensity (fun x => ENNReal.ofReal (standardMatrixGaussianPDF x))

instance standard_matrix_gaussian_probability :
    IsProbabilityMeasure (standardMatrixGaussianMeasure n) := by
  constructor
  rw [standardMatrixGaussianMeasure, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [←ofReal_integral_eq_lintegral_ofReal standard_matrix_gaussian_pdf_integrable
    (Eventually.of_forall fun x => (standard_matrix_gaussian_pdf_pos x).le),
    standard_matrix_gaussian_pdf_integral]
  norm_num

theorem standard_matrix_gaussian_pdf_formula (x : n → ℝ) :
    standardMatrixGaussianPDF x = (Real.sqrt (2*Real.pi))^(-(Fintype.card n : ℤ)) *
      Real.exp (-(∑ i, (x i)^2)/2) := by
  simp only [standardMatrixGaussianPDF, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ←Real.exp_sum]
  rw [_root_.zpow_neg, zpow_natCast, inv_pow]
  congr 2
  simp only [←Finset.sum_div, Finset.sum_neg_distrib]

variable [DecidableEq n]

def matrixGaussianPDF (X : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  (Real.sqrt (2*Real.pi))^(-(Fintype.card n : ℤ)) * (Real.sqrt X.det)⁻¹ *
    Real.exp (-(dotProduct x (X⁻¹ *ᵥ x))/2)

theorem matrix_gaussian_pdf_pos (X : Matrix n n ℝ) (hX : X.PosDef) (x : n → ℝ) :
    0 < matrixGaussianPDF X x := by
  unfold matrixGaussianPDF
  exact mul_pos (mul_pos (zpow_pos (Real.sqrt_pos.2 (by positivity)) _)
    (inv_pos.2 (Real.sqrt_pos.2 hX.det_pos))) (Real.exp_pos _)

theorem matrix_gaussian_pdf_continuous (X : Matrix n n ℝ) : Continuous (matrixGaussianPDF X) := by
  unfold matrixGaussianPDF
  simp only [Matrix.mulVec, Matrix.dotProduct]
  fun_prop

/-- The square-root transformation is an actual invertible linear map. -/
def matrixGaussianSqrtEquiv (X : Matrix n n ℝ) (hX : X.PosDef) : (n → ℝ) ≃L[ℝ] (n → ℝ) :=
  (hX.posSemidef.sqrt.toLinearEquiv (Pi.basisFun ℝ n)
    ((Matrix.isUnit_iff_isUnit_det _).mp (sqrt_positive_definite_isUnit X hX))).toContinuousLinearEquiv

theorem matrix_gaussian_sqrt_equiv_apply (X : Matrix n n ℝ) (hX : X.PosDef) (x : n → ℝ) :
    matrixGaussianSqrtEquiv X hX x = hX.posSemidef.sqrt *ᵥ x := by
  rfl

theorem matrix_gaussian_sqrt_equiv_symm_apply (X : Matrix n n ℝ) (hX : X.PosDef) (x : n → ℝ) :
    (matrixGaussianSqrtEquiv X hX).symm x = hX.posSemidef.sqrt⁻¹ *ᵥ x := by
  rfl

/-- The centered Gaussian with supplied SPD covariance is defined by the
actual square-root pushforward, not by its relative entropy. -/
def matrixGaussianMeasure (X : Matrix n n ℝ) (hX : X.PosDef) : Measure (n → ℝ) :=
  (standardMatrixGaussianMeasure n).map (matrixGaussianSqrtEquiv X hX)

instance matrix_gaussian_probability (X : Matrix n n ℝ) (hX : X.PosDef) :
    IsProbabilityMeasure (matrixGaussianMeasure X hX) := by
  apply isProbabilityMeasure_map
  exact (matrixGaussianSqrtEquiv X hX).continuous.measurable.aemeasurable

theorem measurable_equiv_map_with_density {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (e : α ≃ᵐ β) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  have hh := setLIntegral_map hs (hf.comp e.symm.measurable) e.measurable (μ := μ)
  simp only [Function.comp_apply] at hh
  rw [hh]
  simp

theorem matrix_gaussian_sqrt_det_abs (X : Matrix n n ℝ) (hX : X.PosDef) :
    Real.sqrt X.det = |hX.posSemidef.sqrt.det| := by
  have h := congrArg Matrix.det hX.posSemidef.sqrt_mul_self
  rw [Matrix.det_mul] at h
  rw [←h, ←pow_two, Real.sqrt_sq_eq_abs]

theorem matrix_gaussian_inverse_sqrt_quadratic (X : Matrix n n ℝ) (hX : X.PosDef)
    (x : n → ℝ) :
    (∑ i, (hX.posSemidef.sqrt⁻¹ *ᵥ x) i ^ 2) = dotProduct x (X⁻¹ *ᵥ x) := by
  let Q := hX.posSemidef.sqrt
  have hQt : Qᵀ = Q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hX.posSemidef.posSemidef_sqrt.isHermitian.eq
  have hQit : Q⁻¹ᵀ = Q⁻¹ := by rw [Matrix.transpose_nonsing_inv, hQt]
  have hsq : Q⁻¹ * Q⁻¹ = X⁻¹ := by
    rw [←Matrix.mul_inv_rev, hX.posSemidef.sqrt_mul_self]
  change (∑ i, (Q⁻¹ *ᵥ x) i ^ 2) = _
  calc
    _ = dotProduct (Q⁻¹ *ᵥ x) (Q⁻¹ *ᵥ x) := by simp only [dotProduct,pow_two]
    _ = dotProduct (x ᵥ* Q⁻¹) (Q⁻¹ *ᵥ x) := by
      rw [←hQit, Matrix.vecMul_transpose, hQit]
    _ = dotProduct x (Q⁻¹ *ᵥ (Q⁻¹ *ᵥ x)) := (Matrix.dotProduct_mulVec _ _ _).symm
    _ = _ := by rw [Matrix.mulVec_mulVec, hsq]

theorem matrix_gaussian_density_sqrt_formula (X : Matrix n n ℝ) (hX : X.PosDef)
    (x : n → ℝ) :
    |hX.posSemidef.sqrt.det|⁻¹ *
      standardMatrixGaussianPDF ((matrixGaussianSqrtEquiv X hX).symm x) =
      matrixGaussianPDF X x := by
  rw [matrix_gaussian_sqrt_equiv_symm_apply, standard_matrix_gaussian_pdf_formula,
    matrix_gaussian_inverse_sqrt_quadratic X hX, ←matrix_gaussian_sqrt_det_abs X hX]
  unfold matrixGaussianPDF
  ring

theorem matrix_gaussian_measure_density (X : Matrix n n ℝ) (hX : X.PosDef) :
    matrixGaussianMeasure X hX =
      volume.withDensity (fun x => ENNReal.ofReal (matrixGaussianPDF X x)) := by
  let e := (matrixGaussianSqrtEquiv X hX).toHomeomorph.toMeasurableEquiv
  have he : (e : (n → ℝ) → (n → ℝ)) = Matrix.toLin' hX.posSemidef.sqrt := rfl
  have hdet : hX.posSemidef.sqrt.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (sqrt_positive_definite_isUnit X hX)).ne_zero
  have hvol : (volume : Measure (n → ℝ)).map e =
      ENNReal.ofReal |hX.posSemidef.sqrt.det|⁻¹ • volume := by
    rw [he]
    simpa only [abs_inv] using Real.map_matrix_volume_pi_eq_smul_volume_pi hdet
  change ((volume : Measure (n → ℝ)).withDensity
    (fun x => ENNReal.ofReal (standardMatrixGaussianPDF x))).map e = _
  rw [measurable_equiv_map_with_density _ e _
    standard_matrix_gaussian_pdf_continuous.measurable.ennreal_ofReal, hvol,
    withDensity_smul_measure, ←withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply congrArg (Measure.withDensity volume)
  funext x
  change ENNReal.ofReal |hX.posSemidef.sqrt.det|⁻¹ *
    ENNReal.ofReal (standardMatrixGaussianPDF (e.symm x)) = _
  rw [←ENNReal.ofReal_mul (by positivity)]
  congr 1
  exact matrix_gaussian_density_sqrt_formula X hX x

theorem matrix_gaussian_pdf_integrable (X : Matrix n n ℝ) (hX : X.PosDef) :
    Integrable (matrixGaussianPDF X) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (matrix_gaussian_pdf_continuous X).aestronglyMeasurable
    (Eventually.of_forall fun x => (matrix_gaussian_pdf_pos X hX x).le)).mp
  have h : (∫⁻ x, ENNReal.ofReal (matrixGaussianPDF X x)) = 1 := by
    rw [←setLIntegral_univ]
    rw [←withDensity_apply _ MeasurableSet.univ, ←matrix_gaussian_measure_density X hX]
    exact measure_univ
  rw [h]
  exact ENNReal.one_ne_top

theorem matrix_gaussian_pdf_integral (X : Matrix n n ℝ) (hX : X.PosDef) :
    (∫ x : n → ℝ, matrixGaussianPDF X x) = 1 := by
  have h := ofReal_integral_eq_lintegral_ofReal (matrix_gaussian_pdf_integrable X hX)
    (Eventually.of_forall fun x => (matrix_gaussian_pdf_pos X hX x).le)
  rw [←setLIntegral_univ] at h
  rw [←withDensity_apply _ MeasurableSet.univ, ←matrix_gaussian_measure_density X hX,
    measure_univ] at h
  have he := congrArg ENNReal.toReal h
  simpa [ENNReal.toReal_ofReal (integral_nonneg fun x => (matrix_gaussian_pdf_pos X hX x).le)] using he

omit [DecidableEq n] in
theorem standard_matrix_gaussian_measure_pi :
    standardMatrixGaussianMeasure n = Measure.pi (fun _ : n => gaussianReal 0 1) := by
  rw [standardMatrixGaussianMeasure]
  have h := finite_iid_density_measure (ι := n) (gaussianPDFReal 0 1)
    (integrable_gaussianPDFReal 0 1) (gaussianPDFReal_nonneg 0 1)
  simpa only [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : ℝ≥0) ≠ 0), gaussianPDF_def,
    standardMatrixGaussianPDF] using h.symm

theorem matrix_gaussian_log_density (X : Matrix n n ℝ) (hX : X.PosDef) (x : n → ℝ) :
    Real.log (matrixGaussianPDF X x) =
      -(Fintype.card n : ℝ)/2 * Real.log (2*Real.pi) -
      (1/2 : ℝ)*Real.log X.det - (1/2 : ℝ)*dotProduct x (X⁻¹ *ᵥ x) := by
  have hp : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hd : 0 < Real.sqrt X.det := Real.sqrt_pos.2 hX.det_pos
  rw [matrixGaussianPDF, Real.log_mul (mul_ne_zero (zpow_ne_zero _ hp.ne') (inv_ne_zero hd.ne'))
    (Real.exp_ne_zero _), Real.log_mul (zpow_ne_zero _ hp.ne') (inv_ne_zero hd.ne'),
    Real.log_zpow, Real.log_inv, Real.log_sqrt (by positivity),
    Real.log_sqrt hX.det_pos.le, Real.log_exp]
  push_cast
  ring

end
end Sigma
