import SigmaMatrixWishartFinite
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace Sigma
noncomputable section
open MeasureTheory Set Matrix Filter
open scoped ENNReal NNReal

/-- A nowhere-zero product density cannot conceal a nonintegrable coordinate.
The conclusion is derived by actual product-measure Fubini slices. -/
theorem integrable_finite_product_factor {ι E : Type*} [Fintype ι]
    [TopologicalSpace E] [MeasureSpace E] [Nonempty E]
    [SigmaFinite (volume : Measure E)] [Measure.IsOpenPosMeasure (volume : Measure E)]
    (f : ι → E → ℝ) (hf : ∀ i x, f i x ≠ 0)
    (h : Integrable (fun x : ι → E => ∏ i, f i (x i))) (j : ι) : Integrable (f j) := by
  classical
  let p : ι → Prop := fun i => i=j
  letI : Unique {i : ι // p i} := ⟨⟨j,rfl⟩,fun i => Subtype.eq i.2⟩
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => E) p
  have he := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => E) p
  have hi := ((MeasurePreserving.symm e he).integrable_comp_emb e.symm.measurableEmbedding).mpr h
  obtain ⟨y,hy⟩ := hi.prod_left_ae.exists
  let c : ℝ := ∏ i : {i : ι // ¬p i}, f i (y i)
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hf i (y i))
  have hfun : (fun x : {i : ι // p i} → E => (fun z : ι → E => ∏ i, f i (z i)) (e.symm (x,y))) =
      fun x => f j (x default) * c := by
    ext x
    change (∏ i, f i (e.symm (x,y) i)) = _
    rw [← Fintype.prod_subtype_mul_prod_subtype p]
    simp only [Fintype.prod_unique]
    have hd : ((default : {i : ι // p i}):ι)=j := (default : {i : ι // p i}).2
    simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
      p, c, hd, show ∀ i : {i : ι // i≠j}, ¬(i:ι)=j from fun i => i.2]
    left
    congr 2
  have hy' : Integrable (fun x : {i : ι // p i} → E => f j (x default) * c) := by
    convert hy using 1
    · exact hfun.symm
    · simp only [volume_pi]
      congr 1
      exact Subsingleton.elim _ _
  rw [integrable_mul_const_iff (isUnit_iff_ne_zero.mpr hc)] at hy'
  exact ((volume_preserving_funUnique {i : ι // p i} E).integrable_comp_emb
    (MeasurableEquiv.funUnique _ _).measurableEmbedding).mp hy'

variable {n : Type*} [Fintype n] [DecidableEq n]

def matrixQuadraticGaussian (B : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  Real.exp (-dotProduct x (B *ᵥ x)/2)

omit [DecidableEq n] in
theorem matrix_quadratic_gaussian_continuous (B : Matrix n n ℝ) :
    Continuous (matrixQuadraticGaussian B) := by
  unfold matrixQuadraticGaussian
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

theorem real_unitary_abs_det (U : Matrix.unitaryGroup n ℝ) :
    |(U:Matrix n n ℝ).det| = 1 := by
  have h := congrArg Matrix.det (unitary.coe_mul_star_self U)
  rw [unitary.coe_star] at h
  have hs : (U:Matrix n n ℝ).det^2 = 1 := by
    simpa only [Matrix.det_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.det_transpose, Matrix.det_one, pow_two] using h
  rw [← Real.sqrt_sq_eq_abs, hs, Real.sqrt_one]

def realUnitaryLinearEquiv (U : Matrix.unitaryGroup n ℝ) : (n → ℝ) ≃L[ℝ] (n → ℝ) :=
  ((U:Matrix n n ℝ).toLinearEquiv (Pi.basisFun ℝ n)
    ((Matrix.isUnit_iff_isUnit_det _).mp (unitary.toUnits U).isUnit)).toContinuousLinearEquiv

theorem real_unitary_linear_equiv_volume (U : Matrix.unitaryGroup n ℝ) :
    MeasurePreserving (realUnitaryLinearEquiv U) := by
  refine ⟨(realUnitaryLinearEquiv U).continuous.measurable, ?_⟩
  have hd : (U:Matrix n n ℝ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (unitary.toUnits U).isUnit).ne_zero
  change (volume : Measure (n → ℝ)).map (Matrix.toLin' (U:Matrix n n ℝ)) = volume
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hd]
  simp [abs_inv, real_unitary_abs_det]

theorem matrix_quadratic_eigenbasis (B : Matrix n n ℝ) (hB : B.IsHermitian) (x : n → ℝ) :
    dotProduct (realUnitaryLinearEquiv hB.eigenvectorUnitary x)
      (B *ᵥ realUnitaryLinearEquiv hB.eigenvectorUnitary x) = ∑ i, hB.eigenvalues i * (x i)^2 := by
  let U := (hB.eigenvectorUnitary : Matrix n n ℝ)
  have he : Uᵀ*B*U = Matrix.diagonal hB.eigenvalues := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id, Function.comp_id, Function.id_comp] using hB.star_mul_self_mul_eq_diagonal
  change dotProduct (U *ᵥ x) (B *ᵥ (U *ᵥ x)) = _
  calc
    _ = dotProduct (x ᵥ* Uᵀ) (B *ᵥ (U *ᵥ x)) := by rw [Matrix.vecMul_transpose]
    _ = dotProduct x ((Uᵀ*B*U) *ᵥ x) := by
      rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = _ := by
      rw [he]
      simp only [dotProduct, Matrix.mulVec_diagonal]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Every zero or negative spectral direction forces nonintegrability of the
actual Euclidean quadratic exponential, including a singular boundary. -/
theorem matrix_quadratic_gaussian_not_integrable (B : Matrix n n ℝ)
    (hB : B.IsHermitian) (hn : ¬B.PosDef) : ¬Integrable (matrixQuadraticGaussian B) := by
  intro hi
  obtain ⟨j,hj⟩ := hermitian_nonpositive_eigenvalue B hB hn
  have ht := ((real_unitary_linear_equiv_volume hB.eigenvectorUnitary).integrable_comp_emb
    (realUnitaryLinearEquiv hB.eigenvectorUnitary).toHomeomorph.measurableEmbedding).mpr hi
  have hp : Integrable (fun x : n → ℝ => ∏ i, Real.exp (-(hB.eigenvalues i/2)*(x i)^2)) := by
    convert ht using 1
    ext x
    change (∏ i, Real.exp (-(hB.eigenvalues i/2)*(x i)^2)) =
      Real.exp (-dotProduct (realUnitaryLinearEquiv hB.eigenvectorUnitary x)
        (B *ᵥ realUnitaryLinearEquiv hB.eigenvectorUnitary x)/2)
    rw [matrix_quadratic_eigenbasis, ← Real.exp_sum]
    congr 1
    simp only [neg_div, neg_mul, div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_neg_distrib]
  have hf := integrable_finite_product_factor
    (fun (i : n) (t : ℝ) => Real.exp (-(hB.eigenvalues i/2)*t^2))
    (fun _ _ => Real.exp_ne_zero _) hp j
  have hh := integrable_exp_neg_mul_sq_iff.mp hf
  linarith

theorem matrix_quadratic_gaussian_lintegral_infinite (B : Matrix n n ℝ)
    (hB : B.IsHermitian) (hn : ¬B.PosDef) :
    (∫⁻ x : n → ℝ, ENNReal.ofReal (matrixQuadraticGaussian B x)) = ∞ := by
  by_contra h
  apply matrix_quadratic_gaussian_not_integrable B hB hn
  refine ⟨(matrix_quadratic_gaussian_continuous B).measurable.aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => (Real.exp_pos _).le)).mpr
    (lt_top_iff_ne_top.mpr h)

def matrixGaussianNormalizer (X : Matrix n n ℝ) : ℝ :=
  (Real.sqrt (2*Real.pi))^(-(Fintype.card n : ℤ)) * (Real.sqrt X.det)⁻¹

theorem matrix_gaussian_normalizer_positive (X : Matrix n n ℝ) (hX : X.PosDef) :
    0 < matrixGaussianNormalizer X := by
  unfold matrixGaussianNormalizer
  exact mul_pos (zpow_pos (Real.sqrt_pos.2 (by positivity)) _)
    (inv_pos.2 (Real.sqrt_pos.2 hX.det_pos))

theorem matrix_gaussian_quadratic_tilt (X Θ : Matrix n n ℝ) (x : n → ℝ) :
    matrixGaussianPDF X x * Real.exp (dotProduct x (Θ *ᵥ x)) =
      matrixGaussianNormalizer X * matrixQuadraticGaussian (matrixWishartPrecision X Θ) x := by
  unfold matrixGaussianPDF matrixGaussianNormalizer matrixQuadraticGaussian
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  simp only [matrixWishartPrecision, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
    Matrix.dotProduct_sub, Matrix.dotProduct_smul, smul_eq_mul]
  ring

theorem matrix_gaussian_sample_quadratic_tilt (m : ℕ) (X Θ : Matrix n n ℝ)
    (Z : Fin m → n → ℝ) :
    matrixGaussianSampleDensity m X Z * Real.exp (trace (Θ*matrixSampleScatter Z)) =
      (matrixGaussianNormalizer X)^m * ∏ j, matrixQuadraticGaussian (matrixWishartPrecision X Θ) (Z j) := by
  rw [← matrix_sample_quadratic_trace, Real.exp_sum]
  unfold matrixGaussianSampleDensity
  rw [← Finset.prod_mul_distrib]
  simp_rw [matrix_gaussian_quadratic_tilt]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem matrix_wishart_moment_as_quadratic (m : ℕ) (X Θ : Matrix n n ℝ) (hX : X.PosDef) :
    matrixWishartExponentialMoment m X hX Θ =
      ∫⁻ Z : Fin m → n → ℝ, ENNReal.ofReal ((matrixGaussianNormalizer X)^m *
        ∏ j, matrixQuadraticGaussian (matrixWishartPrecision X Θ) (Z j)) := by
  rw [matrix_wishart_moment_on_samples, matrix_gaussian_sample_measure_density]
  have hg : Measurable (fun Z : Fin m → n → ℝ =>
      ENNReal.ofReal (Real.exp (trace (Θ*matrixSampleScatter Z)))) :=
    ((matrix_trace_product_continuous Θ).comp
      (matrix_sample_scatter_continuous m)).rexp.measurable.ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _
    (matrix_gaussian_sample_density_continuous m X).measurable.ennreal_ofReal hg]
  apply lintegral_congr
  intro Z
  change ENNReal.ofReal (matrixGaussianSampleDensity m X Z) *
    ENNReal.ofReal (Real.exp (trace (Θ*matrixSampleScatter Z))) = _
  rw [← ENNReal.ofReal_mul (matrix_gaussian_sample_density_positive m X hX Z).le,
    matrix_gaussian_sample_quadratic_tilt]

/-- The extended expectation really diverges whenever the symmetric precision
has any nonpositive eigenvalue; no finiteness-domain premise is assumed. -/
theorem matrix_wishart_moment_infinite_precision (m : ℕ) (hm : 0<m)
    (X Θ : Matrix n n ℝ) (hX : X.PosDef) (hΘ : Θ.IsHermitian)
    (hn : ¬(matrixWishartPrecision X Θ).PosDef) :
    matrixWishartExponentialMoment m X hX Θ = ∞ := by
  by_contra h
  rw [matrix_wishart_moment_as_quadratic] at h
  have hnrm := matrix_gaussian_normalizer_positive X hX
  have hcont : Continuous (fun Z : Fin m → n → ℝ => (matrixGaussianNormalizer X)^m *
      ∏ j, matrixQuadraticGaussian (matrixWishartPrecision X Θ) (Z j)) := by
    apply continuous_const.mul
    apply continuous_finset_prod
    intro j _
    exact (matrix_quadratic_gaussian_continuous _).comp (continuous_apply j)
  have hi : Integrable (fun Z : Fin m → n → ℝ => (matrixGaussianNormalizer X)^m *
      ∏ j, matrixQuadraticGaussian (matrixWishartPrecision X Θ) (Z j)) := by
    refine ⟨hcont.measurable.aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun Z => ?_)).mpr
      (lt_top_iff_ne_top.mpr h)
    exact mul_nonneg (pow_nonneg hnrm.le _) (Finset.prod_nonneg fun j _ => (Real.exp_pos _).le)
  rw [integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (pow_ne_zero m hnrm.ne'))] at hi
  have hf := integrable_finite_product_factor
    (fun (_ : Fin m) (x : n → ℝ) => matrixQuadraticGaussian (matrixWishartPrecision X Θ) x)
    (fun _ _ => Real.exp_ne_zero _) hi ⟨0,hm⟩
  have hP : (matrixWishartPrecision X Θ).IsHermitian := by
    apply hX.inv.isHermitian.sub
    change ((2:ℝ) • Θ)ᴴ = (2:ℝ) • Θ
    rw [Matrix.conjTranspose_smul, star_trivial, hΘ.eq]
  exact matrix_quadratic_gaussian_not_integrable _ hP hn hf

theorem matrix_wishart_moment_infinite (m : ℕ) (hm : 0<m)
    (X Θ : Matrix n n ℝ) (hX : X.PosDef) (hΘ : Θ.IsHermitian)
    (hn : ¬(matrixWishartDomain X Θ hX).PosDef) :
    matrixWishartExponentialMoment m X hX Θ = ∞ := by
  apply matrix_wishart_moment_infinite_precision m hm X Θ hX hΘ
  exact fun hP => hn ((matrix_wishart_domain_positive_iff X Θ hX).mpr hP)

theorem matrix_wishart_moment_finite_iff (m : ℕ) (hm : 0<m)
    (X Θ : Matrix n n ℝ) (hX : X.PosDef) (hΘ : Θ.IsHermitian) :
    matrixWishartExponentialMoment m X hX Θ < ∞ ↔ (matrixWishartDomain X Θ hX).PosDef := by
  constructor
  · intro h
    by_contra hn
    rw [matrix_wishart_moment_infinite m hm X Θ hX hΘ hn] at h
    exact lt_irrefl _ h
  · intro hB
    rw [matrix_wishart_moment_finite m X Θ hX hB]
    exact ENNReal.ofReal_lt_top

theorem matrix_wishart_moment_formula (m : ℕ) (hm : 0<m)
    (X Θ : Matrix n n ℝ) (hX : X.PosDef) (hΘ : Θ.IsHermitian) :
    matrixWishartExponentialMoment m X hX Θ =
      @ite ℝ≥0∞ (matrixWishartDomain X Θ hX).PosDef (Classical.propDecidable _)
        (ENNReal.ofReal ((matrixWishartDomain X Θ hX).det ^ (-(m:ℝ)/2))) ∞ := by
  classical
  split_ifs with h
  · exact matrix_wishart_moment_finite m X Θ hX h
  · exact matrix_wishart_moment_infinite m hm X Θ hX hΘ h

end
end Sigma
