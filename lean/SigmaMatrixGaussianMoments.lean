import SigmaMatrixGaussianMeasure
import Mathlib.MeasureTheory.Function.L2Space

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped BigOperators ENNReal NNReal
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem gaussian_zero_identity_integrable : Integrable (fun t : ℝ => t) (gaussianReal 0 1) := by
  apply Memℒp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact (memℒp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr
    (gaussian_zero_square_integrable 1 (by norm_num))

theorem gaussian_zero_first_moment : (∫ t : ℝ, t ∂gaussianReal 0 1) = 0 := by
  have he := congrArg (fun μ : Measure ℝ => ∫ t : ℝ, t ∂μ)
    (gaussianReal_map_const_mul (μ := 0) (v := 1) (-1))
  dsimp only at he
  rw [integral_map (f := fun t : ℝ => t) (by fun_prop)
    (measurable_id : Measurable (fun t : ℝ => t)).aestronglyMeasurable] at he
  norm_num [integral_neg] at he
  rw [integral_neg] at he
  linarith

omit [DecidableEq n] in
theorem standard_matrix_gaussian_product_integral (f : n → ℝ → ℝ) :
    (∫ x : n → ℝ, ∏ i, f i (x i) ∂standardMatrixGaussianMeasure n) =
      ∏ i, ∫ t : ℝ, f i t ∂gaussianReal 0 1 := by
  rw [standard_matrix_gaussian_measure_pi]
  letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
  letI : IsProbabilityMeasure (volume : Measure ℝ) := by
    change IsProbabilityMeasure (gaussianReal 0 1)
    infer_instance
  exact integral_fintype_prod_eq_prod n f

omit [DecidableEq n] in
theorem standard_matrix_gaussian_product_integrable (f : n → ℝ → ℝ)
    (hf : ∀ i, Integrable (f i) (gaussianReal 0 1)) :
    Integrable (fun x : n → ℝ => ∏ i, f i (x i)) (standardMatrixGaussianMeasure n) := by
  rw [standard_matrix_gaussian_measure_pi]
  letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
  letI : IsProbabilityMeasure (volume : Measure ℝ) := by
    change IsProbabilityMeasure (gaussianReal 0 1)
    infer_instance
  exact Integrable.fintype_prod hf

theorem standard_matrix_gaussian_coordinate_integrable (i : n) :
    Integrable (fun x : n → ℝ => x i) (standardMatrixGaussianMeasure n) := by
  have hi := standard_matrix_gaussian_product_integrable
    (fun k t => if k=i then t else 1) (fun k => by
      by_cases hk : k=i
      · simpa only [if_pos hk] using gaussian_zero_identity_integrable
      · simpa only [if_neg hk] using (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 1)))
  simpa using hi

theorem standard_matrix_gaussian_coordinate_mean (i : n) :
    (∫ x : n → ℝ, x i ∂standardMatrixGaussianMeasure n) = 0 := by
  have hi := standard_matrix_gaussian_product_integral (fun k t => if k=i then t else 1)
  have he (k : n) : (∫ t : ℝ, (if k=i then t else 1) ∂gaussianReal 0 1) =
      if k=i then (0 : ℝ) else 1 := by
    by_cases hk : k=i <;> simp [hk,gaussian_zero_first_moment]
  simp only [he] at hi
  simpa using hi

theorem standard_matrix_gaussian_pair_integrable (i j : n) :
    Integrable (fun x : n → ℝ => x i * x j) (standardMatrixGaussianMeasure n) := by
  have hi := standard_matrix_gaussian_product_integrable
    (fun k t => (if k=i then t else 1)*(if k=j then t else 1)) (fun k => by
      by_cases hki : k=i <;> by_cases hkj : k=j
      · simpa only [if_pos hki,if_pos hkj,pow_two] using gaussian_zero_square_integrable 1 (by norm_num)
      · simpa only [if_pos hki,if_neg hkj,mul_one] using gaussian_zero_identity_integrable
      · simpa only [if_neg hki,if_pos hkj,one_mul] using gaussian_zero_identity_integrable
      · simp [hki,hkj])
  simpa only [Finset.prod_mul_distrib,Finset.prod_ite_eq',Finset.mem_univ,if_true] using hi

theorem standard_matrix_gaussian_pair_moment (i j : n) :
    (∫ x : n → ℝ, x i * x j ∂standardMatrixGaussianMeasure n) = if i=j then 1 else 0 := by
  have hi := standard_matrix_gaussian_product_integral
    (fun k t => (if k=i then t else 1)*(if k=j then t else 1))
  simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true] at hi
  rw [hi]
  by_cases hij : i=j
  · subst j
    have he (k : n) : (∫ t : ℝ, (if k=i then t else 1)*(if k=i then t else 1)
        ∂gaussianReal 0 1) = 1 := by
      by_cases hk : k=i
      · simpa [hk,pow_two] using gaussian_zero_second_moment 1 (by norm_num)
      · simp [hk]
    simp only [he,Finset.prod_const_one,if_pos rfl,ite_true]
  · rw [if_neg hij]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa [hij] using gaussian_zero_first_moment

theorem standard_matrix_gaussian_linear_integrable (a : n → ℝ) :
    Integrable (fun x : n → ℝ => dotProduct a x) (standardMatrixGaussianMeasure n) := by
  exact integrable_finset_sum _ fun i _ => (standard_matrix_gaussian_coordinate_integrable i).const_mul (a i)

theorem standard_matrix_gaussian_linear_mean (a : n → ℝ) :
    (∫ x : n → ℝ, dotProduct a x ∂standardMatrixGaussianMeasure n) = 0 := by
  unfold dotProduct
  rw [integral_finset_sum _ (fun i _ => (standard_matrix_gaussian_coordinate_integrable i).const_mul (a i))]
  simp only [integral_mul_left,standard_matrix_gaussian_coordinate_mean,mul_zero,Finset.sum_const_zero]

omit [DecidableEq n] in
theorem gaussian_linear_pair_expansion (a b x : n → ℝ) :
    dotProduct a x * dotProduct b x = ∑ i, ∑ j, (a i*b j)*(x i*x j) := by
  unfold dotProduct
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem standard_matrix_gaussian_linear_pair_integrable (a b : n → ℝ) :
    Integrable (fun x : n → ℝ => dotProduct a x * dotProduct b x)
      (standardMatrixGaussianMeasure n) := by
  simp only [gaussian_linear_pair_expansion]
  apply integrable_finset_sum
  intro i hi
  apply integrable_finset_sum
  intro j hj
  exact (standard_matrix_gaussian_pair_integrable i j).const_mul _

theorem standard_matrix_gaussian_linear_pair_moment (a b : n → ℝ) :
    (∫ x : n → ℝ, dotProduct a x * dotProduct b x ∂standardMatrixGaussianMeasure n) =
      dotProduct a b := by
  simp only [gaussian_linear_pair_expansion]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _
    (fun j _ => (standard_matrix_gaussian_pair_integrable i j).const_mul _))]
  simp_rw [integral_finset_sum _ (fun j _ => (standard_matrix_gaussian_pair_integrable _ j).const_mul _),
    integral_mul_left, standard_matrix_gaussian_pair_moment]
  simp [dotProduct]

theorem matrix_gaussian_coordinate_integrable (X : Matrix n n ℝ) (hX : X.PosDef) (i : n) :
    Integrable (fun x : n → ℝ => x i) (matrixGaussianMeasure X hX) := by
  unfold matrixGaussianMeasure
  apply (integrable_map_measure (continuous_apply i).aestronglyMeasurable
    (matrixGaussianSqrtEquiv X hX).continuous.measurable.aemeasurable).mpr
  exact standard_matrix_gaussian_linear_integrable (hX.posSemidef.sqrt i)

theorem matrix_gaussian_coordinate_mean (X : Matrix n n ℝ) (hX : X.PosDef) (i : n) :
    (∫ x : n → ℝ, x i ∂matrixGaussianMeasure X hX) = 0 := by
  rw [matrixGaussianMeasure, integral_map
    (matrixGaussianSqrtEquiv X hX).continuous.measurable.aemeasurable
    (continuous_apply i).aestronglyMeasurable]
  exact standard_matrix_gaussian_linear_mean (hX.posSemidef.sqrt i)

theorem matrix_gaussian_coordinate_pair_integrable (X : Matrix n n ℝ) (hX : X.PosDef) (i j : n) :
    Integrable (fun x : n → ℝ => x i * x j) (matrixGaussianMeasure X hX) := by
  unfold matrixGaussianMeasure
  apply (integrable_map_measure ((continuous_apply i).mul (continuous_apply j)).aestronglyMeasurable
    (matrixGaussianSqrtEquiv X hX).continuous.measurable.aemeasurable).mpr
  exact standard_matrix_gaussian_linear_pair_integrable (hX.posSemidef.sqrt i) (hX.posSemidef.sqrt j)

/-- The covariance parameter is the actual second-moment matrix of the
constructed centered probability measure, not a merely nominal label. -/
theorem matrix_gaussian_coordinate_pair_moment (X : Matrix n n ℝ) (hX : X.PosDef) (i j : n) :
    (∫ x : n → ℝ, x i * x j ∂matrixGaussianMeasure X hX) = X i j := by
  rw [matrixGaussianMeasure, integral_map
    (matrixGaussianSqrtEquiv X hX).continuous.measurable.aemeasurable
    ((continuous_apply i).mul (continuous_apply j)).aestronglyMeasurable]
  change (∫ x : n → ℝ, dotProduct (hX.posSemidef.sqrt i) x *
    dotProduct (hX.posSemidef.sqrt j) x ∂standardMatrixGaussianMeasure n) = _
  rw [standard_matrix_gaussian_linear_pair_moment]
  have hQt : hX.posSemidef.sqrtᵀ = hX.posSemidef.sqrt := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hX.posSemidef.posSemidef_sqrt.isHermitian.eq
  change (hX.posSemidef.sqrt * hX.posSemidef.sqrtᵀ) i j = _
  rw [hQt,hX.posSemidef.sqrt_mul_self]

theorem matrix_gaussian_quadratic_integrable (X P : Matrix n n ℝ) (hX : X.PosDef) :
    Integrable (fun x : n → ℝ => dotProduct x (P *ᵥ x)) (matrixGaussianMeasure X hX) := by
  have he (x : n → ℝ) : dotProduct x (P *ᵥ x) = ∑ i, ∑ j, P i j*(x i*x j) := by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [he]
  exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
    (matrix_gaussian_coordinate_pair_integrable X hX i j).const_mul _

theorem matrix_gaussian_quadratic_mean (X P : Matrix n n ℝ) (hX : X.PosDef) :
    (∫ x : n → ℝ, dotProduct x (P *ᵥ x) ∂matrixGaussianMeasure X hX) = Matrix.trace (P*X) := by
  have he (x : n → ℝ) : dotProduct x (P *ᵥ x) = ∑ i, ∑ j, P i j*(x i*x j) := by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [he]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _
    (fun j _ => (matrix_gaussian_coordinate_pair_integrable X hX i j).const_mul _))]
  simp_rw [integral_finset_sum _ (fun j _ => (matrix_gaussian_coordinate_pair_integrable X hX _ j).const_mul _),
    integral_mul_left,matrix_gaussian_coordinate_pair_moment]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show X i j = X j i from hX.isHermitian.apply j i]

end
end Sigma
