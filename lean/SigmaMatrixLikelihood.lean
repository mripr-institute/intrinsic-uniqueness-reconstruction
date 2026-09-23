import SigmaMatrixFenchel

namespace Sigma
noncomputable section
open scoped Matrix ComplexOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The parameter-dependent negative logarithm of the displayed likelihood,
in terms of the observed scatter. No divergence appears in this definition. -/
def matrixScatterNegLogLikelihood (m : ℕ) (W X : Matrix n n ℝ) : ℝ :=
  (m:ℝ)/2*Real.log X.det+(1/2:ℝ)*Matrix.trace (X⁻¹*W)

/-- The same objective in terms of the observed covariance W/m. -/
def matrixCovarianceNegLogLikelihood (m : ℕ) (C X : Matrix n n ℝ) : ℝ :=
  (m:ℝ)/2*(Real.log X.det+Matrix.trace (X⁻¹*C))

theorem matrix_scatter_likelihood_covariance (m : ℕ) (hm : 0<m)
    (W X : Matrix n n ℝ) :
    matrixScatterNegLogLikelihood m W X=
      matrixCovarianceNegLogLikelihood m ((m:ℝ)⁻¹ • W) X := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  simp only [matrixScatterNegLogLikelihood,matrixCovarianceNegLogLikelihood,
    Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul]
  field_simp
  ring

/-- The likelihood difference equals m/2 times D(C,X), with the covariance
and candidate in the paper's specified order. -/
theorem matrix_covariance_likelihood_gap (m : ℕ) (C X : Matrix n n ℝ)
    (hC : C.PosDef) (hX : X.PosDef) :
    matrixCovarianceNegLogLikelihood m C X-matrixCovarianceNegLogLikelihood m C C=
      (m:ℝ)/2*matrixDivergence C X := by
  unfold matrixCovarianceNegLogLikelihood matrixDivergence
  rw [Matrix.nonsing_inv_mul C (isUnit_iff_ne_zero.mpr hC.det_pos.ne'),Matrix.trace_one,
    Matrix.det_mul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv,
    Real.log_mul (inv_ne_zero hX.det_pos.ne') hC.det_pos.ne',Real.log_inv]
  ring

theorem matrix_covariance_likelihood_minimum (m : ℕ) (C X : Matrix n n ℝ)
    (hC : C.PosDef) (hX : X.PosDef) :
    matrixCovarianceNegLogLikelihood m C C≤matrixCovarianceNegLogLikelihood m C X := by
  have h := mul_nonneg (show (0:ℝ)≤m/2 by positivity)
    (matrixDivergence_nonnegative C X hC hX)
  rw [← matrix_covariance_likelihood_gap m C X hC hX] at h
  linarith

theorem matrix_covariance_likelihood_equality_iff (m : ℕ) (hm : 0<m)
    (C X : Matrix n n ℝ) (hC : C.PosDef) (hX : X.PosDef) :
    matrixCovarianceNegLogLikelihood m C X=matrixCovarianceNegLogLikelihood m C C ↔ X=C := by
  have hp : (0:ℝ)<m/2 := by positivity
  rw [← sub_eq_zero, matrix_covariance_likelihood_gap m C X hC hX,
    mul_eq_zero,or_iff_right hp.ne',matrixDivergence_eq_zero_iff C X hC hX,eq_comm]

/-- The maximum likelihood covariance is the unique minimizer in the open
SPD cone whenever the observed covariance is SPD. -/
theorem matrix_covariance_unique_mle (m : ℕ) (hm : 0<m) (C : Matrix n n ℝ) (hC : C.PosDef) :
    ∃! X : Matrix n n ℝ, X.PosDef ∧
      ∀ Y : Matrix n n ℝ, Y.PosDef →
        matrixCovarianceNegLogLikelihood m C X≤matrixCovarianceNegLogLikelihood m C Y := by
  refine ⟨C,⟨hC,fun Y hY => matrix_covariance_likelihood_minimum m C Y hC hY⟩,?_⟩
  intro X hX
  apply (matrix_covariance_likelihood_equality_iff m hm C X hC hX.1).mp
  exact le_antisymm (hX.2 C hC) (matrix_covariance_likelihood_minimum m C X hC hX.1)

/-- Precision substitution converts the likelihood objective to the negative
Fenchel objective, with its explicit dimension constant. -/
theorem matrix_covariance_likelihood_precision (m : ℕ) (C P : Matrix n n ℝ)
    (hP : P.PosDef) :
    matrixCovarianceNegLogLikelihood m C P⁻¹=
      (m:ℝ)/2*((Fintype.card n:ℝ)-
        (Matrix.trace ((1-C)*P)-matrixPotential P)) := by
  unfold matrixCovarianceNegLogLikelihood matrixPotential
  rw [Matrix.nonsing_inv_nonsing_inv P (isUnit_iff_ne_zero.mpr hP.det_pos.ne'),
    Matrix.det_nonsing_inv,Ring.inverse_eq_inv,Real.log_inv,
    Matrix.sub_mul,Matrix.one_mul,Matrix.trace_sub,Matrix.trace_mul_comm P C]
  ring

/-- An observed symmetric non-SPD scatter has an unbounded-below likelihood
objective. In particular this applies to every singular PSD covariance. -/
theorem matrix_covariance_likelihood_unbounded (m : ℕ) (hm : 0<m)
    (C : Matrix n n ℝ) (hC : C.IsHermitian) (hn : ¬C.PosDef) (M : ℝ) :
    ∃ X : Matrix n n ℝ, X.PosDef ∧ matrixCovarianceNegLogLikelihood m C X<M := by
  have hp : (0:ℝ)<m/2 := by positivity
  have hc : (1 : Matrix n n ℝ)-(1-C)=C := by abel
  obtain ⟨P,hP,hbound⟩ := matrix_fenchel_unbounded (1-C)
    (Matrix.isHermitian_one.sub hC) (by rwa [hc]) ((Fintype.card n:ℝ)-M/((m:ℝ)/2))
  refine ⟨P⁻¹,hP.inv,?_⟩
  rw [matrix_covariance_likelihood_precision m C P hP]
  have hh := mul_lt_mul_of_pos_left hbound hp
  rw [mul_sub,mul_div_cancel₀ _ hp.ne'] at hh
  linarith

theorem matrix_singular_covariance_no_mle (m : ℕ) (hm : 0<m)
    (C : Matrix n n ℝ) (hC : C.PosSemidef) (hs : C.det=0) :
    ¬∃ X : Matrix n n ℝ, X.PosDef ∧
      ∀ Y : Matrix n n ℝ, Y.PosDef →
        matrixCovarianceNegLogLikelihood m C X≤matrixCovarianceNegLogLikelihood m C Y := by
  rintro ⟨X,_,hmin⟩
  have hn : ¬C.PosDef := by
    intro hp
    have h := hp.det_pos
    rw [hs] at h
    exact lt_irrefl 0 h
  obtain ⟨Y,hY,hy⟩ := matrix_covariance_likelihood_unbounded m hm C hC.isHermitian hn
    (matrixCovarianceNegLogLikelihood m C X)
  exact (not_lt_of_ge (hmin Y hY)) hy

/-- The actual deterministic scatter of a supplied finite sample. -/
def matrixSampleScatter {m : ℕ} (Z : Fin m → n → ℝ) : Matrix n n ℝ :=
  ∑ j, Matrix.vecMulVec (Z j) (Z j)

omit [Fintype n] [DecidableEq n] in
theorem matrix_sample_scatter_gram {m : ℕ} (Z : Fin m → n → ℝ) :
    matrixSampleScatter Z=(Matrix.of Z).transpose*Matrix.of Z := by
  ext i k
  simp [matrixSampleScatter,Matrix.mul_apply,Matrix.vecMulVec,Matrix.sum_apply]

omit [DecidableEq n] in
theorem matrix_sample_scatter_posSemidef {m : ℕ} (Z : Fin m → n → ℝ) :
    (matrixSampleScatter Z).PosSemidef := by
  rw [matrix_sample_scatter_gram]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self (Z : Matrix (Fin m) n ℝ)

def matrixSampleCovariance {m : ℕ} (Z : Fin m → n → ℝ) : Matrix n n ℝ :=
  (m:ℝ)⁻¹ • matrixSampleScatter Z

omit [DecidableEq n] in
theorem matrix_sample_covariance_posSemidef {m : ℕ} (Z : Fin m → n → ℝ) :
    (matrixSampleCovariance Z).PosSemidef := by
  have hW := matrix_sample_scatter_posSemidef Z
  constructor
  · change (((m:ℝ)⁻¹ • matrixSampleScatter Z)ᴴ)=_
    rw [Matrix.conjTranspose_smul,star_trivial,hW.isHermitian]
    rfl
  · intro x
    simp only [matrixSampleCovariance,Matrix.smul_mulVec_assoc,Matrix.dotProduct_smul,smul_eq_mul]
    exact mul_nonneg (by positivity) (hW.2 x)

theorem matrix_sample_likelihood_gap {m : ℕ} (hm : 0<m) (Z : Fin m → n → ℝ)
    (X : Matrix n n ℝ) (hC : (matrixSampleCovariance Z).PosDef) (hX : X.PosDef) :
    matrixScatterNegLogLikelihood m (matrixSampleScatter Z) X-
      matrixScatterNegLogLikelihood m (matrixSampleScatter Z) (matrixSampleCovariance Z)=
        (m:ℝ)/2*matrixDivergence (matrixSampleCovariance Z) X := by
  rw [matrix_scatter_likelihood_covariance m hm,matrix_scatter_likelihood_covariance m hm]
  exact matrix_covariance_likelihood_gap m (matrixSampleCovariance Z) X hC hX

theorem matrix_singular_sample_no_mle {m : ℕ} (hm : 0<m) (Z : Fin m → n → ℝ)
    (hs : (matrixSampleCovariance Z).det=0) :
    ¬∃ X : Matrix n n ℝ, X.PosDef ∧
      ∀ Y : Matrix n n ℝ, Y.PosDef →
        matrixScatterNegLogLikelihood m (matrixSampleScatter Z) X≤
          matrixScatterNegLogLikelihood m (matrixSampleScatter Z) Y := by
  simp_rw [matrix_scatter_likelihood_covariance m hm]
  exact matrix_singular_covariance_no_mle m hm (matrixSampleCovariance Z)
    (matrix_sample_covariance_posSemidef Z) hs

end
end Sigma
