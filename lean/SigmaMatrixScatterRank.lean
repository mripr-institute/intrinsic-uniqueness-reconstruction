import SigmaMatrixGaussianLikelihood
import Mathlib.Data.Matrix.Rank

namespace Sigma
noncomputable section
open MeasureTheory Matrix Set

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The scatter rank is exactly the dimension of the span of the observed
vectors, not merely a bound obtained from the sampling model. -/
theorem matrix_sample_scatter_rank {m : ℕ} (Z : Fin m → n → ℝ) :
    (matrixSampleScatter Z).rank =
      Module.finrank ℝ (Submodule.span ℝ (Set.range Z)) := by
  rw [matrix_sample_scatter_gram, Matrix.rank_transpose_mul_self]
  exact Matrix.rank_eq_finrank_span_row (Matrix.of Z)

omit [DecidableEq n] in
theorem matrix_sample_scatter_rank_le {m : ℕ} (Z : Fin m → n → ℝ) :
    (matrixSampleScatter Z).rank ≤ m := by
  rw [matrix_sample_scatter_gram, Matrix.rank_transpose_mul_self]
  simpa using Matrix.rank_le_card_height (Matrix.of Z)

/-- Fewer observations than coordinates force singular scatter for every
sample, independently of any exceptional null sets. -/
theorem matrix_sample_scatter_singular_of_small_sample {m : ℕ}
    (hm : m < Fintype.card n) (Z : Fin m → n → ℝ) :
    (matrixSampleScatter Z).det = 0 := by
  by_contra h
  have hu : IsUnit (matrixSampleScatter Z) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)
  have hr := matrix_sample_scatter_rank_le Z
  rw [Matrix.rank_of_isUnit _ hu] at hr
  omega

theorem matrix_sample_scatter_not_posDef_of_small_sample {m : ℕ}
    (hm : m < Fintype.card n) (Z : Fin m → n → ℝ) :
    ¬ (matrixSampleScatter Z).PosDef := by
  intro h
  have hp := h.det_pos
  rw [matrix_sample_scatter_singular_of_small_sample hm Z] at hp
  exact (lt_irrefl 0) hp

/-- The actual Wishart law is concentrated on singular matrices when m<n. -/
theorem matrix_wishart_small_sample_singular {m : ℕ} (hm : m < Fintype.card n)
    (X : Matrix n n ℝ) (hX : X.PosDef) :
    ∀ᵐ W ∂matrixWishartMeasure m X hX, W.det = 0 := by
  apply (ae_map_iff (matrix_sample_scatter_continuous m).measurable.aemeasurable
    (isClosed_eq continuous_id.matrix_det continuous_const).measurableSet).mpr
  exact Filter.Eventually.of_forall (matrix_sample_scatter_singular_of_small_sample hm)

end
end Sigma
