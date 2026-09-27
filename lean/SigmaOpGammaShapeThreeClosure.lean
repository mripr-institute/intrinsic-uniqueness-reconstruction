import SigmaOpGammaShapeThreeApproximation

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
set_option maxHeartbeats 800000

theorem gamma_shape_three_compact_pair_mem_minimal_graph_closure (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    (gammaShapeThreeCompactVector f hf hs, gammaShapeThreeCompactImage f hf hs) ∈
      gammaShapeThreeMinimalOperator.graph.topologicalClosure := by
  have hx := gamma_shape_three_log_cutoff_vector_tendsto f hf hs
  have hy := gamma_shape_three_log_cutoff_image_tendsto f hf hs
  change (gammaShapeThreeCompactVector f hf hs, gammaShapeThreeCompactImage f hf hs) ∈
    closure (gammaShapeThreeMinimalOperator.graph :
      Set (GammaShapeThreeWeightedHilbert × GammaShapeThreeWeightedHilbert))
  apply mem_closure_of_tendsto (hx.prod_mk_nhds hy)
  apply Eventually.of_forall
  intro k
  have h := gammaShapeThreeMinimalOperator.mem_graph
    ⟨gammaShapeThreeCompactVector (operatorLogCutoffTest k f)
      (operator_log_cutoff_test_smooth k f hf) (operator_log_cutoff_test_compact k f hs),
      gamma_shape_three_compact_test_mem _ _ _ (operator_log_cutoff_test_positive_support k f)⟩
  rwa [gamma_shape_three_minimal_test_action _ _ _
    (operator_log_cutoff_test_positive_support k f)] at h

theorem gamma_shape_three_laguerre_pair_mem_minimal_graph_closure (n : ℕ) :
    (gammaShapeThreeL2Vector n, (n : ℂ) • gammaShapeThreeL2Vector n) ∈
      gammaShapeThreeMinimalOperator.graph.topologicalClosure := by
  apply gammaShapeThreeMinimalOperator.graph.isClosed_topologicalClosure.mem_of_tendsto
    (gamma_shape_three_upper_laguerre_graph_tendsto n)
  apply Eventually.of_forall
  intro k
  exact gamma_shape_three_compact_pair_mem_minimal_graph_closure _
    (upper_cutoff_test_smooth _ (gamma_shape_three_laguerre_complex_contDiff n) k)
    (upper_cutoff_test_compact _ k)

theorem gamma_shape_three_basis_pair_mem_minimal_graph_closure (n : ℕ) :
    (gammaShapeThreeHilbertBasis n, (n : ℂ) • gammaShapeThreeHilbertBasis n) ∈
      gammaShapeThreeMinimalOperator.graph.topologicalClosure := by
  have h := gammaShapeThreeMinimalOperator.graph.topologicalClosure.smul_mem
    ((Real.sqrt ((n+1 : ℝ)*(n+2)/2) : ℂ)⁻¹)
    (gamma_shape_three_laguerre_pair_mem_minimal_graph_closure n)
  simpa only [gamma_shape_three_hilbert_basis_apply,
    normalizedGammaShapeThreeL2Vector, Prod.smul_mk, smul_smul, mul_comm] using h

/-- The closure of the literal `C_c^∞(0,∞)` differential graph. -/
def gammaShapeThreeCanonicalOperator :
    GammaShapeThreeWeightedHilbert →ₗ.[ℂ] GammaShapeThreeWeightedHilbert :=
  gammaShapeThreeMinimalOperator.closure

/-- Actual compact-interior graph approximation identifies the full domain
and action of the closure with the maximal Laguerre operator. -/
theorem gamma_shape_three_canonical_eq_spectral :
    gammaShapeThreeCanonicalOperator = gammaShapeThreeSpectralOperator :=
  integer_basis_restriction_closure_eq_of_modes gammaShapeThreeHilbertBasis
    (fun n => (n : ℂ)) gammaShapeThreeMinimalOperator
    gamma_shape_three_minimal_le_spectral gamma_shape_three_basis_pair_mem_minimal_graph_closure

theorem gamma_shape_three_canonical_selfAdjoint : IsSelfAdjoint gammaShapeThreeCanonicalOperator := by
  rw [gamma_shape_three_canonical_eq_spectral]
  exact gamma_shape_three_spectral_selfAdjoint

theorem gamma_shape_three_canonical_nonnegative : OpNonnegative gammaShapeThreeCanonicalOperator := by
  rw [gamma_shape_three_canonical_eq_spectral]
  exact gamma_shape_three_spectral_nonnegative

end
end Sigma
