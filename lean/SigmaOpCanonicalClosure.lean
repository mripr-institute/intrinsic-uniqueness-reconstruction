import SigmaOpUpperApproximation
import SigmaOpLogCutoffApproximation
import SigmaOpLaguerreEigenvalues
import SigmaOpLaguerreComplexResolvent
import SigmaOpLaguerreResolventCompact

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology

theorem laguerre_raw_graph_mem_minimal_closure (n : ℕ) :
    (laguerreL2Vector n, (n : ℂ) • laguerreL2Vector n) ∈
      laguerreMinimalOperator.graph.topologicalClosure := by
  apply laguerreMinimalOperator.graph.isClosed_topologicalClosure.mem_of_tendsto
    (upper_laguerre_graph_tendsto n)
  apply Eventually.of_forall
  intro k
  exact smooth_compact_pair_mem_minimal_graph_closure _
    (upper_cutoff_test_smooth _ (op_laguerre_complex_contDiff n) k)
    (upper_cutoff_test_compact _ k)

/-- Actual compact-interior graph approximants to every marked normalized
mode, derived by logarithmic lower and ordinary upper cutoffs. -/
theorem laguerre_modes_mem_minimal_graph_closure (n : ℕ) :
    (laguerreHilbertBasis n, (n : ℂ) • laguerreHilbertBasis n) ∈
      laguerreMinimalOperator.graph.topologicalClosure := by
  have h := laguerreMinimalOperator.graph.topologicalClosure.smul_mem
    ((Real.sqrt (n+1 : ℝ) : ℂ)⁻¹) (laguerre_raw_graph_mem_minimal_closure n)
  convert h using 1
  apply Prod.ext
  · exact laguerre_hilbert_basis_apply n
  · change (n : ℂ) • laguerreHilbertBasis n =
      (Real.sqrt (n+1 : ℝ) : ℂ)⁻¹ • ((n : ℂ) • laguerreL2Vector n)
    rw [laguerre_hilbert_basis_apply, normalizedLaguerreL2Vector, smul_comm]

/-- The paper's operator is the graph closure of the literal compact-test
differential operator, not a spectral operator renamed by definition. -/
def laguerreCanonicalOperator : LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert :=
  laguerreMinimalOperator.closure

theorem laguerre_canonical_eq_spectral :
    laguerreCanonicalOperator = laguerreSpectralOperator id :=
  laguerre_minimal_closure_eq_of_modes laguerre_modes_mem_minimal_graph_closure

theorem laguerre_minimal_dense :
    Dense (laguerreMinimalOperator.domain : Set LaguerreWeightedHilbert) :=
  laguerre_minimal_dense_of_modes laguerre_modes_mem_minimal_graph_closure

theorem laguerre_minimal_adjoint_eq_canonical :
    laguerreMinimalOperator.adjoint = laguerreCanonicalOperator := by
  rw [laguerre_canonical_eq_spectral]
  exact laguerre_minimal_adjoint_eq_of_modes laguerre_modes_mem_minimal_graph_closure

theorem laguerre_canonical_selfAdjoint : IsSelfAdjoint laguerreCanonicalOperator := by
  rw [laguerre_canonical_eq_spectral]
  exact laguerre_spectral_selfAdjoint id

theorem laguerre_canonical_unique_selfAdjoint_extension
    (T : LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert)
    (hT : IsSelfAdjoint T) (hExt : laguerreMinimalOperator ≤ T) :
    T = laguerreCanonicalOperator := by
  rw [laguerre_canonical_eq_spectral]
  exact laguerre_selfadjoint_extension_unique_of_modes
    laguerre_modes_mem_minimal_graph_closure T hT hExt

theorem laguerre_canonical_domain_iff (x : LaguerreWeightedHilbert) :
    x ∈ laguerreCanonicalOperator.domain ↔
      Summable (fun n : ℕ => (n : ℝ)^2 * ‖laguerreCoefficient x n‖^2) := by
  rw [laguerre_canonical_eq_spectral]
  exact laguerre_integer_domain_iff x

theorem laguerre_basis_mem_canonical_domain (n : ℕ) :
    laguerreHilbertBasis n ∈ laguerreCanonicalOperator.domain := by
  rw [laguerre_canonical_eq_spectral]
  exact laguerre_basis_mem_spectral_domain id n

theorem laguerre_canonical_basis_action (n : ℕ) :
  laguerreCanonicalOperator ⟨laguerreHilbertBasis n, laguerre_basis_mem_canonical_domain n⟩ =
      (n : ℂ) • laguerreHilbertBasis n := by
  calc
    _ = laguerreSpectralOperator id
        ⟨laguerreHilbertBasis n, laguerre_basis_mem_spectral_domain id n⟩ :=
      laguerre_canonical_eq_spectral.le.2 rfl
    _ = _ := laguerre_spectral_basis_action id n

theorem laguerre_canonical_action_hasSum (x : laguerreCanonicalOperator.domain) :
    HasSum (fun n : ℕ => ((n : ℂ) * laguerreCoefficient x.val n) •
      laguerreHilbertBasis n) (laguerreCanonicalOperator x) := by
  have hx := laguerre_canonical_eq_spectral.le.1 x.property
  have he : laguerreCanonicalOperator x = laguerreSpectralOperator id ⟨x.val,hx⟩ :=
    laguerre_canonical_eq_spectral.le.2 rfl
  rw [he]
  exact laguerre_integer_action_hasSum ⟨x.val,hx⟩

theorem laguerre_canonical_spectrum_exact :
    unboundedOperatorSpectrum laguerreCanonicalOperator = Set.range (fun n : ℕ => (n : ℂ)) := by
  rw [laguerre_canonical_eq_spectral]
  exact laguerre_full_spectrum_exact

theorem laguerre_canonical_compact_resolvent (α : ℝ) (hα : 0 < α) :
    ∃ R : LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert,
      IsCompactOperator R ∧ ∃ hdom : ∀ x, R x ∈ laguerreCanonicalOperator.domain,
        (∀ x, laguerreCanonicalOperator ⟨R x,hdom x⟩ + (α : ℂ) • R x = x) ∧
        (∀ x : laguerreCanonicalOperator.domain,
          R (laguerreCanonicalOperator x + (α : ℂ) • x.val) = x.val) := by
  rw [laguerre_canonical_eq_spectral]
  exact ⟨laguerreResolvent α hα, laguerre_resolvent_compact α hα,
    laguerre_resolvent_mem_domain α hα,
    laguerre_resolvent_right_inverse α hα, laguerre_resolvent_left_inverse α hα⟩

end
end Sigma
