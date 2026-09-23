import SigmaOpMinimalOperator
import SigmaOpSpectralClosed
import SigmaOpLaguerreDomains

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology

theorem laguerre_minimal_closable : laguerreMinimalOperator.IsClosable :=
  (laguerre_spectral_closed id).isClosable.leIsClosable laguerre_minimal_le_spectral

theorem laguerre_minimal_closure_le_spectral :
    laguerreMinimalOperator.closure ≤ laguerreSpectralOperator id := by
  apply LinearPMap.le_of_le_graph
  rw [← laguerre_minimal_closable.graph_closure_eq_closure_graph]
  have h := Submodule.topologicalClosure_mono
    (LinearPMap.le_graph_of_le laguerre_minimal_le_spectral)
  rwa [(laguerre_spectral_closed id).submodule_topologicalClosure_eq] at h

theorem laguerre_minimal_nonnegative (x : laguerreMinimalOperator.domain) :
    0 ≤ (@inner ℂ LaguerreWeightedHilbert _ x.val (laguerreMinimalOperator x)).re := by
  rw [laguerre_minimal_le_spectral.2 (y :=
    ⟨x.val, laguerre_minimal_le_spectral.1 x.property⟩) rfl]
  exact laguerre_spectral_nonnegative id (fun n => Nat.cast_nonneg n)
    ⟨x.val, laguerre_minimal_le_spectral.1 x.property⟩

/-- Closed linear subspaces of the graph ambient space containing every
eigenvector graph pair contain the whole maximal spectral graph. -/
theorem laguerre_graph_le_of_modes
    (G : Submodule ℂ (LaguerreWeightedHilbert × LaguerreWeightedHilbert))
    (hG : IsClosed (G : Set (LaguerreWeightedHilbert × LaguerreWeightedHilbert)))
    (hmodes : ∀ n : ℕ, (laguerreHilbertBasis n, (n : ℂ) • laguerreHilbertBasis n) ∈ G) :
    (laguerreSpectralOperator id).graph ≤ G := by
  intro p hp
  obtain ⟨x,hx,hy⟩ := (LinearPMap.mem_graph_iff _).mp hp
  change (p.1,p.2) ∈ G
  rw [← hx, ← hy]
  have hsum := (laguerreHilbertBasis.hasSum_repr x.val).prod_mk
    (laguerre_integer_action_hasSum x)
  apply hG.mem_of_tendsto hsum
  apply Eventually.of_forall
  intro s
  apply G.sum_mem
  intro n _
  have h := G.smul_mem (laguerreCoefficient x.val n) (hmodes n)
  convert h using 1
  ext <;> simp [laguerreCoefficient, smul_smul, mul_comm]

/-- This abstract assembly lemma isolates the remaining analytic obligation:
actual compact-test graph approximations of each marked mode. It does not
assert those approximations or hide them in a realization structure. -/
theorem laguerre_minimal_closure_eq_of_modes
    (hmodes : ∀ n : ℕ, (laguerreHilbertBasis n, (n : ℂ) • laguerreHilbertBasis n) ∈
      laguerreMinimalOperator.graph.topologicalClosure) :
    laguerreMinimalOperator.closure = laguerreSpectralOperator id := by
  apply le_antisymm laguerre_minimal_closure_le_spectral
  apply LinearPMap.le_of_le_graph
  rw [← laguerre_minimal_closable.graph_closure_eq_closure_graph]
  exact laguerre_graph_le_of_modes _
    laguerreMinimalOperator.graph.isClosed_topologicalClosure hmodes

theorem laguerre_minimal_dense_of_modes
    (hmodes : ∀ n : ℕ, (laguerreHilbertBasis n, (n : ℂ) • laguerreHilbertBasis n) ∈
      laguerreMinimalOperator.graph.topologicalClosure) :
    Dense (laguerreMinimalOperator.domain : Set LaguerreWeightedHilbert) := by
  have hproj : Prod.fst '' (laguerreMinimalOperator.graph :
      Set (LaguerreWeightedHilbert × LaguerreWeightedHilbert)) =
      (laguerreMinimalOperator.domain : Set LaguerreWeightedHilbert) := by
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩
      obtain ⟨u,hu,_⟩ := (LinearPMap.mem_graph_iff _).mp hp
      exact hu ▸ u.property
    · intro hx
      exact ⟨(x,laguerreMinimalOperator ⟨x,hx⟩), LinearPMap.mem_graph _ ⟨x,hx⟩, rfl⟩
  have hb (n : ℕ) : laguerreHilbertBasis n ∈
      laguerreMinimalOperator.domain.topologicalClosure := by
    have h := image_closure_subset_closure_image continuous_fst
      (show laguerreHilbertBasis n ∈ Prod.fst '' closure
        (laguerreMinimalOperator.graph :
          Set (LaguerreWeightedHilbert × LaguerreWeightedHilbert)) from
        ⟨(laguerreHilbertBasis n,(n : ℂ) • laguerreHilbertBasis n), hmodes n, rfl⟩)
    rw [hproj] at h
    exact h
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  rw [← laguerreHilbertBasis.dense_span]
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨n,rfl⟩
    exact hb n
  · exact laguerreMinimalOperator.domain.isClosed_topologicalClosure

/-- Graph-core approximation determines the adjoint as well as the closure;
this uses continuity of the actual inner products on H times H. -/
theorem laguerre_minimal_adjoint_eq_of_modes
    (hmodes : ∀ n : ℕ, (laguerreHilbertBasis n, (n : ℂ) • laguerreHilbertBasis n) ∈
      laguerreMinimalOperator.graph.topologicalClosure) :
    laguerreMinimalOperator.adjoint = laguerreSpectralOperator id := by
  have hd := laguerre_minimal_dense_of_modes hmodes
  have hc := laguerre_minimal_closure_eq_of_modes hmodes
  have hformal : laguerreMinimalOperator.adjoint.IsFormalAdjoint
      (laguerreSpectralOperator id) := by
    intro y x
    let C : Set (LaguerreWeightedHilbert × LaguerreWeightedHilbert) :=
      {p | @inner ℂ LaguerreWeightedHilbert _ (laguerreMinimalOperator.adjoint y) p.1 =
        @inner ℂ LaguerreWeightedHilbert _ y.val p.2}
    have hC : IsClosed C := isClosed_eq
      (continuous_const.inner continuous_fst) (continuous_const.inner continuous_snd)
    have hsub : (laguerreMinimalOperator.graph :
        Set (LaguerreWeightedHilbert × LaguerreWeightedHilbert)) ⊆ C := by
      intro p hp
      obtain ⟨u,hu,hv⟩ := (LinearPMap.mem_graph_iff _).mp hp
      change @inner ℂ LaguerreWeightedHilbert _ (laguerreMinimalOperator.adjoint y) p.1 =
        @inner ℂ LaguerreWeightedHilbert _ y.val p.2
      rw [← hu, ← hv]
      exact laguerreMinimalOperator.adjoint_isFormalAdjoint hd y u
    change (x.val, laguerreSpectralOperator id x) ∈ C
    apply (closure_minimal hsub hC)
    change (x.val, laguerreSpectralOperator id x) ∈
      laguerreMinimalOperator.graph.topologicalClosure
    rw [laguerre_minimal_closable.graph_closure_eq_closure_graph, hc]
    exact LinearPMap.mem_graph _ x
  apply le_antisymm
  · have h := hformal.symm.le_adjoint (laguerre_spectral_domain_dense id)
    rwa [show (laguerreSpectralOperator id).adjoint = laguerreSpectralOperator id from
      LinearPMap.isSelfAdjoint_def.mp (laguerre_spectral_selfAdjoint id)] at h
  · apply LinearPMap.IsFormalAdjoint.le_adjoint (hT := hd)
    intro x y
    have h := laguerre_spectral_formal_adjoint id
      ⟨x.val, laguerre_minimal_le_spectral.1 x.property⟩ y
    rwa [← laguerre_minimal_le_spectral.2 (x := x) rfl] at h

/-- A self-adjoint extension is forced once the actual compact-test graph
approximations are supplied. No choice of extension enters the conclusion. -/
theorem laguerre_selfadjoint_extension_unique_of_modes
    (hmodes : ∀ n : ℕ, (laguerreHilbertBasis n, (n : ℂ) • laguerreHilbertBasis n) ∈
      laguerreMinimalOperator.graph.topologicalClosure)
    (T : LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert)
    (hT : IsSelfAdjoint T) (hExt : laguerreMinimalOperator ≤ T) :
    T = laguerreSpectralOperator id := by
  have hTD := hT.dense_domain
  have hTSymm : T.IsFormalAdjoint T := by
    have h := T.adjoint_isFormalAdjoint hTD
    rwa [LinearPMap.isSelfAdjoint_def.mp hT] at h
  have hMT : laguerreMinimalOperator.IsFormalAdjoint T := by
    intro x y
    have h := hTSymm ⟨x.val,hExt.1 x.property⟩ y
    rwa [← hExt.2 (x := x) rfl] at h
  have hle : T ≤ laguerreSpectralOperator id := by
    have h := hMT.le_adjoint (laguerre_minimal_dense_of_modes hmodes)
    rwa [laguerre_minimal_adjoint_eq_of_modes hmodes] at h
  apply le_antisymm hle
  have hST : T.IsFormalAdjoint (laguerreSpectralOperator id) := by
    intro x y
    have h := laguerre_spectral_formal_adjoint id ⟨x.val,hle.1 x.property⟩ y
    rwa [← hle.2 (x := x) rfl] at h
  have h := hST.le_adjoint hTD
  rwa [LinearPMap.isSelfAdjoint_def.mp hT] at h

end
end Sigma
