import SigmaOpGraphCore
import SigmaOpDifferentialEnergy
import SigmaOpCutoffApproximation

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

theorem laguerre_square_root_graph_bound (x : (laguerreSpectralOperator id).domain) :
    ‖laguerreSpectralOperator Real.sqrt
      ⟨x.val, laguerre_integer_domain_le_square_root x.property⟩‖^2 ≤
      ‖x.val‖ * ‖laguerreSpectralOperator id x‖ := by
  have h := re_inner_le_norm (𝕜 := ℂ) x.val (laguerreSpectralOperator id x)
  rw [laguerre_integer_inner_energy] at h
  simpa only [RCLike.ofReal_re] using h

/-- Operator-graph approximation implies square-root/form-graph
approximation, by the proved energy bound, not by an assumed form core. -/
theorem laguerre_square_root_tendsto_of_graph
    (u : ℕ → (laguerreSpectralOperator id).domain)
    (x : (laguerreSpectralOperator id).domain)
    (hu : Tendsto (fun k => (u k).val) atTop (𝓝 x.val))
    (hAu : Tendsto (fun k => laguerreSpectralOperator id (u k)) atTop
      (𝓝 (laguerreSpectralOperator id x))) :
    Tendsto (fun k => laguerreSpectralOperator Real.sqrt
      ⟨(u k).val, laguerre_integer_domain_le_square_root (u k).property⟩) atTop
      (𝓝 (laguerreSpectralOperator Real.sqrt
        ⟨x.val, laguerre_integer_domain_le_square_root x.property⟩)) := by
  apply laguerre_l2_tendsto_of_sq_error
  have hlim : Tendsto (fun k => ‖(u k).val-x.val‖ *
      ‖laguerreSpectralOperator id (u k)-laguerreSpectralOperator id x‖)
      atTop (𝓝 0) := by
    simpa using ((hu.sub_const x.val).norm.mul
      ((hAu.sub_const (laguerreSpectralOperator id x)).norm))
  apply squeeze_zero (fun _ => sq_nonneg _) _ hlim
  intro k
  have h := laguerre_square_root_graph_bound (u k-x)
  have he : laguerreSpectralOperator Real.sqrt
      ⟨(u k-x).val, laguerre_integer_domain_le_square_root (u k-x).property⟩ =
      laguerreSpectralOperator Real.sqrt
        ⟨(u k).val, laguerre_integer_domain_le_square_root (u k).property⟩ -
      laguerreSpectralOperator Real.sqrt
        ⟨x.val, laguerre_integer_domain_le_square_root x.property⟩ := by
    change laguerreSpectralOperator Real.sqrt
      (⟨(u k).val, laguerre_integer_domain_le_square_root (u k).property⟩ -
        ⟨x.val, laguerre_integer_domain_le_square_root x.property⟩) = _
    exact LinearPMap.map_sub _ _ _
  rw [he, LinearPMap.map_sub] at h
  exact h

def laguerreMinimalFormRoot : LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert :=
  (laguerreSpectralOperator Real.sqrt).domRestrict laguerreMinimalOperator.domain

theorem laguerre_minimal_form_root_domain :
    laguerreMinimalFormRoot.domain = laguerreMinimalOperator.domain :=
  inf_eq_left.mpr (laguerre_minimal_le_spectral.1.trans laguerre_integer_domain_le_square_root)

theorem laguerre_minimal_form_root_le :
    laguerreMinimalFormRoot ≤ laguerreSpectralOperator Real.sqrt :=
  LinearPMap.domRestrict_le

theorem laguerre_form_mode_approximation
    (hmodes : ∀ n : ℕ, (laguerreHilbertBasis n, (n : ℂ) • laguerreHilbertBasis n) ∈
      laguerreMinimalOperator.graph.topologicalClosure) (n : ℕ) :
    (laguerreHilbertBasis n, (Real.sqrt n : ℂ) • laguerreHilbertBasis n) ∈
      laguerreMinimalFormRoot.graph.topologicalClosure := by
  obtain ⟨p,hp,ht⟩ := mem_closure_iff_seq_limit.mp (hmodes n)
  choose u hu1 hu2 using fun k => (LinearPMap.mem_graph_iff _).mp (hp k)
  let v : ℕ → (laguerreSpectralOperator id).domain := fun k =>
    ⟨(u k).val, laguerre_minimal_le_spectral.1 (u k).property⟩
  let x : (laguerreSpectralOperator id).domain :=
    ⟨laguerreHilbertBasis n, laguerre_basis_mem_spectral_domain id n⟩
  have hv : Tendsto (fun k => (v k).val) atTop (𝓝 x.val) := by
    exact ((continuous_fst.tendsto _).comp ht).congr'
      (Eventually.of_forall fun k => (hu1 k).symm)
  have hAv : Tendsto (fun k => laguerreSpectralOperator id (v k)) atTop
      (𝓝 (laguerreSpectralOperator id x)) := by
    have hx : laguerreSpectralOperator id x = (n : ℂ) • laguerreHilbertBasis n :=
      laguerre_spectral_basis_action id n
    rw [hx]
    apply ((continuous_snd.tendsto _).comp ht).congr'
    apply Eventually.of_forall
    intro k
    exact (hu2 k).symm.trans (laguerre_minimal_le_spectral.2 (x := u k) rfl)
  have hroot := laguerre_square_root_tendsto_of_graph v x hv hAv
  have hsqrt : laguerreSpectralOperator Real.sqrt
      ⟨x.val, laguerre_integer_domain_le_square_root x.property⟩ =
      (Real.sqrt n : ℂ) • laguerreHilbertBasis n := laguerre_spectral_basis_action Real.sqrt n
  rw [hsqrt] at hroot
  apply mem_closure_of_tendsto (hv.prod_mk_nhds hroot)
  apply Eventually.of_forall
  intro k
  have hdom : (v k).val ∈ laguerreMinimalFormRoot.domain := by
    rw [laguerre_minimal_form_root_domain]
    exact (u k).property
  apply (LinearPMap.mem_graph_iff _).mpr
  refine ⟨⟨(v k).val,hdom⟩, rfl, ?_⟩
  exact laguerre_minimal_form_root_le.2 rfl

theorem laguerre_sqrt_graph_le_of_modes
    (G : Submodule ℂ (LaguerreWeightedHilbert × LaguerreWeightedHilbert))
    (hG : IsClosed (G : Set (LaguerreWeightedHilbert × LaguerreWeightedHilbert)))
    (hmodes : ∀ n : ℕ, (laguerreHilbertBasis n, (Real.sqrt n : ℂ) • laguerreHilbertBasis n) ∈ G) :
    (laguerreSpectralOperator Real.sqrt).graph ≤ G := by
  intro p hp
  obtain ⟨x,hx,hy⟩ := (LinearPMap.mem_graph_iff _).mp hp
  change (p.1,p.2) ∈ G
  rw [← hx, ← hy]
  have hsum := (laguerreHilbertBasis.hasSum_repr x.val).prod_mk
    (laguerre_spectral_action_hasSum Real.sqrt x)
  apply hG.mem_of_tendsto hsum
  apply Eventually.of_forall
  intro s
  apply G.sum_mem
  intro n _
  have h := G.smul_mem (laguerreCoefficient x.val n) (hmodes n)
  convert h using 1
  apply Prod.ext
  · rfl
  · change (((Real.sqrt n : ℂ) * laguerreCoefficient x.val n) • laguerreHilbertBasis n) =
      laguerreCoefficient x.val n • ((Real.sqrt n : ℂ) • laguerreHilbertBasis n)
    rw [smul_smul, mul_comm]

theorem laguerre_form_graph_approximation_of_modes
    (hmodes : ∀ n : ℕ, (laguerreHilbertBasis n, (n : ℂ) • laguerreHilbertBasis n) ∈
      laguerreMinimalOperator.graph.topologicalClosure)
    (x : (laguerreSpectralOperator Real.sqrt).domain) :
    (x.val, laguerreSpectralOperator Real.sqrt x) ∈
      laguerreMinimalFormRoot.graph.topologicalClosure :=
  laguerre_sqrt_graph_le_of_modes _ laguerreMinimalFormRoot.graph.isClosed_topologicalClosure
    (laguerre_form_mode_approximation hmodes) (LinearPMap.mem_graph _ x)

theorem laguerre_compact_form_sequence_of_modes
    (hmodes : ∀ n : ℕ, (laguerreHilbertBasis n, (n : ℂ) • laguerreHilbertBasis n) ∈
      laguerreMinimalOperator.graph.topologicalClosure)
    (x : (laguerreSpectralOperator Real.sqrt).domain) :
    ∃ u : ℕ → laguerreMinimalFormRoot.domain,
      Tendsto (fun k => (u k).val) atTop (𝓝 x.val) ∧
      Tendsto (fun k => laguerreMinimalFormRoot (u k)) atTop
        (𝓝 (laguerreSpectralOperator Real.sqrt x)) := by
  obtain ⟨p,hp,ht⟩ := mem_closure_iff_seq_limit.mp
    (laguerre_form_graph_approximation_of_modes hmodes x)
  choose u hu1 hu2 using fun k => (LinearPMap.mem_graph_iff _).mp (hp k)
  exact ⟨u, ((continuous_fst.tendsto _).comp ht).congr' (Eventually.of_forall fun k => (hu1 k).symm),
    ((continuous_snd.tendsto _).comp ht).congr' (Eventually.of_forall fun k => (hu2 k).symm)⟩

end
end Sigma
