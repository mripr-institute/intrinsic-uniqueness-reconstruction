import SigmaOpLaguerreSpectral
import Mathlib.Topology.Algebra.Module.LinearPMap

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology

theorem laguerre_spectral_graph_iff (f : ℝ → ℝ)
    (p : LaguerreWeightedHilbert × LaguerreWeightedHilbert) :
    p ∈ (laguerreSpectralOperator f).graph ↔
      ∀ n : ℕ, laguerreHilbertBasis.repr p.2 n =
        (f n : ℂ) * laguerreHilbertBasis.repr p.1 n := by
  constructor
  · intro hp
    obtain ⟨x,hx,hy⟩ := (LinearPMap.mem_graph_iff _).mp hp
    rw [← hx, ← hy]
    exact laguerre_spectral_coordinate f x
  · intro hp
    have hd : p.1 ∈ (laguerreSpectralOperator f).domain := by
      change Memℓp (fun n : ℕ => (f n : ℂ) * laguerreHilbertBasis.repr p.1 n) 2
      have he : (fun n : ℕ => (f n : ℂ) * laguerreHilbertBasis.repr p.1 n) =
          fun n => laguerreHilbertBasis.repr p.2 n := funext fun n => (hp n).symm
      rw [he]
      exact (laguerreHilbertBasis.repr p.2).property
    apply (LinearPMap.mem_graph_iff _).mpr
    refine ⟨⟨p.1,hd⟩, rfl, ?_⟩
    apply laguerreHilbertBasis.repr.injective
    apply lp.ext
    funext n
    rw [laguerre_spectral_coordinate, hp n]

theorem laguerre_coefficient_continuous (n : ℕ) :
    Continuous (fun x : LaguerreWeightedHilbert => laguerreHilbertBasis.repr x n) :=
  (continuous_apply n).comp (lp.uniformContinuous_coe.continuous.comp
    laguerreHilbertBasis.repr.continuous)

/-- The maximal spectral graph is genuinely closed in H times H. -/
theorem laguerre_spectral_closed (f : ℝ → ℝ) :
    (laguerreSpectralOperator f).IsClosed := by
  change IsClosed ((laguerreSpectralOperator f).graph :
    Set (LaguerreWeightedHilbert × LaguerreWeightedHilbert))
  have he : ((laguerreSpectralOperator f).graph :
      Set (LaguerreWeightedHilbert × LaguerreWeightedHilbert)) =
      ⋂ n : ℕ, {p | laguerreHilbertBasis.repr p.2 n =
        (f n : ℂ) * laguerreHilbertBasis.repr p.1 n} := by
    ext p
    simp only [mem_iInter, mem_setOf_eq]
    exact laguerre_spectral_graph_iff f p
  rw [he]
  exact isClosed_iInter fun n => isClosed_eq
    ((laguerre_coefficient_continuous n).comp continuous_snd)
    (continuous_const.mul ((laguerre_coefficient_continuous n).comp continuous_fst))

end
end Sigma
