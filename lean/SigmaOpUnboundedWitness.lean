import SigmaOpUnboundedWitnessIntegrability

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

/-- The explicit regularized log-log witness is a vector in the actual
canonical domain, established using the proved maximal-domain equivalence. -/
def laguerreUnboundedDomainVector : laguerreCanonicalOperator.domain :=
  ⟨laguerre_unbounded_representative_mem_l2.toLp laguerreUnboundedRepresentative,
    (laguerre_canonical_domain_iff_maximal _).mpr
      ⟨laguerreUnboundedRepresentative,(Memℒp.coeFn_toLp laguerre_unbounded_representative_mem_l2).symm,
        laguerre_unbounded_representative_locally_ac,laguerre_unbounded_flux_locally_ac,
        laguerre_unbounded_divergence_mem_l2⟩⟩

theorem laguerre_unbounded_domain_vector_representative :
    laguerreUnboundedRepresentative =ᵐ[gammaProbability]
      (laguerreUnboundedDomainVector.val : ℝ → ℂ) :=
  (Memℒp.coeFn_toLp laguerre_unbounded_representative_mem_l2).symm

/-- Every locally AC representative of this domain class diverges in real
part at zero. The failure of a finite boundary value is intrinsic to the class. -/
theorem laguerre_unbounded_domain_any_ac_representative (F : ℝ → ℂ)
    (hFx : F =ᵐ[gammaProbability] (laguerreUnboundedDomainVector.val : ℝ → ℂ))
    (hF : PositiveRayLocallyAbsolutelyContinuous F) :
    Tendsto (fun t => (F t).re) (𝓝[>] (0:ℝ)) atTop := by
  have he := hF.eqOn_of_ae laguerre_unbounded_representative_locally_ac
    (hFx.trans laguerre_unbounded_domain_vector_representative.symm)
  apply laguerre_unbounded_representative_tendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [he ht]

/-- No finite boundary value at zero may be imposed on the actual operator
domain: this explicit domain vector has no such locally AC representative. -/
theorem laguerre_domain_without_finite_boundary_value :
    ∃ x : laguerreCanonicalOperator.domain,
      (∃ F : ℝ → ℂ, F =ᵐ[gammaProbability] (x.val : ℝ → ℂ) ∧
        PositiveRayLocallyAbsolutelyContinuous F) ∧
      ∀ F : ℝ → ℂ, F =ᵐ[gammaProbability] (x.val : ℝ → ℂ) →
        PositiveRayLocallyAbsolutelyContinuous F →
        ¬∃ c : ℂ, Tendsto F (𝓝[>] (0:ℝ)) (𝓝 c) := by
  refine ⟨laguerreUnboundedDomainVector,
    ⟨laguerreUnboundedRepresentative,laguerre_unbounded_domain_vector_representative,
      laguerre_unbounded_representative_locally_ac⟩,?_⟩
  intro F hFx hF hc
  obtain ⟨c,hc⟩ := hc
  exact not_tendsto_nhds_of_tendsto_atTop (laguerre_unbounded_domain_any_ac_representative F hFx hF)
    c.re (Complex.continuous_re.continuousAt.tendsto.comp hc)

end
end Sigma
