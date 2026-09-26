import SigmaProbGammaProcessIndependence
import SigmaProbGammaProcessDyadic

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators

/-- Flatten the two children of each of finitely many parent increments. -/
def gammaProcessPairFlatten (K : ℕ) (z : Fin K → ℝ × ℝ) (j : Fin (K*2)) : ℝ :=
  if (finProdFinEquiv.symm j).2 = (0 : Fin 2) then (z (finProdFinEquiv.symm j).1).1
  else (z (finProdFinEquiv.symm j).1).2

theorem gamma_process_pair_flatten_measurable (K : ℕ) : Measurable (gammaProcessPairFlatten K) := by
  apply measurable_pi_lambda
  intro j
  unfold gammaProcessPairFlatten
  split_ifs
  · exact measurable_fst.comp (measurable_pi_apply _)
  · exact measurable_snd.comp (measurable_pi_apply _)

theorem gamma_process_pair_flatten_product (K : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (Measure.pi (fun _ : Fin K => μ.prod μ)).map (gammaProcessPairFlatten K) =
      Measure.pi (fun _ : Fin (K*2) => μ) := by
  classical
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (gamma_process_pair_flatten_measurable K) (MeasurableSet.univ_pi hs)]
  have he : gammaProcessPairFlatten K ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun k : Fin K => s (finProdFinEquiv (k,0)) ×ˢ s (finProdFinEquiv (k,1))) := by
    ext z
    simp only [mem_preimage, mem_univ_pi, mem_prod]
    constructor
    · intro h k
      constructor
      · simpa [gammaProcessPairFlatten] using h (finProdFinEquiv (k,0))
      · simpa [gammaProcessPairFlatten] using h (finProdFinEquiv (k,1))
    · intro h j
      obtain ⟨⟨k,i⟩,rfl⟩ := finProdFinEquiv.surjective j
      fin_cases i
      · simpa [gammaProcessPairFlatten] using (h k).1
      · simpa [gammaProcessPairFlatten] using (h k).2
  rw [he, Measure.pi_pi]
  simp_rw [Measure.prod_prod]
  rw [← (finProdFinEquiv : Fin K × Fin 2 ≃ Fin (K*2)).prod_comp
    (fun j => μ (s j)), Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro k hk
  rw [Fin.prod_univ_two]

/-- Apply the native one-parent splitting law simultaneously to a finite
independent vector, obtaining the refined scalar Gamma product. -/
theorem gamma_process_split_product_law (K : ℕ) (r : ℝ≥0) (β : Measure ℝ)
    [IsProbabilityMeasure β]
    (hsplit : ((gammaCompletion r).prod β).map
      (fun p : ℝ × ℝ => (p.1*p.2,p.1*(1-p.2))) =
      (gammaCompletion (r/2)).prod (gammaCompletion (r/2))) :
    (Measure.pi (fun _ : Fin K => (gammaCompletion r).prod β)).map
      (fun z => gammaProcessPairFlatten K (fun k => ((z k).1*(z k).2,(z k).1*(1-(z k).2)))) =
      Measure.pi (fun _ : Fin (K*2) => gammaCompletion (r/2)) := by
  have hm : Measurable (fun p : ℝ×ℝ => (p.1*p.2,p.1*(1-p.2))) := by fun_prop
  have hp := measurePreserving_pi
    (fun _ : Fin K => (gammaCompletion r).prod β)
    (fun _ : Fin K => (gammaCompletion (r/2)).prod (gammaCompletion (r/2)))
    (fun _ => (⟨hm, hsplit⟩ : MeasurePreserving
      (fun p : ℝ×ℝ => (p.1*p.2,p.1*(1-p.2))) _ _))
  change (Measure.pi (fun _ : Fin K => (gammaCompletion r).prod β)).map
    (gammaProcessPairFlatten K ∘ (fun z k => ((z k).1*(z k).2,(z k).1*(1-(z k).2)))) = _
  rw [← Measure.map_map (gamma_process_pair_flatten_measurable K) hp.measurable,
    hp.map_eq, gamma_process_pair_flatten_product]

end
end Sigma
