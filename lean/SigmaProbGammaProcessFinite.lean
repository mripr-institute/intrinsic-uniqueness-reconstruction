import SigmaProbCompletionProcess

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

/-- Adding independent Gamma increments adds their time parameters, on the
actual underlying probability space. -/
theorem gamma_process_independent_add_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (r s : ℝ≥0) (hr : P.map X = gammaCompletion r) (hs : P.map Y = gammaCompletion s) :
    P.map (fun ω => X ω+Y ω) = gammaCompletion (r+s) := by
  have hp := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp hXY
  rw [hr, hs] at hp
  rw [← gamma_completion_convolution, independentAffineSum, ← hp,
    Measure.map_map (by fun_prop) (hX.prod_mk hY)]
  congr 1
  funext ω
  simp

/-- Any finite block of independent increments has the Gamma law corresponding
to its total duration. This includes the empty block and zero durations. -/
theorem gamma_process_finset_sum_law {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hi : iIndepFun (fun _ => inferInstance) X P)
    (d : ι → ℝ≥0) (hlaw : ∀ i, P.map (X i) = gammaCompletion (d i)) (S : Finset ι) :
    P.map (fun ω => ∑ i ∈ S, X i ω) = gammaCompletion (∑ i ∈ S, d i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [gamma_completion_zero, Measure.map_const]
  | @insert i S hiS ih =>
    simp only [Finset.sum_insert hiS]
    apply gamma_process_independent_add_law P (X i) (fun ω => ∑ j ∈ S, X j ω)
      (hX i) (Finset.measurable_sum _ fun j hj => hX j)
    · have hh := (hi.indepFun_finset_sum_of_not_mem hX hiS).symm
      have he : (∑ j ∈ S, X j) = (fun ω => ∑ j ∈ S, X j ω) := by
        funext ω
        simp
      rwa [he] at hh
    · exact hlaw i
    · exact ih

/-- Exact marginal law of a coordinate of the literal Gamma product. -/
theorem gamma_process_product_coordinate_law {ι : Type*} [Fintype ι]
    (d : ι → ℝ≥0) (i : ι) : (Measure.pi (fun i => gammaCompletion (d i))).map
      (fun x : ι → ℝ => x i) = gammaCompletion (d i) := by
  classical
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  have he : (fun x : ι → ℝ => x i) ⁻¹' s =
      Set.pi Set.univ (fun j => if j = i then s else Set.univ) := by
    ext x
    simp
  rw [he, Measure.pi_pi]
  simp only [apply_ite, measure_univ]
  simp

/-- Coordinates under the literal finite product measure are independent. -/
theorem gamma_process_product_coordinates_independent {ι : Type*} [Fintype ι]
    (d : ι → ℝ≥0) : iIndepFun (fun _ : ι => inferInstance)
      (fun i (x : ι → ℝ) => x i) (Measure.pi (fun i => gammaCompletion (d i))) := by
  classical
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S sets hs
  have he : (⋂ i ∈ S, (fun x : ι → ℝ => x i) ⁻¹' sets i) =
      Set.pi Set.univ (fun i => if i ∈ S then sets i else Set.univ) := by
    ext x
    simp
  rw [he, Measure.pi_pi]
  have hm := gamma_process_product_coordinate_law d
  rw [← Finset.prod_mul_prod_compl S]
  have hc : (∏ i ∈ Sᶜ, gammaCompletion (d i) (if i ∈ S then sets i else Set.univ)) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    simp [(Finset.mem_compl.mp hi)]
  rw [hc, mul_one]
  apply Finset.prod_congr rfl
  intro i hi
  rw [if_pos hi, ← hm i, Measure.map_apply (measurable_pi_apply i) (hs i hi)]

end
end Sigma
