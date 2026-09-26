import SigmaProbGammaProcessIndependence

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

/-- Any injective selection from a constant Gamma product has the selected
constant product law. -/
theorem gamma_process_product_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ℝ≥0) (e : κ ↪ ι) :
    (Measure.pi (fun _ : ι => gammaCompletion r)).map (fun x k => x (e k)) =
      Measure.pi (fun _ : κ => gammaCompletion r) := by
  have hi := gamma_process_independent_reindex _ _
    (gamma_process_product_coordinates_independent (fun _ : ι => r)) e
  rw [gamma_process_finite_joint_law _ _ (fun k => measurable_pi_apply (e k)) hi]
  simp_rw [gamma_process_product_coordinate_law]

theorem gamma_process_prefix_restrict {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] (P : Measure Ω) (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (r : ℝ≥0)
    (h : P.map (fun ω i => X i ω) = Measure.pi (fun _ : ι => gammaCompletion r))
    (e : κ ↪ ι) :
    P.map (fun ω k => X (e k) ω) = Measure.pi (fun _ : κ => gammaCompletion r) := by
  have hm : Measurable (fun x : ι → ℝ => fun k => x (e k)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  rw [← gamma_process_product_reindex r e, ← h,
    Measure.map_map hm (measurable_pi_lambda _ hX)]
  rfl

theorem gamma_process_prefix_marginal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (r : ℝ≥0)
    (h : ∀ K, P.map (fun ω (i : Fin K) => X i ω) =
      Measure.pi (fun _ : Fin K => gammaCompletion r)) (i : ℕ) :
    P.map (X i) = gammaCompletion r := by
  have hh := congrArg (fun μ : Measure (Fin (i+1) → ℝ) =>
    μ.map (fun x => x ⟨i,Nat.lt_succ_self i⟩)) (h (i+1))
  dsimp only at hh
  rw [Measure.map_map (measurable_pi_apply _) (measurable_pi_lambda _ (fun j : Fin (i+1) => hX j)),
    gamma_process_product_coordinate_law] at hh
  exact hh

/-- Prefix product laws establish independence of the entire countable family. -/
theorem gamma_process_prefix_independent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (r : ℝ≥0)
    (h : ∀ K, P.map (fun ω (i : Fin K) => X i ω) =
      Measure.pi (fun _ : Fin K => gammaCompletion r)) :
    iIndepFun (fun _ => inferInstance) X P := by
  classical
  apply gamma_process_independent_of_finite_joint_laws P X hX
  intro S
  let K := S.sup id + 1
  let e : S ↪ Fin K := ⟨fun i => ⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)⟩,
    fun i j hij => Subtype.ext (congrArg Fin.val hij)⟩
  have hh := gamma_process_prefix_restrict P (fun i : Fin K => X i)
    (fun i => hX i) r (h K) e
  simpa only [gamma_process_prefix_marginal P X hX r h] using hh

end
end Sigma
