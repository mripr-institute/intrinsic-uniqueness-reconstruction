import SigmaOpNonnegativeMixing
import SigmaOpResolventHeatSemigroup

namespace Sigma
noncomputable section
open Set MeasureTheory
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual exponential is constructed from the native self-adjoint
operator and has its generator on the entire native domain. -/
theorem op_nonnegative_heat_evolution (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) :
    OpContractionEvolution B (opNonnegativeHeat B hsa hB) :=
  op_resolvent_heat_contraction_evolution B _ (op_nonnegative_shift_resolvent B hsa hB)
    (op_nonnegative_resolvent_selfAdjoint B hsa hB)
    (op_nonnegative_resolvent_spectrum B hsa hB)
    (op_nonnegative_resolvent_norm B hsa hB)
    (op_nonnegative_resolvent_dense_range B hsa hB)

theorem op_nonnegative_heat_semigroup (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    opNonnegativeHeat B hsa hB (s+t) =
      opNonnegativeHeat B hsa hB s * opNonnegativeHeat B hsa hB t :=
  resolvent_heat_operator_add _ (op_nonnegative_resolvent_selfAdjoint B hsa hB)
    (op_nonnegative_resolvent_spectrum B hsa hB) hs ht

theorem op_nonnegative_complex_orbit_integrable (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B)
    (μ : Measure OpNonnegativeRay) [IsFiniteMeasure μ] (x : H) :
    Integrable (fun s : OpNonnegativeRay => opNonnegativeHeat B hsa hB s.val x) μ :=
  op_evolution_finite_measure_integrable B _ (op_nonnegative_heat_evolution B hsa hB) μ x

/-- The displayed Gamma recipe is also a solution as the original native
complex Borel measure, not merely a scalar density integral. -/
theorem op_nonnegative_gamma_complex_mixing (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) (x : H) :
    complexStrongIntegral nonnegativeGammaComplexMeasure
      (fun s => opNonnegativeHeat B hsa hB s.val x) =
        opNonnegativeResolvent B hsa hB (opNonnegativeResolvent B hsa hB x) := by
  rw [nonnegative_gamma_complex_strong_integral, nonnegativeGammaMixingMeasure]
  have hc : Continuous (fun s : OpNonnegativeRay => opNonnegativeHeat B hsa hB s.val x) :=
    ((op_nonnegative_heat_evolution B hsa hB).continuous_orbit x).restrict
  letI : SecondCountableTopologyEither OpNonnegativeRay H := ⟨Or.inl inferInstance⟩
  rw [integral_map nonnegative_gamma_coordinate_measurable.aemeasurable hc.aestronglyMeasurable]
  have he : (∫ t : ℝ, opNonnegativeHeat B hsa hB (nonnegativeGammaCoordinate t).val x
      ∂gammaProbability) = ∫ t : ℝ, opNonnegativeHeat B hsa hB t x ∂gammaProbability := by
    apply integral_congr_ae
    filter_upwards [operator_integer_samples_ae_pos gammaProbability
      operator_gamma_probability_integer_samples] with t ht
    simp only [nonnegativeGammaCoordinate, max_eq_left ht.le]
  rw [he]
  exact op_nonnegative_gamma_probability_mixing B hsa hB x

/-- Exact existence and uniqueness of the unknown finite complex measure.
Only one nonzero eigenvector per integer is required. -/
theorem op_nonnegative_complex_mixing_iff (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B)
    (heigen : ∀ n : ℕ, ∃ x : B.domain, x.val ≠ 0 ∧ B x = (n : ℂ) • x.val)
    (μ : ComplexMeasure OpNonnegativeRay) :
    (∀ x : H, complexStrongIntegral μ (fun s => opNonnegativeHeat B hsa hB s.val x) =
      opNonnegativeResolvent B hsa hB (opNonnegativeResolvent B hsa hB x)) ↔
        μ = nonnegativeGammaComplexMeasure := by
  constructor
  · exact op_nonnegative_complex_mixing_unique B hsa hB μ heigen
  · rintro rfl
    exact op_nonnegative_gamma_complex_mixing B hsa hB

end
end Sigma
