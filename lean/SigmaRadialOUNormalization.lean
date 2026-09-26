import SigmaEuclideanLaplacian
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
The everywhere-defined normalization used in the radial OU construction.
This file proves only properties of the actual integrand. It does not assert
the existence of a stochastic integral or a Brownian motion.
-/

namespace Sigma
noncomputable section
open MeasureTheory
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Normalize off zero, and use the designated unit vector at zero. -/
def radialOUNormalize (e z : V) : V := by
  classical
  exact if z = 0 then e else ‖z‖⁻¹ • z

theorem radial_ou_normalize_norm (e z : V) (he : ‖e‖ = 1) :
    ‖radialOUNormalize e z‖ = 1 := by
  by_cases hz : z = 0
  · simp [radialOUNormalize, hz, he]
  · simp only [radialOUNormalize, if_neg hz]
    exact norm_smul_inv_norm hz

theorem radial_ou_normalize_reconstruct (e z : V) :
    ‖z‖ • radialOUNormalize e z = z := by
  by_cases hz : z = 0
  · simp [hz]
  · simp only [radialOUNormalize, if_neg hz, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]

theorem radial_ou_normalize_energy_reconstruct (e z : V) :
    Real.sqrt (2 * (‖z‖ ^ 2 / 2)) • radialOUNormalize e z = z := by
  rw [show 2 * (‖z‖ ^ 2 / 2) = ‖z‖ ^ 2 by ring,
    Real.sqrt_sq (norm_nonneg z)]
  exact radial_ou_normalize_reconstruct e z

theorem radial_ou_normalize_inner (e z v : V) :
    ⟪z, v⟫_ℝ = ‖z‖ * ⟪radialOUNormalize e z, v⟫_ℝ := by
  rw [← real_inner_smul_left, radial_ou_normalize_reconstruct]

variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

theorem radial_ou_normalize_measurable (e : V) : Measurable (radialOUNormalize e) := by
  classical
  exact Measurable.ite (measurableSet_singleton (0 : V)) measurable_const
    (measurable_id.norm.inv.smul measurable_id)

theorem radial_ou_normalize_progressive {Ω ι : Type*} [MeasurableSpace Ω]
    [Preorder ι] [MeasurableSpace ι] (ℱ : Filtration ι ‹MeasurableSpace Ω›)
    (Z : ι → Ω → V) (hZ : ProgMeasurable ℱ Z) (e : V) :
    ProgMeasurable ℱ (fun t ω => radialOUNormalize e (Z t ω)) := by
  intro t
  exact ((radial_ou_normalize_measurable e).comp (hZ t).measurable).stronglyMeasurable

end
end Sigma
