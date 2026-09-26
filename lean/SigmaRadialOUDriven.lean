import SigmaRadialOUBrownian
import SigmaRadialOUPaths

/-!
Construction of the actual OU paths from supplied Brownian paths. The output
satisfies the additive-noise SDE in integral form on one common full-measure
event. Existence of the Brownian probability space, and the radial stochastic
integral identity, remain separate requirements.
-/

namespace Sigma
noncomputable section
open MeasureTheory
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Extend the Brownian path constantly to negative times, then apply the
explicit Bochner-convolution solution. The result is evaluated at nonnegative
time. -/
def radialOUDriven (D : ℕ) (z : EuclideanSpace ℝ (Fin D))
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D))
    (t : ℝ≥0) (ω : Ω) : EuclideanSpace ℝ (Fin D) :=
  ouPath z (fun s => B s.toNNReal ω) t

theorem radial_ou_driven_paths {D : ℕ} {P : Measure Ω}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D)}
    (hB : IsRadialBrownian D P B) (z : EuclideanSpace ℝ (Fin D)) :
    ∀ᵐ ω ∂P,
      Continuous (fun t => radialOUDriven D z B t ω) ∧
      radialOUDriven D z B 0 ω = z ∧
      ∀ t : ℝ≥0, radialOUDriven D z B t ω = z + B t ω +
        ∫ s in (0 : ℝ)..(t : ℝ),
          -(1 / 2 : ℝ) • ouPath z (fun r => B r.toNNReal ω) s := by
  filter_upwards [hB.continuous, hB.zero] with ω hcont hzero
  have hc : Continuous (fun s : ℝ => B s.toNNReal ω) :=
    hcont.comp continuous_real_toNNReal
  refine ⟨(ou_path_continuous z _ hc).comp continuous_subtype_val, ?_, ?_⟩
  · exact ou_path_initial z _ (by simpa using hzero)
  · intro t
    simpa only [radialOUDriven, Real.toNNReal_coe] using
      ou_path_integral_equation z (fun r => B r.toNNReal ω) hc (t : ℝ)

end
end Sigma
