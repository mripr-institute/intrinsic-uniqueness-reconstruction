import SigmaProbDeficitRecurrence
import SigmaProbCanonicalPair

namespace Sigma
noncomputable section
open MeasureTheory Set
open scoped ENNReal

def rayDeficitLaw (J : ℝ → ℝ) : Measure ℝ :=
  Measure.map (positiveRayExtension J)
    ((volume.restrict (Ioi 0)).withDensity
      (deficitWeight ∘ positiveRayExtension J))

/-- The complete explicit Euler/zeta algebraic cumulant list may replace
equality with the canonical deficit law in the linked inverse theorem. -/
theorem canonical_deficit_pair_identifies_from_explicit_cumulants
    (J : ℝ → ℝ) (hJ : RayPotential J)
    (hpair : ∀ b ≥ 1,
      0 < canonicalDeficitInvolution b ∧ canonicalDeficitInvolution b ≤ 1 ∧
        J (canonicalDeficitInvolution b) = J b)
    (hprob : IsProbabilityMeasure (rayDeficitLaw J))
    (hi : ∀ n : ℕ, Integrable (fun v : ℝ => v ^ n) (rayDeficitLaw J))
    (hcumulants : AlgebraicCumulantRecurrence (rayDeficitLaw J) deficitCumulantValue) :
    ∀ t > 0,
      J t = SigmaBase.potential t ∧
        Real.exp (-1 - J t) = SigmaPresentations.density t := by
  letI : IsProbabilityMeasure (rayDeficitLaw J) := hprob
  have hlaw : rayDeficitLaw J = gammaDeficitProbability :=
    gamma_deficit_explicit_algebraic_cumulants_identify
      (rayDeficitLaw J) hi hcumulants
  apply canonical_deficit_pair_identifies_on_positive_ray J hJ hpair
  simpa only [rayDeficitLaw] using hlaw

end
end Sigma
