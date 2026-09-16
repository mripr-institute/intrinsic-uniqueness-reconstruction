import SigmaPlacementMeasure

namespace Sigma
noncomputable section
open Set

/-- A placed presentation carries its admissible scale and offset together.
The fields below package the already proved coordinate bijection, local
parameter recovery, density identity, and normalization facts without
changing any of their hypotheses. -/
structure PlacedParameters where
  μ : ℝ
  a : ℝ
  hμ : 0 < μ
  ha : 0 < a

namespace PlacedParameters

def presentation (P : PlacedParameters) (r : ℝ) : ℝ :=
  placed P.μ P.a r

theorem coordinate_bijective (P : PlacedParameters) :
    BijOn (fun r : ℝ => P.μ * r + P.a)
      (Ioi (-P.a / P.μ)) (Ioi 0) :=
  placed_coordinate_bijective P.hμ

theorem original_identity (P : PlacedParameters) (r : ℝ)
    (hr : 0 < P.μ * r + P.a) :
    placedOriginal P.μ (P.μ / P.a) r = P.presentation r := by
  exact placed_original_identity P.hμ P.ha hr

theorem parameter_recovery (P : PlacedParameters) (r : ℝ)
    (hr : 0 < P.μ * r + P.a) :
    Real.sqrt (-deriv (deriv P.presentation) r) - deriv P.presentation r = P.μ ∧
    Real.sqrt (-deriv (deriv P.presentation) r) /
      (1 - r * Real.sqrt (-deriv (deriv P.presentation) r)) = P.μ / P.a := by
  simpa [presentation] using placed_parameter_recovery P.hμ P.ha hr

theorem density_identity (P : PlacedParameters) (r : ℝ)
    (hr : 0 < P.μ * r + P.a) :
    Real.exp (P.presentation r) =
      P.μ * Real.exp P.a / (1 + P.a) * p (P.μ * r + P.a) := by
  exact placed_density_identity P.hμ P.ha hr

theorem positive_ray_mass_one (P : PlacedParameters) :
    (∫ r in Ioi (0 : ℝ), Real.exp (P.presentation r)) = 1 := by
  exact placed_nonnegative_ray_mass_one P.hμ P.ha

theorem full_domain_mass (P : PlacedParameters) :
    (∫ r in Ioi (-P.a / P.μ), Real.exp (P.presentation r)) =
      Real.exp P.a / (1 + P.a) := by
  exact placed_full_domain_mass P.hμ P.ha

end PlacedParameters

end
end Sigma
