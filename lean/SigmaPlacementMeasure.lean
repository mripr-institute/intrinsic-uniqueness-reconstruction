import SigmaPlacement
import SigmaProbSurvival

namespace Sigma
noncomputable section
open Filter Set MeasureTheory
open scoped Topology

def placedMassPrimitive (μ a r : ℝ) : ℝ :=
  -(Real.exp a/(1+a))*gammaSurvival (μ*r+a)

theorem placedMassPrimitive_deriv {μ a r : ℝ}
    (hμ : 0 < μ) (ha : 0 < a) (ht : 0 < μ*r+a) :
    HasDerivAt (placedMassPrimitive μ a) (Real.exp (placed μ a r)) r := by
  have hd := ((gamma_survival_derivative (μ*r+a)).comp r
    (((hasDerivAt_id r).const_mul μ).add_const a)).const_mul (-(Real.exp a/(1+a)))
  convert hd using 1
  rw [placed_density_identity hμ ha ht]
  unfold p
  ring

theorem placedMassPrimitive_continuous (μ a : ℝ) : Continuous (placedMassPrimitive μ a) := by
  have hs : Continuous gammaSurvival := continuous_iff_continuousAt.mpr
    (fun t => (gamma_survival_derivative t).continuousAt)
  exact continuous_const.mul (hs.comp ((continuous_const.mul continuous_id).add continuous_const))

theorem placedMassPrimitive_limit {μ a : ℝ} (hμ : 0 < μ) :
    Tendsto (placedMassPrimitive μ a) atTop (nhds 0) := by
  have hc : Tendsto (fun r : ℝ => μ*r+a) atTop atTop :=
    tendsto_atTop_add_const_right _ a (tendsto_id.const_mul_atTop hμ)
  unfold placedMassPrimitive
  simpa only [Function.comp_def, mul_zero] using
    (gamma_survival_tendsto.comp hc).const_mul (-(Real.exp a/(1+a)))

theorem placed_tail_mass {μ a c : ℝ}
    (hμ : 0 < μ) (ha : 0 < a) (hc : 0 ≤ μ*c+a) :
    (∫ r in Ioi c, Real.exp (placed μ a r)) =
      Real.exp a/(1+a)*gammaSurvival (μ*c+a) := by
  have hd : ∀ r ∈ Ioi c, HasDerivAt (placedMassPrimitive μ a)
      (Real.exp (placed μ a r)) r := by
    intro r hr
    apply placedMassPrimitive_deriv hμ ha
    have hp : 0 < μ*(r-c) := mul_pos hμ (sub_pos.mpr hr)
    nlinarith
  have hi := integral_Ioi_of_hasDerivAt_of_nonneg
    (placedMassPrimitive_continuous μ a).continuousAt.continuousWithinAt hd
    (fun r _ => (Real.exp_pos _).le) (placedMassPrimitive_limit hμ)
  simpa [placedMassPrimitive] using hi

theorem placed_nonnegative_ray_mass_one {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    (∫ r in Ioi (0 : ℝ), Real.exp (placed μ a r)) = 1 := by
  rw [placed_tail_mass hμ ha (by simpa using ha.le)]
  simp only [mul_zero, zero_add, gammaSurvival]
  have he : Real.exp a*Real.exp (-a) = 1 := by rw [← Real.exp_add]; simp
  calc
    _ = Real.exp a*Real.exp (-a) := by field_simp; ring
    _ = 1 := he

theorem placed_full_domain_mass {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    (∫ r in Ioi (-a/μ), Real.exp (placed μ a r)) = Real.exp a/(1+a) := by
  have hz : μ*(-a/μ)+a = 0 := by field_simp; ring
  rw [placed_tail_mass hμ ha (by rw [hz]), hz, gamma_survival_anchor, mul_one]

theorem placed_closed_nonnegative_ray_mass_one {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    (∫ r in Ici (0 : ℝ), Real.exp (placed μ a r)) = 1 := by
  rw [integral_Ici_eq_integral_Ioi]
  exact placed_nonnegative_ray_mass_one hμ ha

end
end Sigma
