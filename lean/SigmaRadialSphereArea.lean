import SigmaRadialSpherePolar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace Sigma
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

/-- The exact geometric volume used in the four-dimensional polar calculation. -/
theorem radial_four_unit_ball_volume :
    (volume : Measure (EuclideanSpace ℝ (Fin 4))) (ball 0 1) =
      ENNReal.ofReal (Real.pi^2/2) := by
  rw [EuclideanSpace.volume_ball]
  norm_num only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  have hg : Real.Gamma (3 : ℝ) = 2 := by
    simpa using Real.Gamma_nat_eq_factorial 2
  rw [hg]
  congr 1
  rw [show (4:ℕ)=2*2 by norm_num, pow_mul, Real.sq_sqrt Real.pi_pos.le]

/-- The actual surface measure of S³ is 2π², as used in the paper. -/
theorem radial_four_surface_area :
    radialFourSurface univ = ENNReal.ofReal (2*Real.pi^2) := by
  rw [radialFourSurface, Measure.toSphere_apply_univ, radial_four_unit_ball_volume]
  norm_num only [finrank_euclideanSpace, Fintype.card_fin]
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end
end Sigma
