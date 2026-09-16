import SigmaRealTreesGenerating
import SigmaRealTreesRadius
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness

namespace Sigma
noncomputable section
open PowerSeries Filter Set
open scoped Topology BigOperators

def borelInverse (t : ℝ) : ℝ := t * Real.exp (1 - t)

theorem borel_inverse_derivative (t : ℝ) :
    HasDerivAt borelInverse (Real.exp (1 - t) * (1 - t)) t := by
  convert (hasDerivAt_id t).mul (((hasDerivAt_const t (1 : ℝ)).sub
    (hasDerivAt_id t)).exp) using 1
  simp [borelInverse]
  ring

theorem borel_inverse_strictMono : StrictMonoOn borelInverse (Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact fun t _ => (borel_inverse_derivative t).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(borel_inverse_derivative t).deriv]
    exact mul_pos (Real.exp_pos _) (sub_pos.mpr ht.2)

theorem borel_inverse_mem_unit (t : ℝ) (ht : t ∈ Icc 0 1) :
    borelInverse t ∈ Icc 0 1 := by
  have h0 := borel_inverse_strictMono.monotoneOn (show (0 : ℝ) ∈ Icc 0 1 by norm_num) ht ht.1
  have h1 := borel_inverse_strictMono.monotoneOn ht (show (1 : ℝ) ∈ Icc 0 1 by norm_num) ht.2
  simpa [borelInverse] using And.intro h0 h1

theorem borel_generating_right_inverse (s : ℝ) (hs : s ∈ Icc 0 1) :
    borelInverse (borelGenerating s) = s := by
  have h := borel_generating_fixed_point s hs.1 hs.2
  unfold borelInverse
  calc
    borelGenerating s * Real.exp (1 - borelGenerating s) =
        s * (Real.exp (borelGenerating s - 1) * Real.exp (1 - borelGenerating s)) := by
      linear_combination Real.exp (1 - borelGenerating s) * h
    _ = s := by rw [← Real.exp_add]; simp

theorem borel_generating_left_inverse (t : ℝ) (ht : t ∈ Icc 0 1) :
    borelGenerating (borelInverse t) = t := by
  have hs := borel_inverse_mem_unit t ht
  apply borel_inverse_strictMono.injOn
    ⟨borel_generating_nonnegative _ hs.1, borel_generating_le_one _ hs.1 hs.2⟩ ht
  exact borel_generating_right_inverse _ hs

theorem rooted_analytic_sum (z : ℝ) :
    rootedAnalyticSeries.sum z = ∑' n, coeff ℝ n (rootedSeries ℝ) * z ^ n := by
  exact FormalMultilinearSeries.ofScalars_sum_eq _ z

theorem rooted_generating_analytic (z : ℝ) (hz : |z| < Real.exp (-1)) :
    AnalyticAt ℝ rootedAnalyticSeries.sum z := by
  have hr : 0 < rootedAnalyticSeries.radius := by
    rw [rooted_series_convergence_radius]
    exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  apply (rootedAnalyticSeries.hasFPowerSeriesOnBall hr).analyticAt_of_mem
  rw [EMetric.mem_ball, rooted_series_convergence_radius, edist_dist, Real.dist_eq, sub_zero]
  exact (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).mpr hz

theorem borel_generating_rescaled_rooted (s : ℝ) :
    borelGenerating s = rootedAnalyticSeries.sum (s * Real.exp (-1)) := by
  rw [borelGenerating, rooted_analytic_sum]
  apply tsum_congr
  intro n
  rw [borelCoefficient, borelSeries, coeff_rescale, mul_pow]
  ring

theorem borel_generating_analytic (s : ℝ) (hs : |s| < 1) :
    AnalyticAt ℝ borelGenerating s := by
  have hz : |s * Real.exp (-1)| < Real.exp (-1) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_lt_mul_of_pos_right hs (Real.exp_pos _)).trans_eq (one_mul _)
  have ha := (rooted_generating_analytic _ hz).comp
    (f := fun x : ℝ => x * Real.exp (-1)) ((analyticAt_id (𝕜 := ℝ) (z := s)).mul (analyticAt_const (v := Real.exp (-1))))
  have he : borelGenerating = fun x => rootedAnalyticSeries.sum (x * Real.exp (-1)) :=
    funext borel_generating_rescaled_rooted
  rw [he]
  exact ha


theorem borel_generating_fixed_point_signed (s : ℝ) (hs : |s| < 1) :
    borelGenerating s = s * Real.exp (borelGenerating s - 1) := by
  have hb : AnalyticOnNhd ℝ borelGenerating (Ioo (-1) 1) := by
    intro x hx
    exact borel_generating_analytic x (abs_lt.mpr hx)
  have he : AnalyticOnNhd ℝ (fun x => x * Real.exp (borelGenerating x - 1)) (Ioo (-1) 1) := by
    intro x hx
    exact analyticAt_id.mul ((analyticOnNhd_rexp _ (mem_univ _)).comp
      ((hb x hx).sub analyticAt_const))
  have hg : borelGenerating =ᶠ[𝓝 (1 / 2 : ℝ)]
      (fun x => x * Real.exp (borelGenerating x - 1)) := by
    filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 1 by norm_num)] with x hx
    exact borel_generating_fixed_point x hx.1.le hx.2.le
  exact hb.eqOn_of_preconnected_of_eventuallyEq he (convex_Ioo (-1 : ℝ) 1).isPreconnected
    (show (1 / 2 : ℝ) ∈ Ioo (-1) 1 by norm_num) hg (abs_lt.mp hs)

theorem borel_inverse_strictMono_below_one : StrictMonoOn borelInverse (Iio 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Iio _)
  · exact fun t _ => (borel_inverse_derivative t).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Iio] at ht
    rw [(borel_inverse_derivative t).deriv]
    exact mul_pos (Real.exp_pos _) (sub_pos.mpr ht)

theorem borel_generating_right_inverse_signed (s : ℝ) (hs : |s| < 1) :
    borelInverse (borelGenerating s) = s := by
  have h := borel_generating_fixed_point_signed s hs
  unfold borelInverse
  calc
    borelGenerating s * Real.exp (1 - borelGenerating s) =
        s * (Real.exp (borelGenerating s - 1) * Real.exp (1 - borelGenerating s)) := by
      linear_combination Real.exp (1 - borelGenerating s) * h
    _ = s := by rw [← Real.exp_add]; simp

theorem borel_inverse_analytic_germs :
    (fun s => borelInverse (borelGenerating s)) =ᶠ[𝓝 (0 : ℝ)] id ∧
    (fun t => borelGenerating (borelInverse t)) =ᶠ[𝓝 (0 : ℝ)] id := by
  have hB : ContinuousAt borelGenerating 0 :=
    (borel_generating_analytic 0 (by norm_num)).continuousAt
  have hi : ContinuousAt borelInverse 0 := (borel_inverse_derivative 0).continuousAt
  have hi0 : borelInverse 0 = 0 := by simp [borelInverse]
  have hB0 : borelGenerating (borelInverse 0) < 1 := by rw [hi0, borel_generating_zero]; norm_num
  constructor
  · filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact borel_generating_right_inverse_signed s (abs_lt.mpr hs)
  · have harg : ∀ᶠ t in 𝓝 (0 : ℝ), borelInverse t ∈ Ioo (-1) 1 :=
      hi.eventually (Ioo_mem_nhds (by rw [hi0]; norm_num) (by rw [hi0]; norm_num))
    have hval : ∀ᶠ t in 𝓝 (0 : ℝ), borelGenerating (borelInverse t) ∈ Iio 1 := by
      exact (hB.comp_of_eq hi hi0).eventually (isOpen_Iio.mem_nhds hB0)
    filter_upwards [harg, hval, isOpen_Iio.mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht hv hlt
    apply borel_inverse_strictMono_below_one.injOn hv hlt
    exact borel_generating_right_inverse_signed _ (abs_lt.mpr ht)


def rootedInverse (t : ℝ) : ℝ := t * Real.exp (-t)

theorem marked_borel_inverse_scale (t : ℝ) :
    borelInverse t = rootedInverse t * Real.exp 1 := by
  simp only [borelInverse, rootedInverse, sub_eq_add_neg, Real.exp_add]
  ring

theorem rooted_generating_scaled_borel (z : ℝ) :
    rootedAnalyticSeries.sum z = borelGenerating (z * Real.exp 1) := by
  rw [borel_generating_rescaled_rooted]
  congr 1
  rw [mul_assoc, ← Real.exp_add]
  norm_num

theorem rooted_inverse_analytic_germs :
    (fun z => rootedInverse (rootedAnalyticSeries.sum z)) =ᶠ[𝓝 (0 : ℝ)] id ∧
    (fun t => rootedAnalyticSeries.sum (rootedInverse t)) =ᶠ[𝓝 (0 : ℝ)] id := by
  have ht : Tendsto (fun z : ℝ => z * Real.exp 1) (𝓝 0) (𝓝 0) := by
    simpa only [zero_mul, id_eq] using
      ((continuousAt_id (x := (0 : ℝ))).mul_const (Real.exp 1))
  constructor
  · have hg := borel_inverse_analytic_germs.1.comp_tendsto ht
    filter_upwards [hg] with z hz
    apply mul_right_cancel₀ (Real.exp_ne_zero 1)
    rw [rooted_generating_scaled_borel, ← marked_borel_inverse_scale]
    exact hz
  · filter_upwards [borel_inverse_analytic_germs.2] with t ht
    rw [rooted_generating_scaled_borel, ← marked_borel_inverse_scale]
    exact ht

theorem inverse_germ_identifies_analytic_density (f : ℝ → ℝ)
    (hf : AnalyticOnNhd ℝ f (Ioi 0)) (δ : ℝ) (hδ : 0 < δ)
    (hgerm : ∀ t, 0 < t → t < δ → f t = t * Real.exp (-t)) :
    ∀ t, 0 < t → f t = t * Real.exp (-t) := by
  have hp : AnalyticOnNhd ℝ (fun t : ℝ => t * Real.exp (-t)) (Ioi 0) := by
    intro t _
    exact analyticAt_id.mul ((analyticOnNhd_rexp _ (mem_univ _)).comp analyticAt_id.neg)
  have hg : f =ᶠ[𝓝 (δ / 2)] (fun t => t * Real.exp (-t)) := by
    filter_upwards [Ioo_mem_nhds (show 0 < δ / 2 by linarith) (show δ / 2 < δ by linarith)] with t ht
    exact hgerm t ht.1 ht.2
  exact hf.eqOn_of_preconnected_of_eventuallyEq hp (convex_Ioi 0).isPreconnected
    (show δ / 2 ∈ Ioi 0 by change 0 < δ / 2; linarith) hg

end
end Sigma
