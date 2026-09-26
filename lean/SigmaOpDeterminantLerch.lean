import SigmaOpDeterminantZetaHalf
import SigmaOpDeterminantZetaRemainder
import SigmaOpDeterminantZetaPrime

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology BigOperators

/-- The entire function extending `s ζ(s+1)` across its removable singularity. -/
def zetaPoleRemoved (s : ℂ) : ℂ :=
  s*(riemannZeta (s+1)-1/s/Complex.Gammaℝ (s+1)) + (Complex.Gammaℝ (s+1))⁻¹

theorem zeta_pole_removed_eq (s : ℂ) (hs : s ≠ 0) :
    zetaPoleRemoved s = s*riemannZeta (s+1) := by
  simp [zetaPoleRemoved, div_eq_mul_inv, mul_sub, ← mul_assoc, hs]


theorem zeta_pole_removed_differentiable : Differentiable ℂ zetaPoleRemoved := by
  intro s
  by_cases hs : s = 0
  · subst s
    have hr := HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div (0 : UnitAddCircle)
    rw [HurwitzZeta.hurwitzZeta_zero] at hr
    have hc := (show DifferentiableAt ℂ (fun x => riemannZeta x-1/(x-1)/Complex.Gammaℝ x)
      ((0 : ℂ)+1) by simpa using hr).comp (0 : ℂ) ((differentiableAt_id).add_const 1)
    have hc' : DifferentiableAt ℂ (fun s : ℂ => riemannZeta (s+1)-1/s/Complex.Gammaℝ (s+1)) 0 := by
      simpa only [Function.comp_def, id_eq, add_sub_cancel_right] using hc
    exact (differentiableAt_id.mul hc').add
      ((Complex.differentiable_Gammaℝ_inv (0+1)).comp 0 (differentiableAt_id.add_const 1))
  · have hd : DifferentiableAt ℂ (fun s : ℂ => s*riemannZeta (s+1)) s := by
      exact differentiableAt_id.mul
        ((differentiableAt_riemannZeta (by simpa using hs)).comp s (differentiableAt_id.add_const 1))
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hs] with z hz
    exact zeta_pole_removed_eq z hz

theorem zeta_regular_series_spectral (a : ℝ) (ha : 0 < a) (s : ℂ) (hs : 1 < s.re) :
    zetaRegularSeries a s = laguerreHurwitzZeta a s-riemannZeta s+
      ((a : ℂ)-1)*zetaPoleRemoved s := by
  have hs1 : 1 < (s+1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hh := ((laguerre_hurwitz_zeta_hasSum a ha s hs).sub
    (integer_zeta_multiplier_hasSum s hs)).add
      ((integer_zeta_multiplier_hasSum (s+1) hs1).mul_left (s*((a : ℂ)-1)))
  have he (n : ℕ) :
      1/((n : ℂ)+(a : ℂ))^s - integerZetaMultiplier s n +
        s*((a : ℂ)-1)*integerZetaMultiplier (s+1) n = zetaRegularTerm a n s := by
    simp only [zetaRegularTerm, integerZetaMultiplier, one_div, Complex.cpow_neg]
    rw [show -s-1 = -(s+1) by ring, Complex.cpow_neg]
  simp only [he] at hh
  have ht := (hasSum_nat_add_iff' 1).mpr hh
  rw [zetaRegularSeries, ht.tsum_eq, Finset.sum_range_one,
    zeta_pole_removed_eq s (by intro h; simp [h] at hs; linarith)]
  ring

private def lerchRegion : Set ℂ :=
  zetaRegularRegion ∩ {s : ℂ | -1 < s.im-s.re}

private theorem lerch_region_open : IsOpen lerchRegion :=
  zeta_regular_region_open.inter
    (isOpen_lt continuous_const (Complex.continuous_im.sub Complex.continuous_re))

private theorem lerch_region_convex : Convex ℝ lerchRegion := by
  have hW : Convex ℝ zetaRegularRegion := by
    exact (convex_halfSpace_re_gt (-(1/2 : ℝ))).inter
      (by simpa only [Metric.ball, dist_zero_right] using convex_ball (0 : ℂ) 4)
  exact hW.inter ((convex_Ioi (-1 : ℝ)).linear_preimage (Complex.imCLM-Complex.reCLM).toLinearMap)

private theorem lerch_region_zero : (0 : ℂ) ∈ lerchRegion := by
  norm_num [lerchRegion, zetaRegularRegion]

private theorem lerch_region_ne_one {s : ℂ} (hs : s ∈ lerchRegion) : s ≠ 1 := by
  intro h
  subst s
  norm_num [lerchRegion] at hs

theorem zeta_regular_series_continuation (a : ℝ) (ha : 0 < a) :
    zetaRegularSeries a =ᶠ[𝓝 (0 : ℂ)]
      (fun s : ℂ => laguerreHurwitzZeta a s-riemannZeta s+((a : ℂ)-1)*zetaPoleRemoved s) := by
  have hf : AnalyticOnNhd ℂ (zetaRegularSeries a) lerchRegion :=
    ((zeta_regular_series_differentiableOn a ha).mono inter_subset_left).analyticOnNhd lerch_region_open
  have hg : AnalyticOnNhd ℂ
      (fun s : ℂ => laguerreHurwitzZeta a s-riemannZeta s+((a : ℂ)-1)*zetaPoleRemoved s)
      lerchRegion := by
    apply DifferentiableOn.analyticOnNhd _ lerch_region_open
    intro z hz
    exact (((laguerre_hurwitz_zeta_differentiableAt a ha z (lerch_region_ne_one hz)).sub
      (differentiableAt_riemannZeta (lerch_region_ne_one hz))).add
      ((zeta_pole_removed_differentiable z).const_mul _)).differentiableWithinAt
  let p : ℂ := 2+2*Complex.I
  have hp : p ∈ lerchRegion := by
    refine ⟨⟨by norm_num [p], ?_⟩, by norm_num [p]⟩
    have hnorm : ‖p‖^2 = 8 := by
      rw [Complex.norm_eq_abs, Complex.sq_abs]
      norm_num [p, Complex.normSq_apply]
    nlinarith [norm_nonneg p]
  have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 p :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num [p])
  have he := hf.eqOn_of_preconnected_of_eventuallyEq hg lerch_region_convex.isPreconnected hp
    (by filter_upwards [hV] with z hz using zeta_regular_series_spectral a ha z hz)
  filter_upwards [lerch_region_open.mem_nhds lerch_region_zero] with s hs
  exact he hs

theorem hurwitz_deriv_zero_difference (a : ℝ) (ha : 0 < a) :
    deriv (laguerreHurwitzZeta a) 0 - deriv riemannZeta 0 +
      ((a : ℂ)-1)*deriv zetaPoleRemoved 0 =
      ((Real.log (Real.Gamma a)+Real.eulerMascheroniConstant*(a-1) : ℝ) : ℂ) := by
  have hd := (((laguerre_hurwitz_zeta_regular_zero a ha).hasDerivAt.sub
    (differentiableAt_riemannZeta zero_ne_one).hasDerivAt).add
      ((zeta_pole_removed_differentiable 0).hasDerivAt.const_mul ((a : ℂ)-1)))
  have he := (hd.congr_of_eventuallyEq (zeta_regular_series_continuation a ha)).deriv
  rw [zeta_regular_series_deriv_zero a ha] at he
  exact he.symm

theorem laguerre_hurwitz_zeta_two (s : ℂ) :
    laguerreHurwitzZeta 2 s = riemannZeta s-1 := by
  norm_num [laguerreHurwitzZeta, laguerreHurwitzBase, laguerreHurwitzShift,
    AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero]

theorem zeta_pole_removed_deriv_zero :
    deriv zetaPoleRemoved 0 = (Real.eulerMascheroniConstant : ℂ) := by
  have h := hurwitz_deriv_zero_difference 2 (by norm_num)
  have he : deriv (laguerreHurwitzZeta 2) 0 = deriv riemannZeta 0 := by
    rw [show laguerreHurwitzZeta 2 = (fun s => riemannZeta s-1) from funext laguerre_hurwitz_zeta_two,
      deriv_sub_const]
  rw [he] at h
  norm_num at h ⊢
  exact h

theorem laguerre_hurwitz_deriv_zero_relative (a : ℝ) (ha : 0 < a) :
    deriv (laguerreHurwitzZeta a) 0 =
      deriv riemannZeta 0 + (Real.log (Real.Gamma a) : ℂ) := by
  have h := hurwitz_deriv_zero_difference a ha
  rw [zeta_pole_removed_deriv_zero] at h
  push_cast at h
  linear_combination h

theorem riemann_zeta_deriv_zero :
    deriv riemannZeta 0 = (-(Real.log (2*Real.pi)/2 : ℝ) : ℂ) := by
  have h := laguerre_hurwitz_deriv_zero_relative (1/2) (by norm_num)
  rw [show laguerreHurwitzZeta (1/2) =
      HurwitzZeta.hurwitzZeta ((1/2 : ℝ) : UnitAddCircle) from funext laguerre_hurwitz_zeta_half,
    hurwitz_half_deriv_zero, Real.Gamma_one_half_eq, Real.log_sqrt Real.pi_pos.le] at h
  have hc : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hc] at h
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  push_cast at h ⊢
  linear_combination -h

/-- Lerch's formula for the actual all-positive-shift continuation. -/
theorem laguerre_hurwitz_deriv_zero (a : ℝ) (ha : 0 < a) :
    deriv (laguerreHurwitzZeta a) 0 =
      ((Real.log (Real.Gamma a) - Real.log (2*Real.pi)/2 : ℝ) : ℂ) := by
  rw [laguerre_hurwitz_deriv_zero_relative a ha, riemann_zeta_deriv_zero]
  push_cast
  ring

/-- Zeta regularization of the native shifted operator, with its absolute normalization. -/
theorem laguerre_zeta_determinant_gamma (a : ℝ) (ha : 0 < a) :
    laguerreZetaDeterminant a = ((Real.sqrt (2*Real.pi)/Real.Gamma a : ℝ) : ℂ) := by
  rw [laguerreZetaDeterminant, laguerre_hurwitz_deriv_zero a ha]
  have hG := Real.Gamma_pos_of_pos ha
  have hp : 0 < 2*Real.pi := by positivity
  have he : Real.exp (-(Real.log (Real.Gamma a)-Real.log (2*Real.pi)/2)) =
      Real.sqrt (2*Real.pi)/Real.Gamma a := by
    rw [show -(Real.log (Real.Gamma a)-Real.log (2*Real.pi)/2) =
      Real.log (2*Real.pi)/2-Real.log (Real.Gamma a) by ring,
      Real.exp_sub, Real.exp_log hG, Real.sqrt_eq_rpow,
      Real.rpow_def_of_pos hp]
    congr 2
    ring
  exact_mod_cast he

theorem laguerre_zeta_determinant_shift_one_value :
    laguerreZetaDeterminant 1 = (Real.sqrt (2*Real.pi) : ℂ) := by
  simpa using laguerre_zeta_determinant_gamma 1 (by norm_num)

theorem laguerre_prime_zeta_determinant_value :
    laguerrePrimeZetaDeterminant = (Real.sqrt (2*Real.pi) : ℂ) := by
  rw [laguerre_prime_zeta_determinant_eq_shift_one, laguerre_zeta_determinant_shift_one_value]

end
end Sigma

