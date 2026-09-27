import SigmaOpResolventHeat
import SigmaOpNonnegativeResolvent
import SigmaOpMixingStrong
import Mathlib.Analysis.Calculus.MeanValue

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology

theorem resolvent_heat_scalar_add {s t r : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hr : 0 ≤ r) :
    resolventHeatScalar (s+t) r = resolventHeatScalar s r * resolventHeatScalar t r := by
  rcases hr.eq_or_lt with h | h
  · rw [← h]; simp only [resolvent_heat_scalar_zero, mul_zero]
  · rw [resolvent_heat_scalar_eq (add_pos hs ht) h,
      resolvent_heat_scalar_eq hs h, resolvent_heat_scalar_eq ht h, ← Real.exp_add]
    congr 1
    ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem heat_clm_map_real_smul (T : H →L[ℂ] H) (c : ℝ) (x : H) :
    T (c • x) = c • T x := (T.restrictScalars ℝ).map_smul c x

theorem resolvent_heat_operator_zero (R : H →L[ℂ] H) :
    resolventHeatOperator R 0 = 1 := by simp [resolventHeatOperator]

theorem resolvent_heat_operator_add (R : H →L[ℂ] H)
    (_hR : IsSelfAdjoint R) (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    resolventHeatOperator R (s+t) =
      resolventHeatOperator R s * resolventHeatOperator R t := by
  rcases hs.eq_or_lt with h | hs
  · rw [← h, zero_add, resolvent_heat_operator_zero, one_mul]
  rcases ht.eq_or_lt with h | ht
  · rw [← h, add_zero, resolvent_heat_operator_zero, mul_one]
  simp only [resolventHeatOperator, if_pos hs, if_pos ht, if_pos (add_pos hs ht)]
  rw [← cfc_mul _ _ _ (resolvent_heat_scalar_continuous s).continuousOn
    (resolvent_heat_scalar_continuous t).continuousOn]
  apply cfc_congr
  intro r hr
  exact resolvent_heat_scalar_add hs ht (hσ hr).1

/-- On a dense resolvent range, the heat evolution converges uniformly after
multiplication by the compactifying spectral coordinate. -/
theorem resolvent_heat_scalar_scaled_bound {t r : ℝ} (ht : 0 < t)
    (hr : r ∈ Icc (0 : ℝ) 1) :
    |r * (resolventHeatScalar t r - 1)| ≤ t := by
  rw [abs_mul, abs_of_nonneg hr.1,
    abs_of_nonpos (sub_nonpos.mpr (resolvent_heat_scalar_le_one ht hr))]
  rcases hr.1.eq_or_lt with h | h
  · rw [← h, zero_mul]; exact ht.le
  have he := Real.add_one_le_exp (-t * (r⁻¹ - 1))
  rw [← resolvent_heat_scalar_eq ht h] at he
  have hi : r * r⁻¹ = 1 := mul_inv_cancel₀ h.ne'
  have hm := mul_le_mul_of_nonneg_left he hr.1
  nlinarith [mul_nonneg ht.le hr.1]

theorem resolvent_heat_resolvent_norm_bound (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 < t) :
    ‖resolventHeatOperator R t * R - R‖ ≤ t := by
  have he : resolventHeatOperator R t * R - R =
      cfc (fun r : ℝ => r * (resolventHeatScalar t r - 1)) R := by
    simp only [resolventHeatOperator, if_pos ht]
    calc
      cfc (resolventHeatScalar t) R * R - R =
          cfc (resolventHeatScalar t) R * cfc (fun r : ℝ => r) R -
            cfc (fun r : ℝ => r) R := by simp only [cfc_id' ℝ R hR]
      _ = cfc (fun r => resolventHeatScalar t r * r - r) R := by
        rw [cfc_sub (fun r => resolventHeatScalar t r * r) (fun r : ℝ => r) R
          ((resolvent_heat_scalar_continuous t).continuousOn.mul
          continuousOn_id) continuousOn_id,
          cfc_mul (resolventHeatScalar t) (fun r : ℝ => r) R
            (resolvent_heat_scalar_continuous t).continuousOn continuousOn_id]
      _ = _ := by apply cfc_congr; intro r _; ring
  rw [he]
  apply norm_cfc_le ht.le
  intro r hr
  simpa only [Real.norm_eq_abs] using resolvent_heat_scalar_scaled_bound ht (hσ hr)

theorem resolvent_heat_range_orbit_bound (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    (t : ℝ) (y : H) :
    ‖resolventHeatOperator R t (R y) - R y‖ ≤ |t| * ‖y‖ := by
  by_cases ht : 0 < t
  · change ‖(resolventHeatOperator R t * R - R) y‖ ≤ |t| * ‖y‖
    apply (ContinuousLinearMap.le_opNorm _ y).trans
    rw [abs_of_pos ht]
    exact mul_le_mul_of_nonneg_right (resolvent_heat_resolvent_norm_bound R hR hσ ht)
      (norm_nonneg _)
  · simp only [resolventHeatOperator, if_neg ht, ContinuousLinearMap.one_apply, sub_self,
      norm_zero]
    exact mul_nonneg (abs_nonneg _) (norm_nonneg _)

/-- Density of the actual resolvent range removes any spectral discreteness
assumption in strong continuity at time zero. -/
theorem resolvent_heat_orbit_tendsto_zero (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    (hdense : DenseRange R) (x : H) :
    Tendsto (fun t => resolventHeatOperator R t x) (𝓝 (0 : ℝ)) (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y, hy⟩ := Metric.mem_closure_range_iff.mp (hdense x) (ε/4) (by positivity)
  have hy' : ‖x - R y‖ < ε/4 := by simpa only [dist_eq_norm] using hy
  have hδ : 0 < ε / (2 * (‖y‖ + 1)) := by positivity
  filter_upwards [((continuous_abs.continuousAt : ContinuousAt abs (0 : ℝ)).tendsto
    |>.eventually (gt_mem_nhds (by simpa only [abs_zero] using hδ)))] with t ht
  rw [dist_eq_norm]
  have he : resolventHeatOperator R t x - x =
      resolventHeatOperator R t (x - R y) +
        (resolventHeatOperator R t (R y) - R y) + (R y - x) := by
    rw [map_sub]
    abel
  rw [he]
  apply (norm_add_le _ _).trans_lt
  apply lt_of_le_of_lt (add_le_add (norm_add_le _ _) le_rfl)
  have hb := resolvent_heat_range_orbit_bound R hR hσ t y
  have hc := resolvent_heat_operator_contracts R hσ t (x - R y)
  have hm : |t| * ‖y‖ < ε/2 := by
    have hmul := (lt_div_iff₀ (by positivity : 0 < 2 * (‖y‖+1))).mp ht
    nlinarith [abs_nonneg t, norm_nonneg y]
  rw [norm_sub_rev (R y) x]
  linarith

theorem resolvent_heat_orbit_modulus (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    (x : H) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖resolventHeatOperator R s x - resolventHeatOperator R t x‖ ≤
      ‖resolventHeatOperator R |s-t| x - x‖ := by
  rcases le_total s t with h | h
  · have he : resolventHeatOperator R t =
        resolventHeatOperator R s * resolventHeatOperator R (t-s) := by
      rw [← resolvent_heat_operator_add R hR hσ hs (sub_nonneg.mpr h), add_sub_cancel]
    rw [he, abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    change ‖resolventHeatOperator R s x -
      resolventHeatOperator R s (resolventHeatOperator R (t-s) x)‖ ≤ _
    rw [← map_sub, norm_sub_rev (resolventHeatOperator R (t-s) x) x]
    exact resolvent_heat_operator_contracts R hσ s _
  · have he : resolventHeatOperator R s =
        resolventHeatOperator R t * resolventHeatOperator R (s-t) := by
      rw [← resolvent_heat_operator_add R hR hσ ht (sub_nonneg.mpr h), add_sub_cancel]
    rw [he, abs_of_nonneg (sub_nonneg.mpr h)]
    change ‖resolventHeatOperator R t (resolventHeatOperator R (s-t) x) -
      resolventHeatOperator R t x‖ ≤ _
    rw [← map_sub]
    exact resolvent_heat_operator_contracts R hσ t _

theorem resolvent_heat_orbit_continuous (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    (hdense : DenseRange R) (x : H) :
    ContinuousOn (fun t => resolventHeatOperator R t x) (Ici 0) := by
  intro t ht
  have hz : Tendsto (fun u => ‖resolventHeatOperator R u x - x‖)
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((resolvent_heat_orbit_tendsto_zero R hR hσ hdense x).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => x) (𝓝 (0 : ℝ)) (𝓝 x))).norm
  have hd : Tendsto (fun s : ℝ => |s-t|) (𝓝[Ici 0] t) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ => |s-t|) :=
      (continuous_id.sub continuous_const).abs
    simpa only [sub_self, abs_zero] using
      (hc.continuousWithinAt (s := Ici (0 : ℝ)) (x := t)).tendsto
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Filter.mem_of_superset self_mem_nhdsWithin fun s hs =>
      resolvent_heat_orbit_modulus R hR hσ x hs ht) (hz.comp hd)

theorem exp_negative_remainder_bound {z : ℝ} (hz : 0 ≤ z) :
    |Real.exp (-z) - 1 + z| ≤ z ^ 2 := by
  by_cases hsmall : z ≤ 1
  · have h := Real.abs_exp_sub_one_sub_id_le (x := -z)
      (by simpa only [abs_neg, abs_of_nonneg hz] using hsmall)
    simpa only [sub_neg_eq_add, neg_sq] using h
  · have hl := Real.add_one_le_exp (-z)
    have hu := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz)
    rw [abs_of_nonneg (by linarith : 0 ≤ Real.exp (-z) - 1 + z)]
    nlinarith

theorem resolvent_heat_scalar_remainder_bound {t r : ℝ} (ht : 0 < t)
    (hr : r ∈ Icc (0 : ℝ) 1) :
    |r^2 * (resolventHeatScalar t r - 1) + t * r * (1-r)| ≤ t^2 := by
  rcases hr.1.eq_or_lt with h | h
  · rw [← h]; simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero, add_zero,
      abs_zero]; positivity
  have hz : 0 ≤ t * (r⁻¹ - 1) :=
    mul_nonneg ht.le (sub_nonneg.mpr ((one_le_inv₀ h).mpr hr.2))
  have hb := mul_le_mul_of_nonneg_left (exp_negative_remainder_bound hz) (sq_nonneg r)
  have he : r^2 * (resolventHeatScalar t r - 1) + t * r * (1-r) =
      r^2 * (Real.exp (-(t * (r⁻¹ - 1))) - 1 + t * (r⁻¹ - 1)) := by
    rw [resolvent_heat_scalar_eq ht h, neg_mul]
    field_simp
    ring
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg r)]
  apply hb.trans
  have hid : r^2 * (t * (r⁻¹ - 1))^2 = t^2 * (1-r)^2 := by field_simp; ring
  rw [hid]
  have hsq : (1-r)^2 ≤ 1 := by nlinarith [hr.1, hr.2]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq (sq_nonneg t)

theorem resolvent_heat_squared_resolvent_remainder (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 < t) :
    ‖resolventHeatOperator R t * R^2 - R^2 - t • ((R-1)*R)‖ ≤ t^2 := by
  have hc := (resolvent_heat_scalar_continuous t).continuousOn (s := spectrum ℝ R)
  have hi : ContinuousOn (fun r : ℝ => r) (spectrum ℝ R) := continuousOn_id
  have hp : ContinuousOn (fun r : ℝ => r^2) (spectrum ℝ R) := hi.pow 2
  have hd := hi.sub (continuousOn_const (c := (1 : ℝ)))
  have he : cfc (fun r : ℝ => (resolventHeatScalar t r * r^2 - r^2) -
      t * ((r-1)*r)) R =
      resolventHeatOperator R t * R^2 - R^2 - t • ((R-1)*R) := by
    rw [cfc_sub (fun r => resolventHeatScalar t r * r^2 - r^2)
      (fun r => t * ((r-1)*r)) R ((hc.mul hp).sub hp)
        (continuousOn_const.mul (hd.mul hi)),
      cfc_sub _ _ R (hc.mul hp) hp,
      cfc_mul (resolventHeatScalar t) (fun r : ℝ => r^2) R hc hp,
      cfc_const_mul t (fun r : ℝ => (r-1)*r) R (hd.mul hi),
      cfc_mul (fun r : ℝ => r-1) (fun r : ℝ => r) R hd hi,
      cfc_sub (fun r : ℝ => r) (fun _ : ℝ => 1) R hi continuousOn_const,
      cfc_pow (fun r : ℝ => r) 2 R hi hR, cfc_id' ℝ R hR, cfc_const_one ℝ R hR]
    simp only [resolventHeatOperator, if_pos ht]
  rw [← he]
  apply norm_cfc_le (sq_nonneg t)
  intro r hr
  have hb := resolvent_heat_scalar_remainder_bound ht (hσ hr)
  simpa only [Real.norm_eq_abs, show
    (resolventHeatScalar t r * r^2 - r^2) - t*((r-1)*r) =
      r^2 * (resolventHeatScalar t r - 1) + t*r*(1-r) by ring] using hb

def resolventHeatError (R : H →L[ℂ] H) (t : ℝ) (y : H) : H :=
  resolventHeatOperator R t (R y) - R y - t • (R y - y)

theorem resolvent_heat_error_bound (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    (hnR : ‖R‖ ≤ 1) {t : ℝ} (ht : 0 < t) (y : H) :
    t⁻¹ * ‖resolventHeatError R t y‖ ≤ 3 * ‖y‖ := by
  have hRy : ‖R y‖ ≤ ‖y‖ :=
    (R.le_opNorm y).trans (by nlinarith [norm_nonneg y])
  have hdiff : ‖R y - y‖ ≤ 2 * ‖y‖ :=
    (norm_sub_le _ _).trans (by linarith)
  have he : ‖resolventHeatError R t y‖ ≤ 3 * t * ‖y‖ := by
    unfold resolventHeatError
    apply (norm_sub_le _ _).trans
    rw [norm_smul, Real.norm_of_nonneg ht.le]
    have hr := resolvent_heat_range_orbit_bound R hR hσ t y
    rw [abs_of_pos ht] at hr
    nlinarith
  calc
    t⁻¹ * ‖resolventHeatError R t y‖ ≤ t⁻¹ * (3*t*‖y‖) :=
      mul_le_mul_of_nonneg_left he (inv_nonneg.mpr ht.le)
    _ = 3 * ‖y‖ := by field_simp; ring

theorem resolvent_heat_error_core_bound (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 < t) (z : H) :
    t⁻¹ * ‖resolventHeatError R t (R z)‖ ≤ t * ‖z‖ := by
  have he : resolventHeatError R t (R z) =
      ((resolventHeatOperator R t * R^2 - R^2 - t • ((R-1)*R)) : H →L[ℂ] H) z := by
    simp only [resolventHeatError, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.mul_apply, pow_two, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
  rw [he]
  have hb := (ContinuousLinearMap.le_opNorm
      (resolventHeatOperator R t * R^2 - R^2 - t • ((R-1)*R)) z).trans
    (mul_le_mul_of_nonneg_right (resolvent_heat_squared_resolvent_remainder R hR hσ ht)
      (norm_nonneg z))
  calc
    t⁻¹ * ‖((resolventHeatOperator R t * R^2 - R^2 - t • ((R-1)*R)) : H →L[ℂ] H) z‖ ≤
        t⁻¹ * (t^2 * ‖z‖) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr ht.le)
    _ = t * ‖z‖ := by field_simp; ring

/-- The native right generator action on the entire resolvent range, derived
by dense approximation from a uniformly differentiated core. -/
theorem resolvent_heat_range_generator_zero (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    (hnR : ‖R‖ ≤ 1) (hdense : DenseRange R) (y : H) :
    HasDerivWithinAt (fun t => resolventHeatOperator R t (R y)) (R y-y) (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto]
  simp only [sub_zero, resolvent_heat_operator_zero, ContinuousLinearMap.one_apply]
  change Tendsto (fun t : ℝ => ‖t‖⁻¹ * ‖resolventHeatError R t y‖)
    (𝓝[Ici 0] (0 : ℝ)) (𝓝 0)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨z,hz⟩ := Metric.mem_closure_range_iff.mp (hdense y) (ε/8) (by positivity)
  have hz' : ‖y-R z‖ < ε/8 := by simpa only [dist_eq_norm] using hz
  have hδ : 0 < ε / (2*(‖z‖+1)) := by positivity
  have hsmall : ∀ᶠ t : ℝ in 𝓝[Ici 0] (0 : ℝ), t < ε/(2*(‖z‖+1)) :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht hsmall
  rw [dist_zero_right, Real.norm_of_nonneg
    (mul_nonneg (inv_nonneg.mpr (norm_nonneg t)) (norm_nonneg _))]
  rcases ht.eq_or_lt with ht | ht
  · rw [← ht]
    simp only [norm_zero, inv_zero, zero_mul]
    exact hε
  · rw [Real.norm_of_nonneg ht.le]
    have he : resolventHeatError R t y =
        resolventHeatError R t (y-R z) + resolventHeatError R t (R z) := by
      simp only [resolventHeatError, map_sub, smul_sub]
      abel
    rw [he]
    have ha := resolvent_heat_error_bound R hR hσ hnR ht (y-R z)
    have hb := resolvent_heat_error_core_bound R hR hσ ht z
    have hmul : t * ‖z‖ < ε/2 := by
      have h := (lt_div_iff₀ (by positivity : 0 < 2*(‖z‖+1))).mp hsmall
      nlinarith [norm_nonneg z]
    have hn := mul_le_mul_of_nonneg_left
      (norm_add_le (resolventHeatError R t (y-R z)) (resolventHeatError R t (R z)))
      (inv_nonneg.mpr ht.le)
    linarith

theorem resolvent_heat_range_remainder_at (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    (y : H) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖resolventHeatOperator R t (R y) - resolventHeatOperator R s (R y) -
      (t-s) • resolventHeatOperator R s (R y-y)‖ ≤
    ‖resolventHeatError R |t-s| y‖ + |t-s| *
      ‖resolventHeatOperator R t (R y-y) - resolventHeatOperator R s (R y-y)‖ := by
  rcases le_total s t with h | h
  · have he : resolventHeatOperator R t =
        resolventHeatOperator R s * resolventHeatOperator R (t-s) := by
      rw [← resolvent_heat_operator_add R hR hσ hs (sub_nonneg.mpr h), add_sub_cancel]
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have he' : resolventHeatOperator R t (R y) - resolventHeatOperator R s (R y) -
        (t-s) • resolventHeatOperator R s (R y-y) =
        resolventHeatOperator R s (resolventHeatError R (t-s) y) := by
      rw [he]
      simp only [resolventHeatError, map_sub, heat_clm_map_real_smul,
        ContinuousLinearMap.mul_apply]
    rw [he']
    exact (resolvent_heat_operator_contracts R hσ s _).trans
      (le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr h) (norm_nonneg _)))
  · have he : resolventHeatOperator R s =
        resolventHeatOperator R t * resolventHeatOperator R (s-t) := by
      rw [← resolvent_heat_operator_add R hR hσ ht (sub_nonneg.mpr h), add_sub_cancel]
    rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    have he' : resolventHeatOperator R t (R y) - resolventHeatOperator R s (R y) -
        (t-s) • resolventHeatOperator R s (R y-y) =
        -(resolventHeatOperator R t (resolventHeatError R (s-t) y)) +
          (s-t) • (resolventHeatOperator R s (R y-y) -
            resolventHeatOperator R t (R y-y)) := by
      rw [he]
      simp only [resolventHeatError, map_sub, heat_clm_map_real_smul,
        ContinuousLinearMap.mul_apply, smul_sub]
      rw [show t-s = -(s-t) by ring, neg_smul]
      module
    rw [he']
    apply (norm_add_le _ _).trans
    rw [norm_neg, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr h),
      norm_sub_rev (resolventHeatOperator R s (R y-y))]
    exact add_le_add (resolvent_heat_operator_contracts R hσ t _) le_rfl

theorem resolvent_heat_range_generator (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    (hnR : ‖R‖ ≤ 1) (hdense : DenseRange R) (y : H) (s : ℝ) (hs : 0 ≤ s) :
    HasDerivWithinAt (fun t => resolventHeatOperator R t (R y))
      (resolventHeatOperator R s (R y-y)) (Ici 0) s := by
  have hz := (hasDerivWithinAt_iff_tendsto.mp
    (resolvent_heat_range_generator_zero R hR hσ hnR hdense y))
  simp only [sub_zero, resolvent_heat_operator_zero, ContinuousLinearMap.one_apply] at hz
  change Tendsto (fun t : ℝ => ‖t‖⁻¹ * ‖resolventHeatError R t y‖)
    (𝓝[Ici 0] (0 : ℝ)) (𝓝 0) at hz
  have hdist : Tendsto (fun t : ℝ => |t-s|) (𝓝[Ici 0] s) (𝓝[Ici 0] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Continuous (fun t : ℝ => |t-s|) :=
        (continuous_id.sub continuous_const).abs
      simpa only [sub_self, abs_zero] using (hc.continuousWithinAt (s := Ici 0) (x := s)).tendsto
    · exact Eventually.of_forall fun t => abs_nonneg (t-s)
  have hzero : Tendsto (fun t : ℝ =>
      |t-s|⁻¹ * ‖resolventHeatError R |t-s| y‖) (𝓝[Ici 0] s) (𝓝 0) := by
    simpa only [Function.comp_def, Real.norm_eq_abs, abs_abs] using hz.comp hdist
  have hcont := (resolvent_heat_orbit_continuous R hR hσ hdense (R y-y)) s hs
  have hd : Tendsto (fun t : ℝ => ‖resolventHeatOperator R t (R y-y) -
      resolventHeatOperator R s (R y-y)‖) (𝓝[Ici 0] s) (𝓝 0) := by
    have hconst : ContinuousWithinAt
        (fun _ : ℝ => resolventHeatOperator R s (R y-y)) (Ici 0) s :=
      continuousWithinAt_const
    simpa only [sub_self, norm_zero] using (hcont.sub hconst).tendsto.norm
  apply hasDerivWithinAt_iff_tendsto.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => mul_nonneg (inv_nonneg.mpr
    (norm_nonneg _)) (norm_nonneg _)) ?_ (by simpa only [zero_add] using hzero.add hd)
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Real.norm_eq_abs]
  have hb := mul_le_mul_of_nonneg_left
    (resolvent_heat_range_remainder_at R hR hσ y hs ht) (inv_nonneg.mpr (abs_nonneg (t-s)))
  apply hb.trans
  rw [mul_add]
  apply add_le_add_left
  have hn : |t-s|⁻¹ * |t-s| ≤ 1 := by
    by_cases he : t=s
    · simp only [he, sub_self, abs_zero, inv_zero, mul_zero]; exact zero_le_one
    · rw [inv_mul_cancel₀ (abs_ne_zero.mpr (sub_ne_zero.mpr he))]
  rw [← mul_assoc]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (norm_nonneg _)

/-- The constructed heat operators satisfy the generator equation on the
entire native domain, without assuming any semigroup properties as input. -/
theorem op_resolvent_heat_contraction_evolution (B : H →ₗ.[ℂ] H)
    (R : H →L[ℂ] H) (hres : OpIsResolvent B 1 R)
    (hR : IsSelfAdjoint R) (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    (hnR : ‖R‖ ≤ 1) (hdense : DenseRange R) :
    OpContractionEvolution B (resolventHeatOperator R) := by
  refine ⟨?_, fun s _ x => resolvent_heat_operator_contracts R hσ s x, ?_, ?_⟩
  · intro x
    rw [resolvent_heat_operator_zero, ContinuousLinearMap.one_apply]
  · exact resolvent_heat_orbit_continuous R hR hσ hdense
  · intro x s hs
    have hleft : R (B x + x.val) = x.val := by
      simpa only [one_smul] using hres.left_inverse x
    have hg := resolvent_heat_range_generator R hR hσ hnR hdense (B x+x.val) s hs
    rw [hleft] at hg
    simpa only [show x.val - (B x+x.val) = -B x by abel, map_neg] using hg

theorem resolvent_heat_operator_commutes (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (t : ℝ) : Commute (resolventHeatOperator R t) R := by
  unfold resolventHeatOperator
  split_ifs
  · have h := cfc_commute_cfc (resolventHeatScalar t) (fun r : ℝ => r) R
    rwa [cfc_id' ℝ R hR] at h
  · exact Commute.one_left R

/-- Strong right differentiability cannot add vectors beyond the actual
native domain: commuting the derivative with the shift inverse recovers the
domain membership and exact generator action. -/
theorem op_resolvent_heat_generator_domain (B : H →ₗ.[ℂ] H)
    (R : H →L[ℂ] H) (hres : OpIsResolvent B 1 R)
    (hR : IsSelfAdjoint R) (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    (hnR : ‖R‖ ≤ 1) (hdense : DenseRange R) (x v : H)
    (hv : HasDerivWithinAt (fun t => resolventHeatOperator R t x) v (Ici 0) 0) :
    ∃ hx : x ∈ B.domain, B ⟨x,hx⟩ = -v := by
  have hcomp := ((R.restrictScalars ℝ).hasFDerivAt).comp_hasDerivWithinAt 0 hv
  change HasDerivWithinAt (fun t => R (resolventHeatOperator R t x)) (R v) (Ici 0) 0 at hcomp
  have hcomm : (fun t => R (resolventHeatOperator R t x)) =
      fun t => resolventHeatOperator R t (R x) := by
    funext t
    exact (congrArg (fun T : H →L[ℂ] H => T x)
      (resolvent_heat_operator_commutes R hR t).eq).symm
  rw [hcomm] at hcomp
  have hgen := resolvent_heat_range_generator_zero R hR hσ hnR hdense x
  have he : R v = R x - x :=
    UniqueDiffWithinAt.eq_deriv (Ici 0) (uniqueDiffOn_Ici (0 : ℝ) 0 left_mem_Ici) hcomp hgen
  have hinv : R (x-v) = x := by rw [map_sub, he]; abel
  have hx : x ∈ B.domain := hinv ▸ hres.image_mem (x-v)
  refine ⟨hx, ?_⟩
  have ha := hres.right_inverse (x-v)
  simp only [one_smul] at ha
  have heq : (⟨R (x-v),hres.image_mem (x-v)⟩ : B.domain) = ⟨x,hx⟩ :=
    Subtype.ext hinv
  rw [heq, hinv] at ha
  exact (eq_sub_of_add_eq ha).trans (by abel)

theorem op_resolvent_heat_generator_domain_iff (B : H →ₗ.[ℂ] H)
    (R : H →L[ℂ] H) (hres : OpIsResolvent B 1 R)
    (hR : IsSelfAdjoint R) (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    (hnR : ‖R‖ ≤ 1) (hdense : DenseRange R) (x : H) :
    x ∈ B.domain ↔ ∃ v : H,
      HasDerivWithinAt (fun t => resolventHeatOperator R t x) v (Ici 0) 0 := by
  constructor
  · intro hx
    refine ⟨-B ⟨x,hx⟩, ?_⟩
    have h := (op_resolvent_heat_contraction_evolution B R hres hR hσ hnR hdense).generator_derivative
      ⟨x,hx⟩ 0 (le_refl 0)
    simpa only [resolvent_heat_operator_zero, ContinuousLinearMap.one_apply] using h
  · rintro ⟨v,hv⟩
    exact (op_resolvent_heat_generator_domain B R hres hR hσ hnR hdense x v hv).choose

end
end Sigma
