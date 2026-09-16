import SigmaCore
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology

/-- The manuscript's real cross-ratio convention. -/
def projectiveCrossRatio (x₁ x₂ x₃ x₄ : ℝ) : ℝ :=
  (x₁ - x₃) * (x₂ - x₄) / ((x₁ - x₄) * (x₂ - x₃))

def PreservesPositiveCrossRatios (f : ℝ → ℝ) : Prop :=
  ∀ x₁ > 0, ∀ x₂ > 0, ∀ x₃ > 0, ∀ x₄ > 0,
    x₁ ≠ x₂ → x₁ ≠ x₃ → x₁ ≠ x₄ → x₂ ≠ x₃ → x₂ ≠ x₄ → x₃ ≠ x₄ →
    projectiveCrossRatio (f x₁) (f x₂) (f x₃) (f x₄) =
      projectiveCrossRatio x₁ x₂ x₃ x₄

/-- Only the cross-ratio slice through the three marked coordinates is needed. -/
theorem projective_three_point_slice_identifies (f : ℝ → ℝ)
    (hi : InjOn f (Ioi 0))
    (h1 : f 1 = 0) (h2 : f 2 = -1 / 2) (h3 : f 3 = -2 / 3)
    (hc : ∀ t > 0, t ≠ 1 → t ≠ 2 → t ≠ 3 →
      projectiveCrossRatio (f 1) (f 2) (f 3) (f t) = projectiveCrossRatio 1 2 3 t) :
    ∀ t > 0, f t = 1 / t - 1 := by
  intro t ht
  by_cases ht1 : t = 1
  · subst t
    norm_num [h1]
  by_cases ht2 : t = 2
  · subst t
    norm_num [h2]
  by_cases ht3 : t = 3
  · subst t
    norm_num [h3]
  have hft : f t ≠ 0 := by
    intro hz
    have he : f t = f 1 := by rw [hz, h1]
    exact ht1 (hi ht (by norm_num) he)
  have hnt : 1 - t ≠ 0 := by exact sub_ne_zero.mpr (Ne.symm ht1)
  have he := hc t ht ht1 ht2 ht3
  rw [h1, h2, h3] at he
  unfold projectiveCrossRatio at he
  field_simp at he
  apply (eq_sub_iff_add_eq).mpr
  apply (eq_div_iff (ne_of_gt ht)).mpr
  nlinarith

theorem calibrated_cross_ratio_identifies (f : ℝ → ℝ)
    (hi : InjOn f (Ioi 0)) (hc : PreservesPositiveCrossRatios f)
    (h1 : f 1 = 0) (h2 : f 2 = -1 / 2) (h3 : f 3 = -2 / 3) :
    ∀ t > 0, f t = 1 / t - 1 := by
  apply projective_three_point_slice_identifies f hi h1 h2 h3
  intro t ht ht1 ht2 ht3
  exact hc 1 (by norm_num) 2 (by norm_num) 3 (by norm_num) t ht
    (by norm_num) (by norm_num) ht1.symm (by norm_num) ht2.symm ht3.symm

/-- The Schwarzian is formed from the candidate's actual first three derivatives. -/
def projectiveSchwarzian (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv (deriv f)) t / deriv f t -
    (3 / 2 : ℝ) * (deriv (deriv f) t / deriv f t) ^ (2 : ℕ)

def projectiveAux (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (deriv f t) - t + 1

/-- Real.log uses the absolute-value extension; the auxiliary is precisely
one half of minus log|f'|, so no logarithm-domain assumption is suppressed. -/
theorem projectiveAux_eq_log_abs (f : ℝ → ℝ) (t : ℝ) :
    projectiveAux f t = -(1 / 2 : ℝ) * Real.log |deriv f t| - t + 1 := by
  simp only [projectiveAux, Real.log_abs]

def projectiveAuxSlope (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * (deriv (deriv f) t / deriv f t) - 1

theorem projectiveAux_hasDerivAt (f : ℝ → ℝ) {t : ℝ}
    (hd : DifferentiableAt ℝ (deriv f) t) (hn : deriv f t ≠ 0) :
    HasDerivAt (projectiveAux f) (projectiveAuxSlope f t) t := by
  convert (((hd.hasDerivAt.log hn).const_mul (-(1 / 2 : ℝ))).sub
    (hasDerivAt_id t)).add_const 1 using 1

theorem projectiveAuxSlope_hasDerivAt (f : ℝ → ℝ) {t : ℝ}
    (hd : DifferentiableAt ℝ (deriv f) t)
    (hdd : DifferentiableAt ℝ (deriv (deriv f)) t)
    (hn : deriv f t ≠ 0) (hz : projectiveSchwarzian f t = 0) :
    HasDerivAt (projectiveAuxSlope f) (-(projectiveAuxSlope f t + 1) ^ (2 : ℕ)) t := by
  have hq := hdd.hasDerivAt.div hd.hasDerivAt hn
  have hh := (hq.const_mul (-(1 / 2 : ℝ))).sub_const 1
  convert hh using 1
  unfold projectiveAuxSlope
  unfold projectiveSchwarzian at hz
  field_simp at hz ⊢
  have hfactor : deriv f t *
      (2 * deriv (deriv (deriv f)) t * deriv f t - 3 * deriv (deriv f) t ^ 2) = 0 := by
    nlinarith
  have hred := (mul_eq_zero.mp hfactor).resolve_left hn
  linear_combination (2 * deriv f t ^ 2) * hred

/-- The auxiliary potential is a genuine twice-differentiable Riccati candidate. -/
theorem projectiveAux_second_hasDerivAt (f : ℝ → ℝ)
    (hd : ∀ t > 0, DifferentiableAt ℝ (deriv f) t)
    (hdd : ∀ t > 0, DifferentiableAt ℝ (deriv (deriv f)) t)
    (hn : ∀ t > 0, deriv f t ≠ 0)
    (hz : ∀ t > 0, projectiveSchwarzian f t = 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deriv (projectiveAux f))
      (-(deriv (projectiveAux f) t + 1) ^ (2 : ℕ)) t := by
  have he : deriv (projectiveAux f) t = projectiveAuxSlope f t :=
    (projectiveAux_hasDerivAt f (hd t ht) (hn t ht)).deriv
  rw [he]
  apply (projectiveAuxSlope_hasDerivAt f (hd t ht) (hdd t ht) (hn t ht) (hz t ht)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
  exact (projectiveAux_hasDerivAt f (hd x hx) (hn x hx)).deriv

theorem calibrated_schwarzian_identifies_minimal (f : ℝ → ℝ)
    (hf : ∀ t > 0, DifferentiableAt ℝ f t)
    (hd : ∀ t > 0, DifferentiableAt ℝ (deriv f) t)
    (hdd : ∀ t > 0, DifferentiableAt ℝ (deriv (deriv f)) t)
    (hn : ∀ t > 0, deriv f t ≠ 0)
    (hz : ∀ t > 0, projectiveSchwarzian f t = 0)
    (hv : f 1 = 0) (h1 : deriv f 1 = -1) (h2 : deriv (deriv f) 1 = 2) :
    ∀ t > 0, f t = 1 / t - 1 := by
  have hA : ∀ t > 0, projectiveAux f t = H t := by
    apply riccati_reconstruction (projectiveAux f)
      (fun t ht => (projectiveAux_hasDerivAt f (hd t ht) (hn t ht)).differentiableAt)
      (fun t ht => projectiveAux_second_hasDerivAt f hd hdd hn hz ht)
    · norm_num [projectiveAux, h1, Real.log_neg_eq_log]
    · rw [(projectiveAux_hasDerivAt f (hd 1 (by norm_num)) (hn 1 (by norm_num))).deriv]
      norm_num [projectiveAuxSlope, h1, h2]
  have hw : ∀ t > 0, deriv (deriv f) t / deriv f t = -2 / t := by
    intro t ht
    have he : deriv (projectiveAux f) t = deriv H t := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
      exact hA x hx
    rw [(projectiveAux_hasDerivAt f (hd t ht) (hn t ht)).deriv, H_deriv ht] at he
    unfold projectiveAuxSlope at he
    linear_combination -2 * he
  have hprod : ∀ t > 0, HasDerivAt (fun t : ℝ => t ^ (2 : ℕ) * deriv f t) 0 t := by
    intro t ht
    have he := (div_eq_iff (hn t ht)).mp (hw t ht)
    have hh := ((hasDerivAt_id t).pow 2).mul (hd t ht).hasDerivAt
    convert hh using 1
    field_simp at he ⊢
    nlinarith
  have hconst : ∀ t > 0, t ^ (2 : ℕ) * deriv f t = -1 := by
    apply equal_of_equal_derivatives _ (fun _ : ℝ => -1)
      (fun t ht => (hprod t ht).differentiableAt)
      (fun t _ => (hasDerivAt_const t (-1 : ℝ)).differentiableAt)
    · intro t ht
      rw [(hprod t ht).deriv]
      simp
    · simpa using h1
  have hder : ∀ t > 0, deriv f t = -(1 / t ^ (2 : ℕ)) := by
    intro t ht
    have he := hconst t ht
    apply (eq_neg_iff_add_eq_zero).mpr
    apply (mul_right_cancel₀ (pow_ne_zero 2 (ne_of_gt ht)))
    field_simp
    nlinarith
  apply equal_of_equal_derivatives f (fun t : ℝ => 1 / t - 1) hf
    (fun t ht => (reciprocal_hasDerivAt ht).differentiableAt)
  · intro t ht
    rw [hder t ht, (reciprocal_hasDerivAt ht).deriv]
  · simpa using hv

theorem calibrated_schwarzian_identifies (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 3 f (Ioi 0))
    (hn : ∀ t > 0, deriv f t ≠ 0)
    (hz : ∀ t > 0, projectiveSchwarzian f t = 0)
    (hv : f 1 = 0) (h1 : deriv f 1 = -1) (h2 : deriv (deriv f) 1 = 2) :
    ∀ t > 0, f t = 1 / t - 1 := by
  have hD1 : ContDiffOn ℝ 2 (deriv f) (Ioi 0) := hf.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hD2 : ContDiffOn ℝ 1 (deriv (deriv f)) (Ioi 0) := hD1.deriv_of_isOpen isOpen_Ioi (by norm_num)
  exact calibrated_schwarzian_identifies_minimal f
    (fun t ht => (hf.differentiableOn (by norm_num) t ht).differentiableAt (isOpen_Ioi.mem_nhds ht))
    (fun t ht => (hD1.differentiableOn (by norm_num) t ht).differentiableAt (isOpen_Ioi.mem_nhds ht))
    (fun t ht => (hD2.differentiableOn (by norm_num) t ht).differentiableAt (isOpen_Ioi.mem_nhds ht))
    hn hz hv h1 h2

theorem projective_anchored_primitive_identifies (F f : ℝ → ℝ)
    (hd : ∀ t > 0, HasDerivAt F (f t) t) (hv : F 1 = 0)
    (hf : ∀ t > 0, f t = 1 / t - 1) : ∀ t > 0, F t = H t := by
  apply reconstruct_H F _ hv
  intro t ht
  simpa only [hf t ht] using hd t ht

end
end Sigma
