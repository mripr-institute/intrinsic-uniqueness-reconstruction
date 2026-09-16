import SigmaCore
import SigmaFenchel
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Topology.Order.IntermediateValue

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology

/-- These are the candidate's actual second and third derivatives. -/
abbrev scCurvature (F : ℝ → ℝ) : ℝ → ℝ := deriv (deriv F)
abbrev scThirdDerivative (F : ℝ → ℝ) : ℝ → ℝ := deriv (scCurvature F)

theorem sc_rpow_three_halves {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = Real.sqrt x ^ (3 : ℕ) := by
  rw [Real.rpow_div_two_eq_sqrt (3 : ℝ) hx]
  exact Real.rpow_natCast _ 3

theorem sc_inverse_sqrt_hasDerivAt {q : ℝ → ℝ} {q' t : ℝ}
    (hq : HasDerivAt q q' t) (hp : 0 < q t) :
    HasDerivAt (fun x => 1 / Real.sqrt (q x))
      (-q' / (2 * Real.sqrt (q t) ^ (3 : ℕ))) t := by
  have hs : Real.sqrt (q t) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have hd := (hasDerivAt_const t (1 : ℝ)).div (hq.sqrt (ne_of_gt hp)) hs
  convert hd using 1
  simp only [zero_mul, one_mul, zero_sub]
  field_simp only [hs]
  <;> ring

/-- The inverse square is derived from the signed equation, not supplied. -/
theorem sc_signed_curvature_unique (q : ℝ → ℝ)
    (hd : ∀ t > 0, DifferentiableAt ℝ q t)
    (hp : ∀ t > 0, 0 < q t) (h1 : q 1 = 1)
    (he : ∀ t > 0, deriv q t = -2 * (q t) ^ (3 / 2 : ℝ)) :
    ∀ t > 0, q t = 1 / t ^ (2 : ℕ) := by
  have hw : ∀ t > 0, HasDerivAt (fun x => 1 / Real.sqrt (q x)) 1 t := by
    intro t ht
    have hh := sc_inverse_sqrt_hasDerivAt (hd t ht).hasDerivAt (hp t ht)
    have hs : Real.sqrt (q t) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hp t ht))
    rw [he t ht, sc_rpow_three_halves (hp t ht).le] at hh
    convert hh using 1
    field_simp
  have hident : ∀ t > 0, 1 / Real.sqrt (q t) = t := by
    apply equal_of_equal_derivatives _ (fun t : ℝ => t)
      (fun t ht => (hw t ht).differentiableAt)
      (fun t _ => (hasDerivAt_id t).differentiableAt)
    · intro t ht
      simpa only [id_eq] using (hw t ht).deriv.trans (hasDerivAt_id t).deriv.symm
    · norm_num [h1]
  intro t ht
  have hs : Real.sqrt (q t) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hp t ht))
  have hh := (div_eq_iff hs).mp (hident t ht)
  have hr : Real.sqrt (q t) = 1 / t := by
    apply (eq_div_iff (ne_of_gt ht)).mpr
    nlinarith
  rw [← Real.sq_sqrt (hp t ht).le, hr, div_pow, one_pow]

/-- The positive-sign third-derivative branch cannot persist on the entire
positive ray: its positive inverse square root would equal 2-t. -/
theorem sc_positive_branch_impossible (q : ℝ → ℝ)
    (hd : ∀ t > 0, DifferentiableAt ℝ q t)
    (hp : ∀ t > 0, 0 < q t) (h1 : q 1 = 1)
    (he : ∀ t > 0, deriv q t = 2 * (q t) ^ (3 / 2 : ℝ)) : False := by
  have hw : ∀ t > 0, HasDerivAt (fun x => 1 / Real.sqrt (q x)) (-1) t := by
    intro t ht
    have hh := sc_inverse_sqrt_hasDerivAt (hd t ht).hasDerivAt (hp t ht)
    have hs : Real.sqrt (q t) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hp t ht))
    rw [he t ht, sc_rpow_three_halves (hp t ht).le] at hh
    convert hh using 1
    field_simp
  have hident : ∀ t > 0, 1 / Real.sqrt (q t) = 2 - t := by
    apply equal_of_equal_derivatives _ (fun t : ℝ => 2 - t)
      (fun t ht => (hw t ht).differentiableAt)
      (fun t _ => ((hasDerivAt_id t).const_sub 2).differentiableAt)
    · intro t ht
      simpa only [id_eq] using (hw t ht).deriv.trans ((hasDerivAt_id t).const_sub 2).deriv.symm
    · norm_num [h1]
  have hh := hident 3 (by norm_num)
  have hp3 : 0 < 1 / Real.sqrt (q 3) := one_div_pos.mpr
    (Real.sqrt_pos.2 (hp 3 (by norm_num)))
  linarith

theorem sc_continuous_nonzero_constant_sign (f : ℝ → ℝ)
    (hc : ContinuousOn f (Ioi 0)) (hne : ∀ t > 0, f t ≠ 0) :
    (∀ t > 0, f t < 0) ∨ (∀ t > 0, 0 < f t) := by
  by_cases h1 : f 1 < 0
  · left
    intro t ht
    by_contra hh
    have hpos : 0 < f t := lt_of_le_of_ne (le_of_not_gt hh) (hne t ht).symm
    have hz := isPreconnected_Ioi.intermediate_value
      (show (1 : ℝ) ∈ Ioi 0 by norm_num) ht hc
      (show (0 : ℝ) ∈ Icc (f 1) (f t) from ⟨h1.le, hpos.le⟩)
    obtain ⟨u, hu, he⟩ := hz
    exact hne u hu he
  · right
    have hp1 : 0 < f 1 := lt_of_le_of_ne (le_of_not_gt h1) (hne 1 (by norm_num)).symm
    intro t ht
    by_contra hh
    have hneg : f t < 0 := lt_of_le_of_ne (le_of_not_gt hh) (hne t ht)
    have hz := isPreconnected_Ioi.intermediate_value ht
      (show (1 : ℝ) ∈ Ioi 0 by norm_num) hc
      (show (0 : ℝ) ∈ Icc (f t) (f 1) from ⟨hneg.le, hp1.le⟩)
    obtain ⟨u, hu, he⟩ := hz
    exact hne u hu he

/-- Darboux's theorem removes any continuity assumption on the third derivative. -/
theorem sc_derivative_nonzero_constant_sign (q : ℝ → ℝ)
    (hd : ∀ t > 0, DifferentiableAt ℝ q t)
    (hne : ∀ t > 0, deriv q t ≠ 0) :
    (∀ t > 0, deriv q t < 0) ∨ (∀ t > 0, 0 < deriv q t) := by
  have hc : OrdConnected (deriv q '' Ioi 0) :=
    isPreconnected_Ioi.ordConnected.image_deriv hd
  have hm1 : deriv q 1 ∈ deriv q '' Ioi 0 := ⟨1, by norm_num, rfl⟩
  by_cases h1 : deriv q 1 < 0
  · left
    intro t ht
    by_contra hh
    have hpos : 0 < deriv q t := lt_of_le_of_ne (le_of_not_gt hh) (hne t ht).symm
    have hz : 0 ∈ deriv q '' Ioi 0 :=
      hc.out hm1 ⟨t, ht, rfl⟩ ⟨h1.le, hpos.le⟩
    obtain ⟨u, hu, he⟩ := hz
    exact hne u hu he
  · right
    have hp1 : 0 < deriv q 1 := lt_of_le_of_ne (le_of_not_gt h1)
      (hne 1 (by norm_num)).symm
    intro t ht
    by_contra hh
    have hneg : deriv q t < 0 := lt_of_le_of_ne (le_of_not_gt hh) (hne t ht)
    have hz : 0 ∈ deriv q '' Ioi 0 :=
      hc.out ⟨t, ht, rfl⟩ hm1 ⟨hneg.le, hp1.le⟩
    obtain ⟨u, hu, he⟩ := hz
    exact hne u hu he

theorem sc_unsigned_curvature_unique (q : ℝ → ℝ)
    (hd : ∀ t > 0, DifferentiableAt ℝ q t)
    (hp : ∀ t > 0, 0 < q t) (h1 : q 1 = 1)
    (he : ∀ t > 0, |deriv q t| = 2 * (q t) ^ (3 / 2 : ℝ)) :
    ∀ t > 0, q t = 1 / t ^ (2 : ℕ) := by
  have hne : ∀ t > 0, deriv q t ≠ 0 := by
    intro t ht hz
    have hh := he t ht
    rw [hz, abs_zero] at hh
    have hpw := Real.rpow_pos_of_pos (hp t ht) (3 / 2 : ℝ)
    linarith
  rcases sc_derivative_nonzero_constant_sign q hd hne with hn | hp'
  · apply sc_signed_curvature_unique q hd hp h1
    intro t ht
    have hh := he t ht
    rw [abs_of_neg (hn t ht)] at hh
    linarith
  · exfalso
    apply sc_positive_branch_impossible q hd hp h1
    intro t ht
    simpa only [abs_of_pos (hp' t ht)] using he t ht

/-- Positive inverse-square curvature and affine anchors recover the intrinsic deficit. -/
theorem sc_anchored_curvature_reconstructs (F : ℝ → ℝ)
    (hF : ∀ t > 0, DifferentiableAt ℝ F t)
    (hF' : ∀ t > 0, DifferentiableAt ℝ (deriv F) t)
    (hc : ∀ t > 0, scCurvature F t = 1 / t ^ (2 : ℕ))
    (hv : F 1 = 0) (hs : deriv F 1 = 0) : ∀ t > 0, F t = I t := by
  have hq : ∀ t > 0, HasDerivAt (fun x : ℝ => 1 - 1 / x) (1 / t ^ (2 : ℕ)) t := by
    intro t ht
    convert (reciprocal_hasDerivAt ht).neg using 1
    · funext x
      ring
    · ring
  have hder : ∀ t > 0, deriv F t = 1 - 1 / t := by
    apply equal_of_equal_derivatives (deriv F) _ hF'
      (fun t ht => (hq t ht).differentiableAt)
    · intro t ht
      rw [(hq t ht).deriv]
      exact hc t ht
    · simpa using hs
  exact SigmaPresentations.reconstruct_derivative F
    (fun t ht => (hF t ht).differentiableWithinAt) hv hder

/-- Continuity of the highest derivative is unnecessary for the signed inverse. -/
theorem self_concordance_signed_identifies_minimal (F : ℝ → ℝ)
    (hF : ∀ t > 0, DifferentiableAt ℝ F t)
    (hF' : ∀ t > 0, DifferentiableAt ℝ (deriv F) t)
    (hF'' : ∀ t > 0, DifferentiableAt ℝ (scCurvature F) t)
    (hp : ∀ t > 0, 0 < scCurvature F t)
    (hv : F 1 = 0) (hs : deriv F 1 = 0) (hc : scCurvature F 1 = 1)
    (he : ∀ t > 0, scThirdDerivative F t = -2 * (scCurvature F t) ^ (3 / 2 : ℝ)) :
    ∀ t > 0, F t = I t :=
  sc_anchored_curvature_reconstructs F hF hF'
    (sc_signed_curvature_unique (scCurvature F) hF'' hp hc he) hv hs

/-- The unsigned inverse also needs only three actual differentiability levels. -/
theorem self_concordance_unsigned_identifies_minimal (F : ℝ → ℝ)
    (hF : ∀ t > 0, DifferentiableAt ℝ F t)
    (hF' : ∀ t > 0, DifferentiableAt ℝ (deriv F) t)
    (hF'' : ∀ t > 0, DifferentiableAt ℝ (scCurvature F) t)
    (hp : ∀ t > 0, 0 < scCurvature F t)
    (hv : F 1 = 0) (hs : deriv F 1 = 0) (hc : scCurvature F 1 = 1)
    (he : ∀ t > 0, |scThirdDerivative F t| = 2 * (scCurvature F t) ^ (3 / 2 : ℝ)) :
    ∀ t > 0, F t = I t :=
  sc_anchored_curvature_reconstructs F hF hF'
    (sc_unsigned_curvature_unique (scCurvature F) hF'' hp hc he) hv hs

theorem self_concordance_signed_identifies (F : ℝ → ℝ)
    (hF : ContDiffOn ℝ 3 F (Ioi 0))
    (hp : ∀ t > 0, 0 < scCurvature F t)
    (hv : F 1 = 0) (hs : deriv F 1 = 0) (hc : scCurvature F 1 = 1)
    (he : ∀ t > 0, scThirdDerivative F t = -2 * (scCurvature F t) ^ (3 / 2 : ℝ)) :
    ∀ t > 0, F t = I t := by
  have hD1 : ContDiffOn ℝ 2 (deriv F) (Ioi 0) := hF.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hD2 : ContDiffOn ℝ 1 (scCurvature F) (Ioi 0) := hD1.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have h1 : ∀ t > 0, DifferentiableAt ℝ F t := fun t ht =>
    (hF.differentiableOn (by norm_num) t ht).differentiableAt (isOpen_Ioi.mem_nhds ht)
  have h2 : ∀ t > 0, DifferentiableAt ℝ (deriv F) t := fun t ht =>
    (hD1.differentiableOn (by norm_num) t ht).differentiableAt (isOpen_Ioi.mem_nhds ht)
  have h3 : ∀ t > 0, DifferentiableAt ℝ (scCurvature F) t := fun t ht =>
    (hD2.differentiableOn (by norm_num) t ht).differentiableAt (isOpen_Ioi.mem_nhds ht)
  exact sc_anchored_curvature_reconstructs F h1 h2
    (sc_signed_curvature_unique (scCurvature F) h3 hp hc he) hv hs

theorem self_concordance_unsigned_identifies (F : ℝ → ℝ)
    (hF : ContDiffOn ℝ 3 F (Ioi 0))
    (hp : ∀ t > 0, 0 < scCurvature F t)
    (hv : F 1 = 0) (hs : deriv F 1 = 0) (hc : scCurvature F 1 = 1)
    (he : ∀ t > 0, |scThirdDerivative F t| = 2 * (scCurvature F t) ^ (3 / 2 : ℝ)) :
    ∀ t > 0, F t = I t := by
  have hD1 : ContDiffOn ℝ 2 (deriv F) (Ioi 0) := hF.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hD2 : ContDiffOn ℝ 1 (scCurvature F) (Ioi 0) := hD1.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have h1 : ∀ t > 0, DifferentiableAt ℝ F t := fun t ht =>
    (hF.differentiableOn (by norm_num) t ht).differentiableAt (isOpen_Ioi.mem_nhds ht)
  have h2 : ∀ t > 0, DifferentiableAt ℝ (deriv F) t := fun t ht =>
    (hD1.differentiableOn (by norm_num) t ht).differentiableAt (isOpen_Ioi.mem_nhds ht)
  have h3 : ∀ t > 0, DifferentiableAt ℝ (scCurvature F) t := fun t ht =>
    (hD2.differentiableOn (by norm_num) t ht).differentiableAt (isOpen_Ioi.mem_nhds ht)
  exact sc_anchored_curvature_reconstructs F h1 h2
    (sc_unsigned_curvature_unique (scCurvature F) h3 hp hc he) hv hs

end
end Sigma
