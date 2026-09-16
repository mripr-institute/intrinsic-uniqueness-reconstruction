import SigmaPresentations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology

abbrev H := SigmaPresentations.H
abbrev I := SigmaBase.potential
abbrev p := SigmaPresentations.density
abbrev star := SigmaBase.star

theorem H_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt H (1 / t - 1) t := by
  convert (SigmaBase.potential_hasDerivAt ht).neg using 1
  · funext x; simp [H, SigmaPresentations.H, SigmaBase.potential]; ring
  · ring

theorem H_deriv {t : ℝ} (ht : 0 < t) : deriv H t = 1 / t - 1 :=
  (H_hasDerivAt ht).deriv

theorem reconstruct_H (F : ℝ → ℝ)
    (hd : ∀ t > 0, HasDerivAt F (1 / t - 1) t) (h1 : F 1 = 0) :
    ∀ t > 0, F t = H t := by
  have he := SigmaBase.reconstruct_from_derivative (fun t => -F t)
    (fun t ht => (hd t ht).neg.differentiableAt.differentiableWithinAt)
    (by simp [h1]) (by intro t ht; convert (hd t ht).neg.deriv using 1; ring)
  intro t ht
  have h := he t ht
  change - F t = SigmaBase.potential t at h
  change F t = SigmaPresentations.H t
  rw [SigmaPresentations.H_eq_neg_potential]
  linarith

/-- The group equation transports a derivative assumed only at the identity. -/
theorem group_log_derivative_from_identity (L : ℝ → ℝ)
    (h0 : HasDerivAt L 1 0)
    (hh : ∀ x > -1, ∀ y > -1, L (star x y) = L x + L y)
    (x : ℝ) (hx : -1 < x) : HasDerivAt L (1 / (1 + x)) x := by
  have hp : 0 < 1 + x := by linarith
  have hne : 1 + x ≠ 0 := ne_of_gt hp
  have ha : HasDerivAt (fun s : ℝ => (s - x) / (1 + x)) (1 / (1 + x)) x := by
    simpa using ((hasDerivAt_id x).sub_const x).div_const (1 + x)
  have hc : HasDerivAt (fun s : ℝ => L x + L ((s - x) / (1 + x)))
      (1 / (1 + x)) x := by
    have hb : HasDerivAt L 1 ((x - x) / (1 + x)) := by simpa using h0
    simpa using (hb.comp x ha).const_add (L x)
  apply hc.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with s hs
  change -1 < s at hs
  have hy : -1 < (s - x) / (1 + x) := by
    apply (lt_div_iff₀ hp).mpr
    linarith
  have he : star x ((s - x) / (1 + x)) = s := by
    unfold star SigmaBase.star
    field_simp
    ring
  simpa only [he] using hh x hx ((s - x) / (1 + x)) hy

theorem normalized_group_log_unique_at_identity (L : ℝ → ℝ)
    (h0 : HasDerivAt L 1 0)
    (hh : ∀ x > -1, ∀ y > -1, L (star x y) = L x + L y) :
    ∀ x > -1, L x = Real.log (1 + x) := by
  exact SigmaPresentations.normalized_group_log_unique L
    (fun x hx => (group_log_derivative_from_identity L h0 hh x hx).differentiableAt.differentiableWithinAt)
    h0 hh

theorem normalized_cocycle_unique_at_identity (h : ℝ → ℝ)
    (h0 : HasDerivAt h 0 0)
    (hc : ∀ x > -1, ∀ y > -1, h (star x y) = h x + h y - x*y) :
    ∀ x > -1, h x = Real.log (1 + x) - x := by
  have hn : HasDerivAt (fun x => h x + x) 1 0 := by
    simpa using h0.add (hasDerivAt_id (0 : ℝ))
  have hm : ∀ x > -1, ∀ y > -1,
      (h (star x y) + star x y) = (h x + x) + (h y + y) := by
    intro x hx y hy
    rw [hc x hx y hy]
    unfold star SigmaBase.star
    ring
  have he := normalized_group_log_unique_at_identity (fun x => h x + x) hn hm
  intro x hx
  have he' := he x hx
  dsimp at he'
  linarith

theorem exact_flow_identifies (q : ℝ → ℝ) (h1 : q 1 = 1)
    (hf : ∀ t > 0, ∀ s : ℝ, 0 < t + s → q (t+s) = q t / (1+s*q t)) :
    ∀ t > 0, q t = 1/t := by
  intro t ht
  have h := hf 1 (by norm_num) (t-1) (by linarith)
  simpa [h1] using h

theorem exact_flow_of_reciprocal (t s : ℝ) (ht : 0 < t) (hs : 0 < t+s) :
    1/(t+s) = (1/t)/(1+s*(1/t)) := by
  have hn : 1+s*(1/t) ≠ 0 := by
    have : 0 < 1+s*(1/t) := by
      have h : 1+s*(1/t) = (t+s)/t := by field_simp
      rw [h]; exact div_pos hs ht
    exact ne_of_gt this
  field_simp

/-- Constant derivatives on the connected positive interval fix a primitive by one anchor. -/
theorem equal_of_equal_derivatives (F G : ℝ → ℝ)
    (hF : ∀ t > 0, DifferentiableAt ℝ F t)
    (hG : ∀ t > 0, DifferentiableAt ℝ G t)
    (hd : ∀ t > 0, deriv F t = deriv G t) (h1 : F 1 = G 1) :
    ∀ t > 0, F t = G t := by
  have hz : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun z => F z - G z) 0 (Ioi 0) x := by
    intro x hx
    simpa [hd x hx] using ((hF x hx).hasDerivAt.sub (hG x hx).hasDerivAt).hasDerivWithinAt
  intro t ht
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hz
    (by intro x hx; simp) (convex_Ioi (0 : ℝ)) (show (1 : ℝ) ∈ Ioi 0 by norm_num) ht
  have he : F t - G t - (F 1 - G 1) = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa using hb) (norm_nonneg _)
  rw [h1, sub_self, sub_zero] at he
  exact sub_eq_zero.mp he

theorem reciprocal_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => 1/t - 1) (-(1/t^2)) t := by
  convert ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) (ne_of_gt ht)).sub_const 1 using 1
  simp [one_div, neg_div]

theorem curvature_reconstruction (F : ℝ → ℝ)
    (hF : ∀ t > 0, DifferentiableAt ℝ F t)
    (hcurv : ∀ t > 0, HasDerivAt (deriv F) (-(1/t^2)) t)
    (hv : F 1 = 0) (hs : deriv F 1 = 0) :
    ∀ t > 0, F t = H t := by
  have he : ∀ t > 0, deriv F t = 1/t - 1 :=
    equal_of_equal_derivatives (deriv F) (fun t : ℝ => 1/t-1)
      (fun t ht => (hcurv t ht).differentiableAt)
      (fun t ht => (reciprocal_hasDerivAt ht).differentiableAt)
      (by intro t ht; rw [(hcurv t ht).deriv, (reciprocal_hasDerivAt ht).deriv])
      (by simpa using hs)
  apply reconstruct_H F _ hv
  intro t ht
  simpa [he t ht] using (hF t ht).hasDerivAt

theorem H_recentring {a v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    H (a*v) - H a - a * deriv H a * (v-1) = H v := by
  rw [H_deriv ha]
  simp only [H, SigmaPresentations.H, Real.log_mul (ne_of_gt ha) (ne_of_gt hv)]
  field_simp
  ring

theorem recentering_derivative_identity (F : ℝ → ℝ)
    (hd : ∀ t > 0, DifferentiableAt ℝ F t)
    (hr : ∀ a > 0, ∀ v > 0, F (a*v) - F a - a*deriv F a*(v-1) = F v)
    (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    a * (deriv F (a*v) - deriv F a) = deriv F v := by
  have hleft := (((hd (a*v) (mul_pos ha hv)).hasDerivAt.comp v
    ((hasDerivAt_id v).const_mul a)).sub_const (F a)).sub
    (((hasDerivAt_id v).sub_const 1).const_mul (a*deriv F a))
  have hright : HasDerivAt (fun v => F (a*v)-F a-a*deriv F a*(v-1))
      (deriv F v) v := by
    apply (hd v hv).hasDerivAt.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hv] with y hy
    exact hr a ha y hy
  have he := hleft.unique hright
  nlinarith

theorem recentering_transports_curvature (F : ℝ → ℝ)
    (hd : ∀ t > 0, DifferentiableAt ℝ F t)
    (hr : ∀ a > 0, ∀ v > 0, F (a*v) - F a - a*deriv F a*(v-1) = F v)
    (h2 : HasDerivAt (deriv F) (-1) 1)
    (a : ℝ) (ha : 0 < a) : HasDerivAt (deriv F) (-(1/a^2)) a := by
  have hn : a ≠ 0 := ne_of_gt ha
  have hi := (hasDerivAt_id a).div_const a
  have h1 : HasDerivAt (deriv F) (-1) (a/a) := by simpa [hn] using h2
  have hc := ((h1.comp (h := fun x : ℝ => x/a) a hi).div_const a).const_add (deriv F a)
  have hc' : HasDerivAt (fun x => deriv F a + deriv F (x/a)/a) (-(1/a^2)) a := by
    convert hc using 1
    field_simp
    ring
  apply hc'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ha] with x hx
  have he := recentering_derivative_identity F hd hr a (x/a) ha (div_pos hx ha)
  rw [mul_div_cancel₀ x hn] at he
  field_simp
  nlinarith

theorem recentering_reconstruction (F : ℝ → ℝ)
    (hd : ∀ t > 0, DifferentiableAt ℝ F t)
    (hr : ∀ a > 0, ∀ v > 0, F (a*v) - F a - a*deriv F a*(v-1) = F v)
    (h2 : HasDerivAt (deriv F) (-1) 1) : ∀ t > 0, F t = H t := by
  have hv : F 1 = 0 := by
    have h := hr 1 (by norm_num) 1 (by norm_num)
    simpa using h.symm
  have hs : deriv F 1 = 0 := by
    have h := recentering_derivative_identity F hd hr 1 1 (by norm_num) (by norm_num)
    simpa using h.symm
  exact curvature_reconstruction F hd (recentering_transports_curvature F hd hr h2) hv hs

/-- The integrating factor uses the candidate F itself; no ODE infrastructure is assumed. -/
theorem riccati_reconstruction (F : ℝ → ℝ)
    (hd : ∀ t > 0, DifferentiableAt ℝ F t)
    (hr : ∀ t > 0, HasDerivAt (deriv F) (-(deriv F t + 1)^2) t)
    (hv : F 1 = 0) (hs : deriv F 1 = 0) : ∀ t > 0, F t = H t := by
  let W : ℝ → ℝ := fun t => (t*(deriv F t+1)-1)*Real.exp (F t+t)
  have hw : ∀ t > 0, HasDerivAt W 0 t := by
    intro t ht
    have hq := (hr t ht).add_const 1
    have he := ((hd t ht).hasDerivAt.add (hasDerivAt_id t)).exp
    have hm := (((hasDerivAt_id t).mul hq).sub_const 1).mul he
    convert hm using 1
    ring
  have hz : ∀ t > 0, W t = 0 :=
    equal_of_equal_derivatives W (fun _ => 0)
      (fun t ht => (hw t ht).differentiableAt)
      (fun t _ => (hasDerivAt_const t (0 : ℝ)).differentiableAt)
      (by intro t ht; rw [(hw t ht).deriv]; simp)
      (by simp [W, hs])
  apply reconstruct_H F _ hv
  intro t ht
  have hq : t*(deriv F t+1)-1 = 0 :=
    (mul_eq_zero.mp (hz t ht)).resolve_right (Real.exp_ne_zero _)
  have hder : deriv F t = 1/t-1 := by
    apply (eq_sub_iff_add_eq).mpr
    apply (eq_div_iff (ne_of_gt ht)).mpr
    nlinarith
  simpa [hder] using (hd t ht).hasDerivAt

theorem recentering_iff (F : ℝ → ℝ)
    (hd : ∀ t > 0, DifferentiableAt ℝ F t)
    (h2 : HasDerivAt (deriv F) (-1) 1) :
    (∀ a > 0, ∀ v > 0, F (a*v)-F a-a*deriv F a*(v-1) = F v) ↔
      ∀ t > 0, F t = H t := by
  constructor
  · exact fun hr => recentering_reconstruction F hd hr h2
  · intro he a ha v hv
    have hda : deriv F a = deriv H a := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [isOpen_Ioi.mem_nhds ha] with t ht
      exact he t ht
    rw [he (a*v) (mul_pos ha hv), he a ha, he v hv, hda]
    exact H_recentring ha hv

theorem scaled_H_recentring (c : ℝ) {a v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    (c*H (a*v))-(c*H a)-a*deriv (fun t => c*H t) a*(v-1) = c*H v := by
  rw [((H_hasDerivAt ha).const_mul c).deriv]
  have he := H_recentring ha hv
  rw [H_deriv ha] at he
  linear_combination c*he

theorem H_two_neg : H 2 < 0 := by
  have h := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) (by norm_num : (2 : ℝ) ≠ 1)
  change Real.log 2 - 2 + 1 < 0
  linarith

theorem recentering_scale_calibration_necessary {c : ℝ} (hc : c ≠ 1) :
    ¬ ∀ t > 0, c*H t = H t := by
  intro h
  have h2 := h 2 (by norm_num)
  have he : (c-1)*H 2 = 0 := by nlinarith
  have hc' : c-1 ≠ 0 := sub_ne_zero.mpr hc
  exact (ne_of_lt H_two_neg) ((mul_eq_zero.mp he).resolve_left hc')

end
end Sigma
