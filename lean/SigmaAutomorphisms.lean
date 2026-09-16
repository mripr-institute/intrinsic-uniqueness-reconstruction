import SigmaCore

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology

theorem group_log_derivative_with_slope (L : ℝ → ℝ) (c : ℝ)
    (h0 : HasDerivAt L c 0)
    (hh : ∀ x > -1, ∀ y > -1, L (star x y) = L x + L y)
    (x : ℝ) (hx : -1 < x) : HasDerivAt L (c/(1+x)) x := by
  have hp : 0 < 1+x := by linarith
  have ha : HasDerivAt (fun s : ℝ => (s-x)/(1+x)) (1/(1+x)) x := by
    simpa using ((hasDerivAt_id x).sub_const x).div_const (1+x)
  have hb : HasDerivAt L c ((x-x)/(1+x)) := by simpa using h0
  have hc : HasDerivAt (fun s : ℝ => L x+L ((s-x)/(1+x))) (c/(1+x)) x := by
    convert (hb.comp (h := fun s : ℝ => (s-x)/(1+x)) x ha).const_add (L x) using 1
    ring
  apply hc.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with s hs
  change -1 < s at hs
  have hy : -1 < (s-x)/(1+x) := by
    apply (lt_div_iff₀ hp).mpr
    linarith
  have he : star x ((s-x)/(1+x)) = s := by
    unfold star SigmaBase.star
    field_simp
    ring
  simpa only [he] using hh x hx ((s-x)/(1+x)) hy

theorem group_log_slope_unique (L : ℝ → ℝ) (c : ℝ)
    (h0 : HasDerivAt L c 0)
    (hh : ∀ x > -1, ∀ y > -1, L (star x y) = L x + L y) :
    ∀ x > -1, L x = c*Real.log (1+x) := by
  have hz : L 0 = 0 := by
    have h := hh 0 (by norm_num) 0 (by norm_num)
    simpa [star, SigmaBase.star] using h.symm
  have hd : ∀ x ∈ Ioi (-1 : ℝ),
      HasDerivWithinAt (fun x => L x-c*Real.log (1+x)) 0 (Ioi (-1)) x := by
    intro x hx
    have hx' : -1 < x := hx
    have hl : HasDerivAt (fun x : ℝ => c*Real.log (1+x)) (c/(1+x)) x := by
      convert (((hasDerivAt_id x).const_add 1).log (by linarith : (1+x : ℝ) ≠ 0)).const_mul c using 1
      simp [id_eq, div_eq_mul_inv]
    simpa using ((group_log_derivative_with_slope L c h0 hh x hx).sub hl).hasDerivWithinAt
  intro x hx
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hd
    (by intro y hy; simp) (convex_Ioi (-1 : ℝ))
    (show (0 : ℝ) ∈ Ioi (-1) by norm_num) hx
  have he : L x-c*Real.log (1+x)-(L 0-c*Real.log (1+0)) = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa using hb) (norm_nonneg _)
  exact sub_eq_zero.mp (by simpa [hz] using he)

def groupPower (c x : ℝ) : ℝ := Real.exp (c*Real.log (1+x))-1

theorem groupPower_closed (c x : ℝ) : -1 < groupPower c x := by
  have h := Real.exp_pos (c*Real.log (1+x))
  unfold groupPower
  linarith

theorem group_endomorphism_classification (φ : ℝ → ℝ) (c : ℝ)
    (hD : ∀ x > -1, -1 < φ x)
    (hh : ∀ x > -1, ∀ y > -1, φ (star x y) = star (φ x) (φ y))
    (h0 : HasDerivAt φ c 0) :
    ∀ x > -1, φ x = groupPower c x := by
  have hz : φ 0 = 0 := by
    have he := hh 0 (by norm_num) 0 (by norm_num)
    have hp := hD 0 (by norm_num)
    simp only [star, SigmaBase.star, add_zero, mul_zero, zero_add] at he
    have hq : φ 0*(φ 0+1) = 0 := by nlinarith
    exact (mul_eq_zero.mp hq).resolve_right (by linarith)
  let L : ℝ → ℝ := fun x => Real.log (1+φ x)
  have hL0 : HasDerivAt L c 0 := by
    have h := (h0.const_add 1).log (show 1+φ 0 ≠ 0 by simp [hz])
    simpa [hz, L] using h
  have hLh : ∀ x > -1, ∀ y > -1, L (star x y) = L x+L y := by
    intro x hx y hy
    unfold L
    rw [hh x hx y hy]
    exact SigmaBase.log_star (hD x hx) (hD y hy)
  intro x hx
  have he := group_log_slope_unique L c hL0 hLh x hx
  have he' := congrArg Real.exp he
  dsimp [L] at he'
  rw [Real.exp_log (by linarith [hD x hx] : 0 < 1+φ x)] at he'
  unfold groupPower
  linarith

theorem group_automorphism_slope_nonzero (φ : ℝ → ℝ) (c : ℝ)
    (hD : ∀ x > -1, -1 < φ x)
    (hh : ∀ x > -1, ∀ y > -1, φ (star x y) = star (φ x) (φ y))
    (h0 : HasDerivAt φ c 0) (hinj : InjOn φ (Ioi (-1))) : c ≠ 0 := by
  intro hc
  have he := group_endomorphism_classification φ c hD hh h0
  have h01 : φ 0 = φ 1 := by
    rw [he 0 (by norm_num), he 1 (by norm_num), hc]
    simp [groupPower]
  have h := hinj (by norm_num) (by norm_num) h01
  norm_num at h

theorem groupPower_composition (c d x : ℝ) :
    groupPower c (groupPower d x) = groupPower (c*d) x := by
  unfold groupPower
  rw [show 1+(Real.exp (d*Real.log (1+x))-1) = Real.exp (d*Real.log (1+x)) by ring,
    Real.log_exp]
  ring_nf

theorem groupPower_one {x : ℝ} (hx : -1 < x) : groupPower 1 x = x := by
  unfold groupPower
  rw [one_mul, Real.exp_log (by linarith : 0 < 1+x)]
  ring

theorem groupPower_inverse (c x : ℝ) (hc : c ≠ 0) (hx : -1 < x) :
    groupPower (1/c) (groupPower c x) = x ∧ groupPower c (groupPower (1/c) x) = x := by
  rw [groupPower_composition, groupPower_composition,
    one_div_mul_cancel hc, mul_one_div_cancel hc, groupPower_one hx]
  exact ⟨rfl,rfl⟩

theorem groupPower_hom (c : ℝ) {x y : ℝ} (hx : -1 < x) (hy : -1 < y) :
    groupPower c (star x y) = star (groupPower c x) (groupPower c y) := by
  unfold groupPower
  rw [SigmaBase.log_star hx hy, mul_add, Real.exp_add]
  unfold star SigmaBase.star
  ring

end
end Sigma
