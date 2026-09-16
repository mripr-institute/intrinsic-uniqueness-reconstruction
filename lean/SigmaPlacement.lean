import SigmaCore

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology

def placed (μ a r : ℝ) : ℝ := H (μ*r+a) + Real.log (μ/(1+a)) + a - 1

def placedOriginal (μ γ r : ℝ) : ℝ :=
  Real.log (μ^2*(1+γ*r)/(μ+γ)) - μ*r

theorem placed_coordinate_positive {μ a r : ℝ} (hμ : 0 < μ) :
    -a/μ < r ↔ 0 < μ*r+a := by
  rw [div_lt_iff₀ hμ]
  constructor <;> intro h <;> nlinarith

theorem placed_coordinate_inverse {μ a : ℝ} (hμ : 0 < μ) (t : ℝ) :
    μ*((t-a)/μ)+a = t := by field_simp

theorem placed_coordinate_bijective {μ a : ℝ} (hμ : 0 < μ) :
    BijOn (fun r : ℝ => μ*r+a) (Ioi (-a/μ)) (Ioi 0) := by
  refine ⟨fun r hr => (placed_coordinate_positive hμ).mp hr, ?_, ?_⟩
  · intro x hx y hy he
    dsimp at he
    have : μ*x = μ*y := by linarith
    exact mul_left_cancel₀ (ne_of_gt hμ) this
  · intro t ht
    refine ⟨(t-a)/μ, ?_, placed_coordinate_inverse hμ t⟩
    apply (placed_coordinate_positive hμ).mpr
    rwa [placed_coordinate_inverse hμ]

theorem placed_original_identity {μ a r : ℝ}
    (hμ : 0 < μ) (ha : 0 < a) (ht : 0 < μ*r+a) :
    placedOriginal μ (μ/a) r = placed μ a r := by
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hap : 0 < 1+a := by linarith
  have he : μ^2*(1+(μ/a)*r)/(μ+μ/a) = (μ/(1+a))*(μ*r+a) := by
    field_simp
    ring
  unfold placedOriginal placed
  rw [he, Real.log_mul (ne_of_gt (div_pos hμ hap)) (ne_of_gt ht)]
  unfold H SigmaPresentations.H
  ring

theorem placed_hasDerivAt {μ a r : ℝ} (ht : 0 < μ*r+a) :
    HasDerivAt (placed μ a) (μ/(μ*r+a)-μ) r := by
  have hd := (((H_hasDerivAt ht).comp r
    (((hasDerivAt_id r).const_mul μ).add_const a)).add_const
    (Real.log (μ/(1+a)))).add_const a |>.sub_const 1
  convert hd using 1
  ring

theorem placed_deriv {μ a r : ℝ} (ht : 0 < μ*r+a) :
    deriv (placed μ a) r = μ/(μ*r+a)-μ := (placed_hasDerivAt ht).deriv

theorem placed_second_hasDerivAt {μ a r : ℝ} (ht : 0 < μ*r+a) :
    HasDerivAt (deriv (placed μ a)) (-(μ/(μ*r+a))^2) r := by
  have hd := ((hasDerivAt_const r μ).div
    (((hasDerivAt_id r).const_mul μ).add_const a) (ne_of_gt ht)).sub_const μ
  have he : HasDerivAt (fun r => μ/(μ*r+a)-μ) (-(μ/(μ*r+a))^2) r := by
    convert hd using 1
    field_simp
    ring
  apply he.congr_of_eventuallyEq
  have ho : IsOpen {x : ℝ | 0 < μ*x+a} :=
    isOpen_lt continuous_const ((continuous_const.mul continuous_id).add continuous_const)
  filter_upwards [ho.mem_nhds ht] with x hx
  exact placed_deriv hx

theorem placed_second_deriv {μ a r : ℝ} (ht : 0 < μ*r+a) :
    deriv (deriv (placed μ a)) r = -(μ/(μ*r+a))^2 :=
  (placed_second_hasDerivAt ht).deriv

theorem placed_closure {μ a : ℝ} (hμ : 0 < μ) :
    deriv (placed μ a) ((1-a)/μ) = 0 ∧
    deriv (deriv (placed μ a)) ((1-a)/μ) = -μ^2 := by
  have he := placed_coordinate_inverse (a := a) hμ 1
  have ht : 0 < μ*((1-a)/μ)+a := by rw [he]; norm_num
  rw [placed_deriv ht, placed_second_deriv ht, he]
  simp

theorem placed_parameter_recovery {μ a r : ℝ}
    (hμ : 0 < μ) (ha : 0 < a) (ht : 0 < μ*r+a) :
    Real.sqrt (-deriv (deriv (placed μ a)) r) - deriv (placed μ a) r = μ ∧
    Real.sqrt (-deriv (deriv (placed μ a)) r) /
      (1-r*Real.sqrt (-deriv (deriv (placed μ a)) r)) = μ/a := by
  rw [placed_deriv ht, placed_second_deriv ht, neg_neg,
    Real.sqrt_sq (div_pos hμ ht).le]
  constructor
  · ring
  · have he : 1-r*(μ/(μ*r+a)) = a/(μ*r+a) := by field_simp; ring
    rw [he]
    field_simp

theorem intrinsic_log_density {t : ℝ} (ht : 0 < t) :
    H t = 1 + Real.log (p t) := by
  change SigmaPresentations.H t = 1 + Real.log (SigmaPresentations.density t)
  rw [SigmaPresentations.density_eq_exp_H ht, Real.log_exp]
  ring

theorem placed_density_identity {μ a r : ℝ}
    (hμ : 0 < μ) (ha : 0 < a) (ht : 0 < μ*r+a) :
    Real.exp (placed μ a r) = μ * Real.exp a / (1+a) * p (μ*r+a) := by
  have he : placed μ a r = (H (μ*r+a)-1)+Real.log (μ/(1+a))+a := by
    unfold placed; ring
  rw [he, Real.exp_add, Real.exp_add,
    Real.exp_log (div_pos hμ (by linarith)), ← SigmaPresentations.density_eq_exp_H ht]
  ring

theorem placed_parameters_unique {μ a ν b : ℝ}
    (hμ : 0 < μ) (ha : 0 < a) (hν : 0 < ν) (hb : 0 < b)
    (he : ∀ r > 0, placed μ a r = placed ν b r) : μ = ν ∧ a = b := by
  have h1 : ∀ r > 0, deriv (placed μ a) r = deriv (placed ν b) r := by
    intro r hr
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioi.mem_nhds hr] with x hx
    exact he x hx
  have h2 : deriv (deriv (placed μ a)) 1 = deriv (deriv (placed ν b)) 1 := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioi.mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact h1 x hx
  have hm := placed_parameter_recovery (r := 1) hμ ha (by nlinarith)
  have hn := placed_parameter_recovery (r := 1) hν hb (by nlinarith)
  rw [h2, h1 1 (by norm_num)] at hm
  have hv : μ = ν := hm.1.symm.trans hn.1
  refine ⟨hv, ?_⟩
  have hq : μ/a = ν/b := hm.2.symm.trans hn.2
  rw [hv] at hq
  have hcross := (div_eq_div_iff (ne_of_gt ha) (ne_of_gt hb)).mp hq
  exact mul_left_cancel₀ (ne_of_gt hν) hcross.symm

theorem placement_scale_is_independent :
    ¬ ∀ r > 0, placed 1 (1/2) r = placed 2 (1/2) r := by
  intro h
  have he := placed_parameters_unique (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) h
  norm_num at he

theorem placement_offset_is_independent :
    ¬ ∀ r > 0, placed 1 (1/2) r = placed 1 (1/3) r := by
  intro h
  have he := placed_parameters_unique (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) h
  norm_num at he

end
end Sigma
