import SigmaProbGamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Sigma
noncomputable section
open Filter MeasureTheory Set
open scoped Topology

def gammaSurvival (x : ℝ) : ℝ := (1 + x) * Real.exp (-x)
def gammaHazard (x : ℝ) : ℝ := x / (1 + x)
def logisticHazard (u : ℝ) : ℝ := Real.exp u / (1 + Real.exp u)

theorem gamma_survival_derivative (x : ℝ) :
    HasDerivAt gammaSurvival (-SigmaPresentations.density x) x := by
  convert (((hasDerivAt_id x).const_add 1).mul
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x))) using 1 ;
    simp [gammaSurvival, SigmaPresentations.density] ; ring

theorem gamma_survival_positive {x : ℝ} (hx : 0 ≤ x) : 0 < gammaSurvival x := by
  unfold gammaSurvival
  positivity

theorem gamma_survival_anchor : gammaSurvival 0 = 1 := by simp [gammaSurvival]

theorem gamma_survival_tendsto : Tendsto gammaSurvival atTop (𝓝 0) := by
  have he : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hx := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hf : gammaSurvival = fun x => Real.exp (-x) + x * Real.exp (-x) := by
    funext x
    unfold gammaSurvival
    ring
  rw [hf]
  simpa using he.add hx

theorem gamma_survival_tail_integral (x : ℝ) (hx : 0 ≤ x) :
    (∫ t : ℝ in Ioi x, SigmaPresentations.density t) = gammaSurvival x := by
  have hd : ∀ t ∈ Ici x,
      HasDerivAt (fun y => -gammaSurvival y) (SigmaPresentations.density t) t := by
    intro t ht
    simpa using (gamma_survival_derivative t).neg
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    (intrinsic_density_integrable.mono_set (Ioi_subset_Ioi hx))
    gamma_survival_tendsto.neg
  simpa using hi

theorem gamma_hazard_ratio (x : ℝ) (hx : 0 ≤ x) :
    SigmaPresentations.density x / gammaSurvival x = gammaHazard x := by
  unfold SigmaPresentations.density gammaSurvival gammaHazard
  field_simp
  ring

theorem gamma_self_survival_shift (x : ℝ) :
    gammaSurvival x = SigmaPresentations.density (1 + x) / SigmaPresentations.density 1 := by
  unfold gammaSurvival SigmaPresentations.density
  rw [neg_add, Real.exp_add]
  field_simp
  ring

theorem gamma_survival_potential (x : ℝ) (hx : 0 ≤ x) :
    gammaSurvival x = Real.exp (-SigmaBase.potential (1 + x)) := by
  have hx1 : 0 < 1 + x := by linarith
  unfold gammaSurvival SigmaBase.potential
  have hh : -(1 + x - 1 - Real.log (1 + x)) = Real.log (1 + x) + (-x) := by ring
  rw [hh, Real.exp_add, Real.exp_log hx1]

/-- The normalized hazard equation has no additional differentiable solutions.
The proof retains one-sided derivatives at zero and proves the normalization constant. -/
theorem gamma_hazard_unique_differentiable (Q : ℝ → ℝ)
    (hq : ∀ x ∈ Ici (0 : ℝ), 0 < Q x) (hzero : Q 0 = 1)
    (hderiv : ∀ x ∈ Ici (0 : ℝ),
      HasDerivWithinAt Q (-gammaHazard x * Q x) (Ici 0) x) :
    ∀ x ∈ Ici (0 : ℝ), Q x = gammaSurvival x := by
  let L : ℝ → ℝ := fun x => Real.log (Q x) + x - Real.log (1 + x)
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt L 0 (Ici 0) x := by
    intro x hx
    have hqp := hq x hx
    have hxp : 0 < 1 + x := by have := hx; simp only [mem_Ici] at this; linarith
    have hlog := (hderiv x hx).log (ne_of_gt hqp)
    have hlog1 := ((hasDerivAt_id x).const_add 1).log (ne_of_gt hxp)
    convert (hlog.add (hasDerivWithinAt_id x (Ici 0))).sub hlog1.hasDerivWithinAt using 1
    unfold gammaHazard
    simp only [id_eq]
    field_simp [ne_of_gt hqp, ne_of_gt hxp]
    ring
  intro x hx
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hd
    (by intro y hy; simp) (convex_Ici (0 : ℝ))
    (show (0 : ℝ) ∈ Ici (0 : ℝ) by simp) hx
  have he : L x = L 0 := by
    have : ‖L x - L 0‖ ≤ 0 := by simpa using hb
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm this (norm_nonneg _)))
  have hl : Real.log (Q x) = Real.log (1 + x) - x := by
    dsimp [L] at he
    simp [hzero] at he
    linarith
  have hxp : 0 < 1 + x := by have := hx; simp only [mem_Ici] at this; linarith
  rw [← Real.exp_log (hq x hx), hl, Real.exp_sub, Real.exp_log hxp]
  simp [gammaSurvival, Real.exp_neg, div_eq_mul_inv]

theorem logistic_hazard_coordinate (u : ℝ) :
    logisticHazard u = gammaHazard (Real.exp u) := rfl

theorem logistic_hazard_anchor : logisticHazard 0 = 1 / 2 := by
  norm_num [logisticHazard]

theorem logistic_hazard_derivative (u : ℝ) :
    HasDerivAt logisticHazard (logisticHazard u * (1 - logisticHazard u)) u := by
  have hp : 1 + Real.exp u ≠ 0 := ne_of_gt (by positivity)
  convert (Real.hasDerivAt_exp u).div ((Real.hasDerivAt_exp u).const_add 1) hp using 1
  unfold logisticHazard
  field_simp
  ring

theorem exponential_pair_convolution (t : ℝ) :
    (∫ s : ℝ in (0 : ℝ)..t, Real.exp (-s) * Real.exp (-(t - s))) =
      SigmaPresentations.density t := by
  have hfun : (fun s : ℝ => Real.exp (-s) * Real.exp (-(t - s))) =
      (fun _ : ℝ => Real.exp (-t)) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfun, intervalIntegral.integral_const]
  simp [SigmaPresentations.density]

/-- Global logistic uniqueness requires no a priori range restriction. -/
theorem logistic_hazard_unique (v : ℝ → ℝ)
    (hv : ∀ u, HasDerivAt v (v u * (1-v u)) u) (h0 : v 0 = 1/2) :
    v = logisticHazard := by
  have hcont : Continuous v := continuous_iff_continuousAt.mpr
    (fun u => (hv u).continuousAt)
  let A : ℝ → ℝ := fun u => ∫ t : ℝ in (0 : ℝ)..u, v t
  let W : ℝ → ℝ := fun u => ((1+Real.exp u)*v u-Real.exp u)*Real.exp (A u-u)
  have hA : ∀ u, HasDerivAt A (v u) u := fun u =>
    (hcont.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hW : ∀ u, HasDerivAt W 0 u := by
    intro u
    have he := (Real.hasDerivAt_exp u)
    have hB := ((he.const_add 1).mul (hv u)).sub he
    have hm := hB.mul (((hA u).sub (hasDerivAt_id u)).exp)
    convert hm using 1
    ring
  have hzero : W 0 = 0 := by simp [W, A, h0]; ring
  have hconst : ∀ u, W u = 0 := by
    intro u
    rw [← hzero]
    exact is_const_of_deriv_eq_zero (fun t => (hW t).differentiableAt)
      (fun t => (hW t).deriv) u 0
  funext u
  have hB : (1+Real.exp u)*v u-Real.exp u = 0 :=
    (mul_eq_zero.mp (hconst u)).resolve_right (Real.exp_ne_zero _)
  unfold logisticHazard
  apply (eq_div_iff (ne_of_gt (by positivity : 0 < 1+Real.exp u))).mpr
  linarith

end
end Sigma
