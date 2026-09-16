import SigmaProbDeficitSmooth
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem deficit_upper_strictMono_closed : StrictMonoOn deficitUpperRoot (Ici (0:ℝ)) := by
  intro u hu v hv huv
  have hs := canonical_deficit_roots_spec u hu
  have ht := canonical_deficit_roots_spec v hv
  by_contra hn
  have hh := intrinsic_potential_two_branch.right_strict.monotoneOn ht.2.2.1 hs.2.2.1
    (le_of_not_gt hn)
  rw [hs.2.2.2.2,ht.2.2.2.2] at hh
  linarith

theorem deficit_lower_strictAnti_closed : StrictAntiOn deficitLowerRoot (Ici (0:ℝ)) := by
  intro u hu v hv huv
  have hs := canonical_deficit_roots_spec u hu
  have ht := canonical_deficit_roots_spec v hv
  by_contra hn
  have hh := intrinsic_potential_two_branch.left_strict.antitoneOn ⟨hs.1,hs.2.1⟩
    ⟨ht.1,ht.2.1⟩ (le_of_not_gt hn)
  rw [hs.2.2.2.1,ht.2.2.2.1] at hh
  linarith

theorem deficit_roots_at_zero : deficitLowerRoot 0 = 1 ∧ deficitUpperRoot 0 = 1 := by
  simp [deficitLowerRoot,deficitUpperRoot,canonical_deficit_roots_zero]

theorem deficit_upper_tendsto_zero : Tendsto deficitUpperRoot (𝓝[>] 0) (𝓝 1) := by
  have him : deficitUpperRoot '' Ici (0:ℝ) = Ici 1 := by
    ext t
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact (canonical_deficit_roots_spec v hv).2.2.1
    · intro ht
      exact ⟨SigmaBase.potential t,intrinsic_potential_two_branch.nonnegative (lt_of_lt_of_le (by norm_num) ht),
        canonical_deficit_upper_inverse t ht⟩
  have hc := deficit_upper_strictMono_closed.continuousWithinAt_right_of_image_mem_nhdsWithin
    self_mem_nhdsWithin (by rw [him,deficit_roots_at_zero.2]; exact self_mem_nhdsWithin)
  rw [ContinuousWithinAt,deficit_roots_at_zero.2] at hc
  exact hc.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

theorem deficit_lower_tendsto_zero : Tendsto deficitLowerRoot (𝓝[>] 0) (𝓝 1) := by
  have hm : StrictMonoOn (fun v => -deficitLowerRoot v) (Ici (0:ℝ)) := by
    intro u hu v hv huv
    exact neg_lt_neg (deficit_lower_strictAnti_closed hu hv huv)
  have him : (fun v => -deficitLowerRoot v) '' Ici (0:ℝ) = Ico (-1) 0 := by
    ext t
    constructor
    · rintro ⟨v,hv,rfl⟩
      have hs := canonical_deficit_roots_spec v hv
      change -1 ≤ -deficitLowerRoot v ∧ -deficitLowerRoot v < 0
      exact ⟨neg_le_neg hs.2.1,neg_neg_of_pos hs.1⟩
    · intro ht
      have hp : 0 < -t := neg_pos.mpr ht.2
      refine ⟨SigmaBase.potential (-t),intrinsic_potential_two_branch.nonnegative hp,?_⟩
      dsimp
      rw [show deficitLowerRoot (SigmaBase.potential (-t)) = -t from
        canonical_deficit_lower_inverse (-t) hp (by linarith [ht.1]),neg_neg]
  have hc := hm.continuousWithinAt_right_of_image_mem_nhdsWithin self_mem_nhdsWithin (by
    rw [him,deficit_roots_at_zero.1]
    exact Ico_mem_nhdsWithin_Ici (by norm_num))
  have hn := hc.neg
  simp only [ContinuousWithinAt,neg_neg,deficit_roots_at_zero.1] at hn
  exact hn.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

theorem deficit_density_scaled_formula (v : ℝ) (hv : 0 < v) :
    gammaDeficitDensity v*Real.sqrt v = Real.exp (-1-v)*
      (deficitLowerRoot v*Real.sqrt (potentialQuadraticFactor (deficitLowerRoot v)) +
       deficitUpperRoot v*Real.sqrt (potentialQuadraticFactor (deficitUpperRoot v))) := by
  have hs := deficit_roots_strict v hv
  have hspec := canonical_deficit_roots_spec v hv.le
  have hIa : SigmaBase.potential (deficitLowerRoot v) = v := hspec.2.2.2.1
  have hIb : SigmaBase.potential (deficitUpperRoot v) = v := hspec.2.2.2.2
  have hl : Real.sqrt v = (1-deficitLowerRoot v)*
      Real.sqrt (potentialQuadraticFactor (deficitLowerRoot v)) := by
    conv_lhs => rw [← hIa,potential_quadratic_factorization]
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_neg (sub_neg.mpr hs.2.1)]
    ring
  have hr : Real.sqrt v = (deficitUpperRoot v-1)*
      Real.sqrt (potentialQuadraticFactor (deficitUpperRoot v)) := by
    conv_lhs => rw [← hIb,potential_quadratic_factorization]
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos (sub_pos.mpr hs.2.2)]
  unfold gammaDeficitDensity
  rw [mul_assoc,add_mul]
  congr 1
  rw [show deficitLowerRoot v/(1-deficitLowerRoot v)*Real.sqrt v =
      deficitLowerRoot v*Real.sqrt (potentialQuadraticFactor (deficitLowerRoot v)) by
        rw [hl]; field_simp [sub_ne_zero.mpr hs.2.1.ne']; ring,
    show deficitUpperRoot v/(deficitUpperRoot v-1)*Real.sqrt v =
      deficitUpperRoot v*Real.sqrt (potentialQuadraticFactor (deficitUpperRoot v)) by
        rw [hr]; field_simp [sub_ne_zero.mpr hs.2.2.ne']; ring]

theorem gamma_deficit_density_asymptotic :
    Tendsto (fun v => gammaDeficitDensity v*Real.sqrt v) (𝓝[>] 0)
      (𝓝 (Real.sqrt 2/Real.exp 1)) := by
  have hr := potential_quadratic_factor_analytic.continuousAt
  have hl := deficit_lower_tendsto_zero.mul (Real.continuous_sqrt.continuousAt.tendsto.comp
    (hr.tendsto.comp deficit_lower_tendsto_zero))
  have hu := deficit_upper_tendsto_zero.mul (Real.continuous_sqrt.continuousAt.tendsto.comp
    (hr.tendsto.comp deficit_upper_tendsto_zero))
  have he : Tendsto (fun v:ℝ => Real.exp (-1-v)) (𝓝[>] 0) (𝓝 (Real.exp (-1))) := by
    have hh : ContinuousAt (fun v:ℝ => Real.exp (-1-v)) 0 := by fun_prop
    simpa using hh.tendsto.mono_left nhdsWithin_le_nhds
  have hh := he.mul (hl.add hu)
  have heq : Real.exp (-1)*(1*Real.sqrt (potentialQuadraticFactor 1)+
      1*Real.sqrt (potentialQuadraticFactor 1)) = Real.sqrt 2/Real.exp 1 := by
    rw [potential_quadratic_factor_one,Real.exp_neg]
    have hs : 2*Real.sqrt ((1:ℝ)/2) = Real.sqrt 2 := by
      have h₁ := Real.sq_sqrt (show (0:ℝ)≤1/2 by norm_num)
      have h₂ := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
      have hp := Real.sqrt_nonneg ((1:ℝ)/2)
      have hq := Real.sqrt_nonneg (2:ℝ)
      nlinarith
    simp only [one_mul]
    rw [← two_mul,hs]
    ring
  rw [heq] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact (deficit_density_scaled_formula v hv).symm


theorem gamma_deficit_density_equivalent :
    Asymptotics.IsEquivalent (𝓝[>] (0:ℝ)) gammaDeficitDensity
      (fun v => Real.sqrt 2/(Real.exp 1*Real.sqrt v)) := by
  apply Asymptotics.isEquivalent_iff_tendsto_one (by
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact div_ne_zero (Real.sqrt_pos.2 (by norm_num)).ne'
      (mul_ne_zero (Real.exp_ne_zero _) (Real.sqrt_pos.2 hv).ne')) |>.mpr
  have hc : Real.sqrt 2/Real.exp 1 ≠ 0 :=
    div_ne_zero (Real.sqrt_pos.2 (by norm_num)).ne' (Real.exp_ne_zero _)
  have hh := gamma_deficit_density_asymptotic.div_const (Real.sqrt 2/Real.exp 1)
  rw [div_self hc] at hh
  convert hh using 1
  funext v
  simp only [Pi.div_apply,div_div,div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

end
end Sigma
