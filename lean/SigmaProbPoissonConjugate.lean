import SigmaProbPoisson
import Mathlib.Topology.Instances.EReal

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

def poissonCenteredConjugate (z : ℝ) : EReal :=
  ⨆ u : ℝ, ((u*z-SigmaPresentations.centeredCGF u : ℝ) : EReal)

theorem poisson_centered_conjugate_bound (z u : ℝ) (hz : -1 < z) :
    u*z-SigmaPresentations.centeredCGF u ≤ (1+z)*Real.log (1+z)-z := by
  have hr : 0 < 1+z := by linarith
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (u-Real.log (1+z))) hr.le
  rw [Real.exp_sub,Real.exp_log hr,mul_div_cancel₀ _ hr.ne'] at hh
  unfold SigmaPresentations.centeredCGF
  nlinarith

theorem poisson_centered_conjugate_interior (z : ℝ) (hz : -1 < z) :
    poissonCenteredConjugate z = ((1+z)*Real.log (1+z)-z : ℝ) := by
  apply le_antisymm
  · apply iSup_le
    intro u
    exact EReal.coe_le_coe_iff.mpr (poisson_centered_conjugate_bound z u hz)
  · have hh := le_iSup (fun u : ℝ => ((u*z-SigmaPresentations.centeredCGF u : ℝ) : EReal)) (Real.log (1+z))
    have he : Real.log (1+z)*z-SigmaPresentations.centeredCGF (Real.log (1+z)) =
        (1+z)*Real.log (1+z)-z := by
      unfold SigmaPresentations.centeredCGF
      rw [Real.exp_log (by linarith : 0 < 1+z)]
      ring
    rwa [he] at hh

theorem poisson_centered_conjugate_boundary : poissonCenteredConjugate (-1) = 1 := by
  apply le_antisymm
  · apply iSup_le
    intro u
    have hh : u*(-1)-SigmaPresentations.centeredCGF u ≤ 1 := by
      unfold SigmaPresentations.centeredCGF
      linarith [Real.exp_pos u]
    exact_mod_cast hh
  · have hl : Tendsto (fun u:ℝ => (1-Real.exp u : ℝ)) atBot (𝓝 1) := by
      simpa using tendsto_const_nhds.sub Real.tendsto_exp_atBot
    have he : Tendsto (fun u:ℝ => ((1-Real.exp u : ℝ) : EReal)) atBot (𝓝 (1:EReal)) := by
      simpa using EReal.tendsto_coe.mpr hl
    apply le_of_tendsto he
    apply Eventually.of_forall
    intro u
    have hh := le_iSup (fun u : ℝ => ((u*(-1)-SigmaPresentations.centeredCGF u : ℝ) : EReal)) u
    have hid : u*(-1)-SigmaPresentations.centeredCGF u = 1-Real.exp u := by
      unfold SigmaPresentations.centeredCGF
      ring
    rwa [hid] at hh

theorem poisson_centered_conjugate_exterior (z : ℝ) (hz : z < -1) :
    poissonCenteredConjugate z = ⊤ := by
  have hl : Tendsto (fun u:ℝ => (z+1)*u) atBot atTop :=
    tendsto_id.const_mul_atBot_of_neg (by linarith)
  have hnon : ∀ᶠ u:ℝ in atBot, 0 ≤ 1-Real.exp u := by
    filter_upwards [eventually_le_atBot (0:ℝ)] with u hu
    have hh := Real.exp_le_exp.mpr hu
    simp only [Real.exp_zero] at hh
    linarith
  have ht := tendsto_atTop_add_nonneg_right' hl hnon
  have heq : (fun u:ℝ => (z+1)*u+(1-Real.exp u)) =
      (fun u:ℝ => u*z-SigmaPresentations.centeredCGF u) := by
    funext u
    unfold SigmaPresentations.centeredCGF
    ring
  rw [heq] at ht
  have he : Tendsto (fun u:ℝ => ((u*z-SigmaPresentations.centeredCGF u : ℝ) : EReal)) atBot (𝓝 ⊤) := by
    apply EReal.tendsto_nhds_top_iff_real.mpr
    intro r
    filter_upwards [ht.eventually_gt_atTop r] with u hu
    exact_mod_cast hu
  apply top_le_iff.mp
  apply le_of_tendsto he
  exact Eventually.of_forall (fun u => le_iSup
    (fun u:ℝ => ((u*z-SigmaPresentations.centeredCGF u:ℝ):EReal)) u)

theorem poisson_centered_conjugate_complete (z : ℝ) :
    poissonCenteredConjugate z =
      if -1 < z then (((1+z)*Real.log (1+z)-z : ℝ):EReal)
      else if z = -1 then 1 else ⊤ := by
  split_ifs with h₁ h₂
  · exact poisson_centered_conjugate_interior z h₁
  · simpa [h₂] using poisson_centered_conjugate_boundary
  · exact poisson_centered_conjugate_exterior z (lt_of_le_of_ne (le_of_not_gt h₁) h₂)

end
end Sigma
