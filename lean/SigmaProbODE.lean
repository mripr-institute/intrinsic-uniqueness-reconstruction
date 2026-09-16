import SigmaProbSurvival
import SigmaCore

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

/-- The normalized second-order Green-kernel equation on the open positive ray.
The derivative equations imply the manuscript's C2 regularity there. -/
theorem normalized_second_order_density_unique (f f' : ℝ → ℝ)
    (hf : ∀ t > 0, HasDerivAt f (f' t) t)
    (hff : ∀ t > 0, HasDerivAt f' (-2*f' t-f t) t)
    (hc0 : ContinuousAt f 0) (h0 : f 0 = 0)
    (hmass : (∫ t : ℝ in Ioi 0, f t) = 1) :
    ∀ t > 0, f t = SigmaPresentations.density t := by
  let G : ℝ → ℝ := fun t => Real.exp t * f t
  let G' : ℝ → ℝ := fun t => Real.exp t * (f t+f' t)
  have hG : ∀ t > 0, HasDerivAt G (G' t) t := by
    intro t ht
    convert (Real.hasDerivAt_exp t).mul (hf t ht) using 1
    dsimp [G']
    ring
  have hG' : ∀ t > 0, HasDerivAt G' 0 t := by
    intro t ht
    convert (Real.hasDerivAt_exp t).mul ((hf t ht).add (hff t ht)) using 1
    ring
  let B : ℝ := G' 1
  have hB : ∀ t > 0, G' t = B :=
    equal_of_equal_derivatives G' (fun _ => B)
      (fun t ht => (hG' t ht).differentiableAt)
      (fun t _ => differentiableAt_const B)
      (by intro t ht; rw [(hG' t ht).deriv]; simp) rfl
  let A : ℝ := G 1-B
  have hline : ∀ t > 0, G t = A+B*t := by
    apply equal_of_equal_derivatives G (fun t => A+B*t)
      (fun t ht => (hG t ht).differentiableAt)
      (fun t _ => by fun_prop)
    · intro t ht
      rw [(hG t ht).deriv, hB t ht]
      have hd : HasDerivAt (fun t : ℝ => A+B*t) B t := by
        simpa using ((hasDerivAt_id t).const_mul B).const_add A
      rw [hd.deriv]
    · dsimp [A]
      ring
  have hfun : ∀ t > 0, f t = (A+B*t)*Real.exp (-t) := by
    intro t ht
    have he := hline t ht
    dsimp [G] at he
    rw [Real.exp_neg]
    apply (eq_mul_inv_iff_mul_eq₀ (Real.exp_ne_zero t)).mpr
    simpa [mul_comm] using he
  have hf0 : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    simpa [h0] using hc0.tendsto.mono_left nhdsWithin_le_nhds
  have hg0 : Tendsto (fun t : ℝ => (A+B*t)*Real.exp (-t)) (𝓝[>] 0) (𝓝 A) := by
    have hc : Continuous (fun t : ℝ => (A+B*t)*Real.exp (-t)) := by fun_prop
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have heq : f =ᶠ[𝓝[>] (0 : ℝ)] (fun t => (A+B*t)*Real.exp (-t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hfun t ht
  have hA0 : A = 0 := (tendsto_nhds_unique hf0 (hg0.congr' heq.symm)).symm
  have hp : ∀ t > 0, f t = B*SigmaPresentations.density t := by
    intro t ht
    rw [hfun t ht, hA0]
    unfold SigmaPresentations.density
    ring
  have hBi : (∫ t : ℝ in Ioi 0, f t) = B := by
    calc
      (∫ t : ℝ in Ioi 0, f t) = ∫ t : ℝ in Ioi 0, B*SigmaPresentations.density t :=
        setIntegral_congr_fun measurableSet_Ioi hp
      _ = B := by rw [integral_mul_left, intrinsic_density_integral_one, mul_one]
  have hB1 : B = 1 := hBi.symm.trans hmass
  intro t ht
  simpa [hB1] using hp t ht

end
end Sigma
