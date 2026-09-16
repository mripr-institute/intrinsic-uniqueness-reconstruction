import SigmaBase
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace SigmaBase

theorem potential_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt potential (1 - 1 / t) t := by
  simpa [potential, one_div] using
    ((hasDerivAt_id t).sub_const 1).sub (Real.hasDerivAt_log (ne_of_gt ht))

theorem reconstruct_from_derivative (phi : ℝ → ℝ)
    (hdiff : DifferentiableOn ℝ phi (Set.Ioi 0))
    (hnorm : phi 1 = 0)
    (hderiv : ∀ t > 0, deriv phi t = 1 - 1 / t) :
    ∀ t > 0, phi t = potential t := by
  intro t ht
  have hphi : ∀ x > 0, HasDerivAt phi (1 - 1 / x) x := by
    intro x hx
    have hd := (hdiff x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
    simpa [hderiv x hx] using hd.hasDerivAt
  have hz : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun z => phi z - potential z) 0 (Set.Ioi 0) x := by
    intro x hx
    simpa using ((hphi x hx).sub (potential_hasDerivAt hx)).hasDerivWithinAt
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hz
    (by intro x hx; simp) (convex_Ioi (0 : ℝ)) (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) ht
  have heq : phi t - potential t - (phi 1 - potential 1) = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa using hb) (norm_nonneg _)
  apply sub_eq_zero.mp
  simpa [hnorm, potential] using heq

#print axioms potential_hasDerivAt
#print axioms reconstruct_from_derivative
end SigmaBase
