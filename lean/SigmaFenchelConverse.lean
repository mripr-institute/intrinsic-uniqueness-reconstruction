import SigmaFenchel
import Mathlib.Topology.Instances.EReal
import Mathlib.Topology.Semicontinuous
import Mathlib.Analysis.Convex.Function

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology

/-- The literal extended-real function from final:C5. -/
def extendedIntrinsic (t : ℝ) : EReal := if 0 < t then (I t : EReal) else ⊤

/-- The actual full supremum, over every real primal coordinate. -/
def fullFenchelConjugate (F : ℝ → EReal) (θ : ℝ) : EReal :=
  ⨆ t : ℝ, (θ * t : ℝ) - F t

def intrinsicConjugateTarget (θ : ℝ) : EReal :=
  if θ < 1 then (-Real.log (1 - θ) : ℝ) else ⊤

/-- Standard extended-real convexity as convexity of the real epigraph. -/
def ExtendedConvex (F : ℝ → EReal) : Prop :=
  Convex ℝ {p : ℝ × ℝ | F p.1 ≤ (p.2 : EReal)}

theorem extended_intrinsic_conjugate_finite {θ : ℝ} (hθ : θ < 1) :
    fullFenchelConjugate extendedIntrinsic θ = (-Real.log (1 - θ) : ℝ) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    by_cases ht : 0 < t
    · simpa only [extendedIntrinsic, if_pos ht, ← EReal.coe_sub, EReal.coe_le_coe_iff]
        using fenchel_upper_bound hθ ht
    · simp [extendedIntrinsic, ht]
  · have ht : 0 < 1 / (1 - θ) := one_div_pos.mpr (sub_pos.mpr hθ)
    apply le_iSup_of_le (1 / (1 - θ))
    rw [extendedIntrinsic, if_pos ht, ← EReal.coe_sub,
      (fenchel_equality_iff hθ ht).mpr rfl]

theorem extended_intrinsic_conjugate_infinite {θ : ℝ} (hθ : 1 ≤ θ) :
    fullFenchelConjugate extendedIntrinsic θ = ⊤ := by
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro M
  apply lt_of_lt_of_le _ (le_iSup (fun t : ℝ => ((θ * t : ℝ) : EReal) - extendedIntrinsic t) (Real.exp M))
  rw [extendedIntrinsic, if_pos (Real.exp_pos M), ← EReal.coe_sub, EReal.coe_lt_coe_iff]
  have hn : 0 ≤ (θ - 1) * Real.exp M := mul_nonneg (sub_nonneg.mpr hθ) (Real.exp_pos M).le
  unfold I SigmaBase.potential
  rw [Real.log_exp]
  nlinarith

theorem extended_intrinsic_full_conjugate :
    fullFenchelConjugate extendedIntrinsic = intrinsicConjugateTarget := by
  funext θ
  by_cases hθ : θ < 1
  · exact (extended_intrinsic_conjugate_finite hθ).trans (if_pos hθ).symm
  · exact (extended_intrinsic_conjugate_infinite (le_of_not_gt hθ)).trans (if_neg hθ).symm

theorem fenchel_candidate_pointwise_bound (F : ℝ → EReal)
    (hc : fullFenchelConjugate F = intrinsicConjugateTarget)
    {θ : ℝ} (hθ : θ < 1) (t : ℝ) :
    ((θ * t : ℝ) : EReal) - F t ≤ (-Real.log (1 - θ) : ℝ) := by
  have hh := le_iSup (fun t : ℝ => ((θ * t : ℝ) : EReal) - F t) t
  change ((θ * t : ℝ) : EReal) - F t ≤ fullFenchelConjugate F θ at hh
  simpa only [hc, intrinsicConjugateTarget, if_pos hθ] using hh

theorem fenchel_candidate_ne_bot (F : ℝ → EReal)
    (hc : fullFenchelConjugate F = intrinsicConjugateTarget) (t : ℝ) : F t ≠ ⊥ := by
  intro h
  have hh := fenchel_candidate_pointwise_bound F hc (show (0 : ℝ) < 1 by norm_num) t
  simp [h] at hh

theorem fenchel_candidate_real_bound (F : ℝ → EReal)
    (hc : fullFenchelConjugate F = intrinsicConjugateTarget)
    {t r θ : ℝ} (hθ : θ < 1) (hr : F t = (r : EReal)) :
    θ * t - r ≤ -Real.log (1 - θ) := by
  have hh := fenchel_candidate_pointwise_bound F hc hθ t
  simpa only [hr, ← EReal.coe_sub, EReal.coe_le_coe_iff] using hh

theorem fenchel_candidate_off_positive (F : ℝ → EReal)
    (hc : fullFenchelConjugate F = intrinsicConjugateTarget)
    {t : ℝ} (ht : t ≤ 0) : F t = ⊤ := by
  by_contra htop
  have hb := fenchel_candidate_ne_bot F hc t
  set r := (F t).toReal
  have hr : F t = (r : EReal) := (EReal.coe_toReal htop hb).symm
  have he : 1 < Real.exp (|r| + 1) := by
    rw [← Real.exp_zero, Real.exp_lt_exp]
    positivity
  have hh := fenchel_candidate_real_bound F hc
    (show 1 - Real.exp (|r| + 1) < 1 by linarith [Real.exp_pos (|r| + 1)]) hr
  rw [show 1 - (1 - Real.exp (|r| + 1)) = Real.exp (|r| + 1) by ring, Real.log_exp] at hh
  have hp : 0 ≤ (1 - Real.exp (|r| + 1)) * t := mul_nonneg_of_nonpos_of_nonpos (by linarith) ht
  linarith [le_abs_self r]

theorem fenchel_candidate_lower_bound (F : ℝ → EReal)
    (hc : fullFenchelConjugate F = intrinsicConjugateTarget) : extendedIntrinsic ≤ F := by
  intro t
  by_cases ht : 0 < t
  · by_cases htop : F t = ⊤
    · simp [htop]
    · have hb := fenchel_candidate_ne_bot F hc t
      set r := (F t).toReal
      have hr : F t = (r : EReal) := (EReal.coe_toReal htop hb).symm
      have hp : 0 < 1 / t := one_div_pos.mpr ht
      have hh := fenchel_candidate_real_bound F hc (show 1 - 1/t < 1 by linarith) hr
      have he := (fenchel_equality_iff (show 1 - 1/t < 1 by linarith) ht).mpr
        (show t = 1 / (1 - (1 - 1/t)) by field_simp)
      rw [extendedIntrinsic, if_pos ht, hr, EReal.coe_le_coe_iff]
      linarith
  · simp [extendedIntrinsic, ht, fenchel_candidate_off_positive F hc (le_of_not_gt ht)]

theorem fenchel_candidate_approximate_optimizer (F : ℝ → EReal)
    (hc : fullFenchelConjugate F = intrinsicConjugateTarget)
    {θ ε : ℝ} (hθ : θ < 1) (hε : 0 < ε) :
    ∃ t r : ℝ, 0 < t ∧ F t = (r : EReal) ∧
      -Real.log (1 - θ) - ε < θ * t - r := by
  have hh : ((-Real.log (1 - θ) - ε : ℝ) : EReal) < fullFenchelConjugate F θ := by
    rw [hc, intrinsicConjugateTarget, if_pos hθ, EReal.coe_lt_coe_iff]
    linarith
  obtain ⟨t, ht⟩ := lt_iSup_iff.mp hh
  have htop : F t ≠ ⊤ := by
    intro he
    simp only [he, EReal.sub_top, not_lt_bot] at ht
  have hb := fenchel_candidate_ne_bot F hc t
  refine ⟨t, (F t).toReal, ?_, (EReal.coe_toReal htop hb).symm, ?_⟩
  · by_contra hn
    exact htop (fenchel_candidate_off_positive F hc (le_of_not_gt hn))
  · rw [← EReal.coe_toReal htop hb, ← EReal.coe_sub, EReal.coe_lt_coe_iff] at ht
    exact ht

end
end Sigma
