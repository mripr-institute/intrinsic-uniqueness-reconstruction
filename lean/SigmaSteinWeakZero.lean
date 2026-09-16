import SigmaSteinPrimitive
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- Locally integrable functions pair integrably with actual compact tests in the interval. -/
theorem stein_local_test_product_integrable (u g : ℝ → ℝ)
    (hu : LocallyIntegrableOn u (Ioi 0) volume)
    (hg : Continuous g) (hs : HasCompactSupport g) (hp : tsupport g ⊆ Ioi 0) :
    Integrable (fun t => u t * g t) := by
  have hi : Integrable ((tsupport g).indicator u) := by
    rw [integrable_indicator_iff hs.measurableSet]
    exact hu.integrableOn_compact_subset hp hs
  have hh := hi.smul_of_top_left (hg.memℒp_top_of_hasCompactSupport hs volume)
  apply hh.congr
  filter_upwards with t
  by_cases ht : t ∈ tsupport g
  · simp [ht, smul_eq_mul]
  · simp [ht, image_eq_zero_of_nmem_tsupport ht, smul_eq_mul]

theorem stein_positive_normalized_test_exists :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ioi 0 ∧ (∫ t : ℝ, ψ t) = 1 := by
  let b : ContDiffBump (1 : ℝ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
  refine ⟨b.normed volume,b.contDiff_normed,b.hasCompactSupport_normed,?_,b.integral_normed⟩
  rw [b.tsupport_normed_eq]
  intro t ht
  have hh := Metric.mem_closedBall.mp ht
  rw [Real.dist_eq] at hh
  have hn := (abs_le.mp hh).1
  change 0 < t
  dsimp [b] at hn
  linarith

/-- The missing distribution lemma is proved from a compact primitive and native
smooth-test separation, under only local integrability and the genuine weak equation. -/
theorem stein_zero_weak_derivative_constant (u : ℝ → ℝ)
    (hu : LocallyIntegrableOn u (Ioi 0) volume)
    (hw : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ Ioi 0 →
      (∫ t : ℝ, u t * deriv f t) = 0) :
    ∃ C : ℝ, ∀ᵐ t : ℝ, t ∈ Ioi 0 → u t = C := by
  obtain ⟨ψ,hψc,hψs,hψp,hψi⟩ := stein_positive_normalized_test_exists
  let C := ∫ t : ℝ, u t * ψ t
  have huψ := stein_local_test_product_integrable u ψ hu hψc.continuous hψs hψp
  have htest : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ioi 0 →
      (∫ t : ℝ, u t * g t) = C * (∫ t : ℝ, g t) := by
    intro g hgc hgs hgp
    let k : ℝ → ℝ := fun t => g t - (∫ s : ℝ, g s) * ψ t
    have hkc : ContDiff ℝ ∞ k := hgc.sub (contDiff_const.mul hψc)
    have hkeq : k = fun t => g t + (-(∫ s : ℝ, g s)) * ψ t := by funext t; dsimp [k]; ring
    have hks : HasCompactSupport k := by
      rw [hkeq]
      exact hgs.add hψs.mul_left
    have hkp : tsupport k ⊆ Ioi 0 := by
      rw [hkeq]
      exact tsupport_add.trans (union_subset hgp (tsupport_mul_subset_right.trans hψp))
    have hki : (∫ t : ℝ, k t) = 0 := by
      rw [show k = fun t => g t - (∫ s : ℝ, g s) * ψ t by rfl,
        integral_sub (hgc.continuous.integrable_of_hasCompactSupport hgs)
          ((hψc.continuous.integrable_of_hasCompactSupport hψs).const_mul _),
        integral_mul_left, hψi]
      ring
    obtain ⟨f,hfc,hfs,hfp,hfd⟩ := stein_compact_primitive_positive k hkc hks hkp hki
    have hh := hw f hfc hfs hfp
    have hk : (fun t => u t * deriv f t) =
        (fun t => u t * g t - (∫ s : ℝ, g s) * (u t * ψ t)) := by
      funext t
      rw [hfd]
      dsimp [k]
      ring
    rw [hk, integral_sub (stein_local_test_product_integrable u g hu hgc.continuous hgs hgp)
      (huψ.const_mul _), integral_mul_left] at hh
    dsimp [C]
    linarith
  refine ⟨C, ?_⟩
  have hlocal : LocallyIntegrableOn (fun t => u t-C) (Ioi 0) volume :=
    hu.sub (continuous_const.continuousOn.locallyIntegrableOn measurableSet_Ioi)
  have hz : ∀ᵐ t : ℝ, t ∈ Ioi 0 → u t-C=0 := by
    apply isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal
    intro g hgc hgs hgp
    have he : (fun t => g t • (u t-C)) = (fun t => u t*g t-C*g t) := by
      funext t
      simp only [smul_eq_mul]
      ring
    rw [he, integral_sub (stein_local_test_product_integrable u g hu hgc.continuous hgs hgp)
      ((hgc.continuous.integrable_of_hasCompactSupport hgs).const_mul C), integral_mul_left,
      htest g hgc hgs hgp, sub_self]
  filter_upwards [hz] with t ht
  intro hp
  exact sub_eq_zero.mp (ht hp)

end
end Sigma
