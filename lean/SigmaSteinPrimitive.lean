import SigmaStein

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- A genuine smooth compact primitive of every zero-integral test on the positive ray. -/
theorem stein_compact_primitive_positive
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0) (hz : (∫ t : ℝ, g t) = 0) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioi 0 ∧
      ∀ t : ℝ, deriv f t = g t := by
  by_cases hne : (tsupport g).Nonempty
  · obtain ⟨m,hm,hmin⟩ := hs.exists_isMinOn hne continuous_id.continuousOn
    obtain ⟨M,hM,hmax⟩ := hs.exists_isMaxOn hne continuous_id.continuousOn
    have hm0 : 0 < m := hp hm
    let a := m/2
    let b := M+1
    have ha : 0 < a := by dsimp [a]; linarith
    have hmM : m ≤ M := hmin hM
    have hab : a < b := by dsimp [a,b]; linarith
    have hbounds : ∀ t ∈ tsupport g, a < t ∧ t < b := by
      intro t ht
      have hmt : m ≤ t := hmin ht
      have htM : t ≤ M := hmax ht
      dsimp [a,b]
      constructor <;> linarith
    let f : ℝ → ℝ := fun t => ∫ u : ℝ in a..t, g u
    have hder (t : ℝ) : HasDerivAt f (g t) t :=
      intervalIntegral.integral_hasDerivAt_right (hg.continuous.intervalIntegrable a t)
        hg.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuous.continuousAt
    have hd : deriv f = g := funext fun t => (hder t).deriv
    have hfc : ContDiff ℝ ∞ f := contDiff_infty_iff_deriv.mpr
      ⟨fun t => (hder t).differentiableAt, by rw [hd]; exact hg⟩
    have hleft (t : ℝ) (ht : t ≤ a) : f t = 0 := by
      dsimp [f]
      rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le ht]
      have hh : (∫ u : ℝ in Ioc t a, g u) = 0 := by
        apply setIntegral_eq_zero_of_forall_eq_zero
        intro u hu
        by_contra hgu
        have hb := hbounds u (subset_closure (show u ∈ Function.support g from hgu))
        linarith [hu.2]
      rw [hh, neg_zero]
    have hright (t : ℝ) (ht : b ≤ t) : f t = 0 := by
      dsimp [f]
      rw [intervalIntegral.integral_of_le (le_trans hab.le ht)]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero, hz]
      intro u hu
      by_contra hgu
      have hb := hbounds u (subset_closure (show u ∈ Function.support g from hgu))
      exact hu ⟨hb.1, le_trans hb.2.le ht⟩
    have hfsub : Function.support f ⊆ Icc a b := by
      intro t ht
      constructor
      · by_contra hn
        exact ht (hleft t (le_of_not_ge hn))
      · by_contra hn
        exact ht (hright t (le_of_not_ge hn))
    have hts : tsupport f ⊆ Icc a b := closure_minimal hfsub isClosed_Icc
    refine ⟨f,hfc,HasCompactSupport.of_support_subset_isCompact isCompact_Icc hfsub,?_,fun t => congrFun hd t⟩
    intro t ht
    have hh := (hts ht).1
    exact lt_of_lt_of_le ha hh
  · have hgz : g = 0 := by
      funext t
      by_contra ht
      exact hne ⟨t,subset_closure (show t ∈ Function.support g from ht)⟩
    refine ⟨0,contDiff_const,HasCompactSupport.zero,?_,?_⟩
    · change tsupport (fun _ : ℝ => (0 : ℝ)) ⊆ Ioi 0
      have he : tsupport (fun _ : ℝ => (0 : ℝ)) = ∅ := tsupport_eq_empty_iff.mpr rfl
      rw [he]
      exact empty_subset _
    · intro t
      rw [hgz]
      exact (hasDerivAt_const t (0 : ℝ)).deriv

end
end Sigma
