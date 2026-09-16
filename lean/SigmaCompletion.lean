import SigmaCore
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.MonotoneContinuity

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology

def completionEll (h : ℝ → ℝ) (z : ℝ) : ℝ := z + h z

def TypedCompletion (h : ℝ → ℝ) : Prop :=
  ∀ z > -1, completionEll h (deriv h z) = -completionEll h z

theorem completionEll_hasDerivAt (h : ℝ → ℝ) {z : ℝ}
    (hd : DifferentiableAt ℝ h z) :
    HasDerivAt (completionEll h) (1 + deriv h z) z :=
  (hasDerivAt_id z).add hd.hasDerivAt

theorem completionEll_strictMono (h : ℝ → ℝ)
    (hd : ∀ z > -1, DifferentiableAt ℝ h z)
    (hr : ∀ z > -1, -1 < deriv h z) : StrictMonoOn (completionEll h) (Ioi (-1)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi (-1 : ℝ))
    (fun z hz => (completionEll_hasDerivAt h (hd z hz)).continuousAt.continuousWithinAt)
  intro z hz
  have hz' : -1 < z := by simpa only [interior_Ioi] using hz
  rw [(completionEll_hasDerivAt h (hd z hz')).deriv]
  linarith [hr z hz']

theorem completion_derivative_involutive (h : ℝ → ℝ)
    (hd : ∀ z > -1, DifferentiableAt ℝ h z)
    (hr : ∀ z > -1, -1 < deriv h z) (he : TypedCompletion h) :
    ∀ z > -1, deriv h (deriv h z) = z := by
  intro z hz
  apply (completionEll_strictMono h hd hr).injOn (hr _ (hr z hz)) hz
  rw [he _ (hr z hz), he z hz, neg_neg]

theorem completion_derivative_strictAnti (h : ℝ → ℝ)
    (hd : ∀ z > -1, DifferentiableAt ℝ h z)
    (hr : ∀ z > -1, -1 < deriv h z) (he : TypedCompletion h) :
    StrictAntiOn (deriv h) (Ioi (-1)) := by
  intro x hx y hy hxy
  have hm := completionEll_strictMono h hd hr
  apply (hm.lt_iff_lt (hr y hy) (hr x hx)).mp
  rw [he y hy, he x hx]
  exact neg_lt_neg (hm hx hy hxy)

theorem completion_neg_derivative_image (h : ℝ → ℝ)
    (hd : ∀ z > -1, DifferentiableAt ℝ h z)
    (hr : ∀ z > -1, -1 < deriv h z) (he : TypedCompletion h) :
    (fun z => -deriv h z) '' Ioi (-1) = Iio (1 : ℝ) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hh := hr z hz
    change -deriv h z < 1
    linarith
  · intro hy
    have hy' : -1 < -y := by change y < 1 at hy; linarith
    refine ⟨deriv h (-y), hr _ hy', ?_⟩
    dsimp only
    rw [completion_derivative_involutive h hd hr he (-y) hy', neg_neg]

theorem completion_derivative_continuousAt (h : ℝ → ℝ)
    (hd : ∀ z > -1, DifferentiableAt ℝ h z)
    (hr : ∀ z > -1, -1 < deriv h z) (he : TypedCompletion h)
    {z : ℝ} (hz : -1 < z) : ContinuousAt (deriv h) z := by
  have hm : StrictMonoOn (fun x => -deriv h x) (Ioi (-1)) := by
    intro x hx y hy hxy
    exact neg_lt_neg (completion_derivative_strictAnti h hd hr he hx hy hxy)
  have hc : ContinuousAt (fun x => -deriv h x) z := by
    apply hm.continuousAt_of_image_mem_nhds (isOpen_Ioi.mem_nhds hz)
    rw [completion_neg_derivative_image h hd hr he]
    apply isOpen_Iio.mem_nhds
    change -deriv h z < 1
    linarith [hr z hz]
  simpa only [neg_neg] using hc.neg

/-- The actual second derivative is derived by quotient limits of the
completion equation. No differentiability of h' is assumed. -/
theorem completion_second_hasDerivAt (h : ℝ → ℝ)
    (hd : ∀ z > -1, DifferentiableAt ℝ h z)
    (hr : ∀ z > -1, -1 < deriv h z) (he : TypedCompletion h)
    {z : ℝ} (hz : -1 < z) :
    HasDerivAt (deriv h) (-(1 + deriv h z) / (1 + z)) z := by
  have hi := completion_derivative_involutive h hd hr he
  have hm := completionEll_strictMono h hd hr
  have hqi := (completion_derivative_strictAnti h hd hr he).injOn
  have hqc := completion_derivative_continuousAt h hd hr he hz
  have hqt : Tendsto (deriv h) (𝓝[≠] z) (𝓝[≠] deriv h z) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hqc.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hz)] with y hy hyD
    change y ≠ z at hy
    change deriv h y ≠ deriv h z
    exact fun hh => hy (hqi hyD hz hh)
  have hnum := hasDerivAt_iff_tendsto_slope.mp
    (completionEll_hasDerivAt h (hd z hz)).neg
  have hden0 := hasDerivAt_iff_tendsto_slope.mp
    (completionEll_hasDerivAt h (hd _ (hr z hz)))
  rw [hi z hz] at hden0
  have hden := hden0.comp hqt
  have htend := hnum.div hden (show 1 + z ≠ 0 by linarith)
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply htend.congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hz)] with y hy hyD
  change y ≠ z at hy
  have hqne : deriv h y ≠ deriv h z := fun hh => hy (hqi hyD hz hh)
  have hene : completionEll h (deriv h y) ≠ completionEll h (deriv h z) :=
    fun hh => hqne (hm.injOn (hr y hyD) (hr z hz) hh)
  have hdif : completionEll h (deriv h y) - completionEll h (deriv h z) ≠ 0 :=
    sub_ne_zero.mpr hene
  simp only [Pi.div_apply, Function.comp_def, slope_def_field]
  rw [← he y hyD, ← he z hz]
  field_simp [hdif, sub_ne_zero.mpr hy, sub_ne_zero.mpr hqne]
  <;> ring

end
end Sigma
