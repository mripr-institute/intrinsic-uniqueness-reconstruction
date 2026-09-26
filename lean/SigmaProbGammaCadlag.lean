import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Order.LeftRightLim

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal

/-- Extension from a countable time grid by taking the infimum strictly to the right.
The real-valued construction is used with nonnegative grid paths and a cofinal grid. -/
def gammaGridRightExtension {ι : Type*} (q : ι → ℝ≥0) (X : ι → ℝ)
    (t : ℝ≥0) : ℝ := ⨅ i : {i // t < q i}, X i

variable {ι : Type*} {q : ι → ℝ≥0} {X : ι → ℝ}

theorem gamma_grid_right_nonempty (hq : ∀ t : ℝ≥0, ∃ i, t < q i) (t : ℝ≥0) :
    Nonempty {i // t < q i} := by
  obtain ⟨i, hi⟩ := hq t
  exact ⟨⟨i, hi⟩⟩

theorem gamma_grid_right_bddBelow (hX : ∀ i, 0 ≤ X i) (t : ℝ≥0) :
    BddBelow (Set.range (fun i : {i // t < q i} => X i)) :=
  ⟨0, fun _ ⟨i, hi⟩ => hi ▸ hX i⟩

theorem gamma_grid_right_extension_nonneg (hq : ∀ t : ℝ≥0, ∃ i, t < q i)
    (hX : ∀ i, 0 ≤ X i) (t : ℝ≥0) : 0 ≤ gammaGridRightExtension q X t := by
  letI := gamma_grid_right_nonempty hq t
  exact le_ciInf fun i => hX i

theorem gamma_grid_right_extension_le (hX : ∀ i, 0 ≤ X i) {t : ℝ≥0} {i : ι}
    (hi : t < q i) : gammaGridRightExtension q X t ≤ X i :=
  ciInf_le (gamma_grid_right_bddBelow hX t) ⟨i, hi⟩

theorem gamma_grid_right_extension_mono (hq : ∀ t : ℝ≥0, ∃ i, t < q i)
    (hX : ∀ i, 0 ≤ X i) : Monotone (gammaGridRightExtension q X) := by
  intro t u htu
  letI := gamma_grid_right_nonempty hq u
  apply le_ciInf
  intro i
  exact gamma_grid_right_extension_le hX (lt_of_le_of_lt htu i.property)

/-- The right-infimum path is genuinely right-continuous at every real time. -/
theorem gamma_grid_right_extension_continuousWithinAt
    (hq : ∀ t : ℝ≥0, ∃ i, t < q i) (hX : ∀ i, 0 ≤ X i) (t : ℝ≥0) :
    ContinuousWithinAt (gammaGridRightExtension q X) (Ici t) t := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact lt_of_lt_of_le ha (gamma_grid_right_extension_mono hq hX hu)
  · intro b hb
    letI := gamma_grid_right_nonempty hq t
    obtain ⟨v, ⟨i, rfl⟩, hi⟩ := (csInf_lt_iff (gamma_grid_right_bddBelow hX t)
      (Set.range_nonempty _)).mp hb
    filter_upwards [show ∀ᶠ u in 𝓝[Ici t] t, u < q i from
      (gt_mem_nhds i.property).filter_mono nhdsWithin_le_nhds] with u hu
    exact lt_of_le_of_lt (gamma_grid_right_extension_le hX hu) hi

theorem gamma_grid_right_extension_measurable {Ω : Type*} [MeasurableSpace Ω]
    [Countable ι] (q : ι → ℝ≥0) (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (t : ℝ≥0) : Measurable (fun ω => gammaGridRightExtension q (fun i => X i ω) t) :=
  Measurable.iInf fun i => hX i

/-- Ordered grid values at any times approaching t strictly from above converge
to the right-continuous extension. No monotonicity of the approximating sequence is needed. -/
theorem gamma_grid_right_extension_tendsto
    (hq : ∀ t : ℝ≥0, ∃ i, t < q i) (hX : ∀ i, 0 ≤ X i)
    (hmono : ∀ i j, q i ≤ q j → X i ≤ X j)
    (t : ℝ≥0) (a : ℕ → ι) (ha : ∀ n, t < q (a n))
    (ht : Tendsto (fun n => q (a n)) atTop (𝓝 t)) :
    Tendsto (fun n => X (a n)) atTop (𝓝 (gammaGridRightExtension q X t)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall fun n => lt_of_lt_of_le hb (gamma_grid_right_extension_le hX (ha n))
  · intro b hb
    letI := gamma_grid_right_nonempty hq t
    obtain ⟨v, ⟨i, rfl⟩, hi⟩ := (csInf_lt_iff (gamma_grid_right_bddBelow hX t)
      (Set.range_nonempty _)).mp hb
    filter_upwards [ht.eventually (gt_mem_nhds i.property)] with n hn
    exact lt_of_le_of_lt (hmono (a n) i hn.le) hi

end
end Sigma
