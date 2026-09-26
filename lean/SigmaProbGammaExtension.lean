import SigmaProbGammaCadlag
import SigmaProbGammaLimits

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

variable {ι Ω : Type*} [MeasurableSpace Ω]

/-- Concrete grid data sufficient for extension. These are properties of actual
random variables on one probability space, not a presumed global process. -/
structure GammaGridRealization (P : Measure Ω) (q : ι → ℝ≥0) (X : ι → Ω → ℝ) : Prop where
  cofinal : ∀ t : ℝ≥0, ∃ i, t < q i
  measurable : ∀ i, Measurable (X i)
  paths : ∀ᵐ ω ∂P, (∀ i, 0 ≤ X i ω) ∧ (∀ i j, q i ≤ q j → X i ω ≤ X j ω)
  marginal : ∀ i, P.map (X i) = gammaCompletion (q i)
  increment : ∀ i j, q i ≤ q j →
    P.map (fun ω => X j ω-X i ω) = gammaCompletion (q j-q i)
  independent : ∀ (n : ℕ) (a : ℕ → ι), Monotone (fun k => q (a k)) →
    iIndepFun (fun _ : Fin n => inferInstance)
      (fun i : Fin n => fun ω => X (a (i.val+1)) ω-X (a i.val) ω) P

/-- Strict upper approximations which preserve the order of observation times. -/
structure GammaGridUpperApproximation (q : ι → ℝ≥0) where
  index : ℝ≥0 → ℕ → ι
  above : ∀ t n, t < q (index t n)
  tendsto : ∀ t, Tendsto (fun n => q (index t n)) atTop (𝓝 t)
  monotone : ∀ n, Monotone (fun t => q (index t n))

def gammaGridProcess (q : ι → ℝ≥0) (X : ι → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  gammaGridRightExtension q (fun i => X i ω) t

variable [Countable ι] (P : Measure Ω) [IsProbabilityMeasure P]
variable {q : ι → ℝ≥0} {X : ι → Ω → ℝ}
variable (h : GammaGridRealization P q X) (a : GammaGridUpperApproximation q)
include h

theorem gamma_grid_process_measurable (t : ℝ≥0) : Measurable (gammaGridProcess q X t) :=
  gamma_grid_right_extension_measurable q X h.measurable t

include a in
theorem gamma_grid_process_approx_tendsto (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Tendsto (fun n => X (a.index t n) ω) atTop (𝓝 (gammaGridProcess q X t ω)) := by
  filter_upwards [h.paths] with ω hω
  exact gamma_grid_right_extension_tendsto h.cofinal hω.1 hω.2 t (a.index t)
    (a.above t) (a.tendsto t)

include a in
theorem gamma_grid_process_marginal (t : ℝ≥0) :
    P.map (gammaGridProcess q X t) = gammaCompletion t :=
  gamma_law_of_ae_tendsto P (fun n => X (a.index t n)) (gammaGridProcess q X t)
    (fun n => h.measurable _) (gamma_grid_process_measurable P h t)
    (gamma_grid_process_approx_tendsto P h a t) _ t (a.tendsto t)
    (fun n => h.marginal _)

include a in
theorem gamma_grid_process_increment (s t : ℝ≥0) (hst : s ≤ t) :
    P.map (fun ω => gammaGridProcess q X t ω-gammaGridProcess q X s ω) =
      gammaCompletion (t-s) := by
  refine gamma_law_of_ae_tendsto P
    (fun n ω => X (a.index t n) ω-X (a.index s n) ω) _
    (fun n => (h.measurable _).sub (h.measurable _))
    ((gamma_grid_process_measurable P h t).sub (gamma_grid_process_measurable P h s))
    ?_ (fun n => q (a.index t n)-q (a.index s n)) (t-s)
    ((a.tendsto t).sub (a.tendsto s)) ?_
  · filter_upwards [gamma_grid_process_approx_tendsto P h a t,
      gamma_grid_process_approx_tendsto P h a s] with ω ht hs
    exact ht.sub hs
  · intro n
    exact h.increment _ _ (a.monotone n hst)

include a in
theorem gamma_grid_process_independent :
    HasIndependentNonnegativeTimeIncrements P (gammaGridProcess q X) := by
  intro n t ht ht0
  apply independent_finite_of_ae_tendsto P
    (fun k (i : Fin n) ω => X (a.index (t (i.val+1)) k) ω-X (a.index (t i.val) k) ω)
    (fun i ω => gammaGridProcess q X (t (i.val+1)) ω-gammaGridProcess q X (t i.val) ω)
    (fun k i => (h.measurable _).sub (h.measurable _))
    (fun i => (gamma_grid_process_measurable P h _).sub (gamma_grid_process_measurable P h _))
  · intro k
    exact h.independent n (fun j => a.index (t j) k) ((a.monotone k).comp ht)
  · intro i
    filter_upwards [gamma_grid_process_approx_tendsto P h a (t (i.val+1)),
      gamma_grid_process_approx_tendsto P h a (t i.val)] with ω hh hl
    exact hh.sub hl

theorem gamma_grid_process_paths :
    ∀ᵐ ω ∂P, (∀ t, 0 ≤ gammaGridProcess q X t ω) ∧
      Monotone (fun t => gammaGridProcess q X t ω) ∧
      (∀ t, ContinuousWithinAt (fun s => gammaGridProcess q X s ω) (Ici t) t) := by
  filter_upwards [h.paths] with ω hω
  exact ⟨gamma_grid_right_extension_nonneg h.cofinal hω.1,
    gamma_grid_right_extension_mono h.cofinal hω.1,
    gamma_grid_right_extension_continuousWithinAt h.cofinal hω.1⟩

include a in
/-- An actual global Gamma process, obtained by extending the supplied actual
grid variables. Starting at zero is derived from the zero-time marginal. -/
theorem gamma_grid_process_category : IsGammaTimeOneProcess P (gammaGridProcess q X) := by
  have hz : ∀ᵐ ω ∂P, gammaGridProcess q X 0 ω = 0 := by
    apply (ae_map_iff (gamma_grid_process_measurable P h 0).aemeasurable
      (measurableSet_singleton 0)).mp
    rw [gamma_grid_process_marginal P h a 0, gamma_completion_zero]
    simp <;> rfl
  refine ⟨gamma_grid_process_measurable P h, hz, ?_,
    gamma_grid_process_independent P h a, ?_, ?_⟩
  · intro t
    exact (gamma_grid_process_paths P h).mono fun ω hω => hω.1 t
  · intro r s
    rw [gamma_grid_process_increment P h a r (r+s) (le_add_right le_rfl),
      add_tsub_cancel_left, gamma_grid_process_marginal P h a s]
  · rw [gamma_grid_process_marginal P h a 1, gamma_completion_one]

end
end Sigma
