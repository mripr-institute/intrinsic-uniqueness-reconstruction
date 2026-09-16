import SigmaProbFourier
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

abbrev ProbabilityCircle := AddCircle (1 : ℝ)
local instance probabilityCircleFact : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

theorem circle_continuous_integrable (μ : Measure ProbabilityCircle) [IsFiniteMeasure μ]
    (f : C(ProbabilityCircle, ℂ)) : Integrable f μ :=
  (BoundedContinuousFunction.mkOfCompact f).integrable μ

def circleIntegral (μ : Measure ProbabilityCircle) [IsFiniteMeasure μ] :
    C(ProbabilityCircle, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := by
        intro f g
        exact integral_add (circle_continuous_integrable μ f) (circle_continuous_integrable μ g)
      map_smul' := by
        intro c f
        simp only [ContinuousMap.smul_apply, RingHom.id_apply, smul_eq_mul, integral_mul_left] }
    (μ univ).toReal
    (by intro f
        simpa only [mul_comm] using norm_integral_le_of_norm_le_const (μ := μ)
          (Eventually.of_forall f.norm_coe_le_norm))

theorem circle_fourier_identifies_continuous_integrals
    (μ ν : Measure ProbabilityCircle) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : ∀ n : ℤ, (∫ x, fourier n x ∂μ) = ∫ x, fourier n x ∂ν)
    (f : C(ProbabilityCircle, ℂ)) : (∫ x, f x ∂μ) = ∫ x, f x ∂ν := by
  have hc : IsClosed {g : C(ProbabilityCircle, ℂ) | circleIntegral μ g = circleIntegral ν g} :=
    isClosed_eq (circleIntegral μ).continuous (circleIntegral ν).continuous
  have hsub : (Submodule.span ℂ (range (@fourier (1 : ℝ))) : Set C(ProbabilityCircle, ℂ)) ⊆
      {g | circleIntegral μ g = circleIntegral ν g} := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
        rcases hg with ⟨n,rfl⟩
        exact hm n
    | zero => simp
    | add f g hf hg hfe hge =>
        change circleIntegral μ f = circleIntegral ν f at hfe
        change circleIntegral μ g = circleIntegral ν g at hge
        change circleIntegral μ (f+g) = circleIntegral ν (f+g)
        rw [map_add, map_add, hfe, hge]
    | smul c f hf hfe =>
        change circleIntegral μ f = circleIntegral ν f at hfe
        change circleIntegral μ (c • f) = circleIntegral ν (c • f)
        rw [_root_.map_smul, _root_.map_smul, hfe]
  have hmem : f ∈ (Submodule.span ℂ (range (@fourier (1 : ℝ)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  exact (closure_minimal hsub hc) hmem

theorem circle_fourier_measure_unique
    (μ ν : Measure ProbabilityCircle) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : ∀ n : ℤ, (∫ x, fourier n x ∂μ) = ∫ x, fourier n x ∂ν) : μ = ν := by
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro f
  apply (ENNReal.toReal_eq_toReal
    (ne_of_lt (f.lintegral_lt_top_of_nnreal μ))
    (ne_of_lt (f.lintegral_lt_top_of_nnreal ν))).mp
  rw [f.toReal_lintegral_coe_eq_integral μ, f.toReal_lintegral_coe_eq_integral ν]
  have he := circle_fourier_identifies_continuous_integrals μ ν hm
    ⟨fun x => ((f x : ℝ) : ℂ), Complex.continuous_ofReal.comp
      (NNReal.continuous_coe.comp f.continuous)⟩
  simp only [ContinuousMap.coe_mk] at he
  have hi (ρ : Measure ProbabilityCircle) :
      (∫ x : ProbabilityCircle, ((f x : ℝ) : ℂ) ∂ρ) =
        Complex.ofReal (∫ x : ProbabilityCircle, (f x : ℝ) ∂ρ) :=
    (@RCLike.ofRealLI ℂ _).integral_comp_comm (fun x : ProbabilityCircle => (f x : ℝ))
  rw [hi μ, hi ν] at he
  exact Complex.ofReal_injective he

def scaledCircleProjection (R x : ℝ) : ProbabilityCircle := ((x/R : ℝ) : ProbabilityCircle)

def scaledCircleDecode (R : ℝ) (x : ProbabilityCircle) : ℝ :=
  R * ((AddCircle.measurableEquivIoc (1 : ℝ) (-1/2) x :
    Ioc (-1/2 : ℝ) (-1/2+1)) : ℝ)

theorem scaled_circle_projection_measurable (R : ℝ) : Measurable (scaledCircleProjection R) :=
  AddCircle.measurable_mk'.comp (measurable_id.div_const R)

theorem scaled_circle_decode_measurable (R : ℝ) : Measurable (scaledCircleDecode R) :=
  measurable_const.mul (measurable_subtype_coe.comp
    (AddCircle.measurableEquivIoc (1 : ℝ) (-1/2)).measurable)

theorem scaled_circle_decode_projection (R x : ℝ) (hR : 0 < R)
    (hx0 : -R/2 < x) (hx1 : x ≤ R/2) :
    scaledCircleDecode R (scaledCircleProjection R x) = x := by
  have hx : x/R ∈ Ioc (-1/2 : ℝ) (-1/2+1) := by
    constructor
    · apply (lt_div_iff₀ hR).mpr
      linarith
    · apply (div_le_iff₀ hR).mpr
      linarith
  change R * AddCircle.liftIoc (1 : ℝ) (-1/2) id ((x/R : ℝ) : ProbabilityCircle) = x
  rw [AddCircle.liftIoc_coe_apply hx]
  dsimp only [id]
  field_simp

theorem scaled_circle_decode_eventually (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, scaledCircleDecode ((n : ℝ)+1)
      (scaledCircleProjection ((n : ℝ)+1) x) = x := by
  have hn : ∀ᶠ n : ℕ in atTop, 2*|x| < (n : ℝ)+1 :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1 : ℝ)))).eventually
      (eventually_gt_atTop (2*|x|))
  filter_upwards [hn] with n hn
  apply scaled_circle_decode_projection _ _ (by positivity)
  · linarith [neg_abs_le x]
  · linarith [le_abs_self x]

theorem characteristic_equality_circle_projections (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ x, probabilityCharacteristic μ x = probabilityCharacteristic ν x) (R : ℝ) :
    Measure.map (scaledCircleProjection R) μ = Measure.map (scaledCircleProjection R) ν := by
  apply circle_fourier_measure_unique
  intro n
  rw [integral_map (scaled_circle_projection_measurable R).aemeasurable
      (fourier n).continuous.measurable.aestronglyMeasurable,
    integral_map (scaled_circle_projection_measurable R).aemeasurable
      (fourier n).continuous.measurable.aestronglyMeasurable]
  have he (ρ : Measure ℝ) :
      (∫ x : ℝ, fourier n (scaledCircleProjection R x) ∂ρ) =
        probabilityCharacteristic ρ (2*Real.pi*(n : ℝ)/R) := by
    apply integral_congr_ae
    filter_upwards with x
    unfold scaledCircleProjection
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [he, he, h]

theorem decoded_circle_integral_limit (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, f (scaledCircleDecode ((n : ℝ)+1)
      (scaledCircleProjection ((n : ℝ)+1) x)) ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => C)
  · intro n
    exact (hf.comp ((scaled_circle_decode_measurable _).comp
      (scaled_circle_projection_measurable _))).aestronglyMeasurable
  · exact integrable_const C
  · intro n
    exact Eventually.of_forall fun x => hb _
  · apply Eventually.of_forall
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [scaled_circle_decode_eventually x] with n hn
    rw [hn]

theorem characteristic_equality_bounded_integrals (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ x, probabilityCharacteristic μ x = probabilityCharacteristic ν x)
    (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, f x ∂μ) = ∫ x, f x ∂ν := by
  have hn : ∀ n : ℕ, (∫ x : ℝ, f (scaledCircleDecode ((n : ℝ)+1)
      (scaledCircleProjection ((n : ℝ)+1) x)) ∂μ) =
      ∫ x : ℝ, f (scaledCircleDecode ((n : ℝ)+1)
        (scaledCircleProjection ((n : ℝ)+1) x)) ∂ν := by
    intro n
    have he := congrArg (fun ρ : Measure ProbabilityCircle =>
      ∫ y, f (scaledCircleDecode ((n : ℝ)+1) y) ∂ρ)
      (characteristic_equality_circle_projections μ ν h ((n : ℝ)+1))
    dsimp only at he
    have hmeas : Measurable (fun y : ProbabilityCircle => f (scaledCircleDecode ((n : ℝ)+1) y)) :=
      hf.comp (scaled_circle_decode_measurable _)
    rw [integral_map (scaled_circle_projection_measurable _).aemeasurable
        hmeas.aestronglyMeasurable,
      integral_map (scaled_circle_projection_measurable _).aemeasurable
        hmeas.aestronglyMeasurable] at he
    exact he
  exact tendsto_nhds_unique (decoded_circle_integral_limit μ f hf C hb)
    ((decoded_circle_integral_limit ν f hf C hb).congr' (Eventually.of_forall fun n => (hn n).symm))

/-- Native finite-Borel-measure uniqueness on the entire real line from actual
characteristic integrals. Compact Fourier density and expanding periods replace
any unproved inversion or probability-uniqueness premise. -/
theorem finite_measure_characteristic_unique (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ x, probabilityCharacteristic μ x = probabilityCharacteristic ν x) : μ = ν := by
  classical
  ext s hs
  apply (ENNReal.toReal_eq_toReal (measure_ne_top μ s) (measure_ne_top ν s)).mp
  have he := characteristic_equality_bounded_integrals μ ν h
    (s.indicator (fun _ : ℝ => (1 : ℝ))) (measurable_const.indicator hs) 1
    (by intro x; by_cases hx : x ∈ s <;> simp [hx])
  simpa [integral_indicator hs] using he

end
end Sigma
