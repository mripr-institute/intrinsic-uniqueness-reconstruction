import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! A Bochner integral of genuine L² vectors is represented by the
pointwise integral of any jointly measurable representatives. The ambient
spatial measure is a probability, as in the paper's heat kernels. -/

namespace Sigma
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

variable {X T 𝕜 : Type*} [MeasurableSpace X] [MeasurableSpace T] [RCLike 𝕜]
  {μ : Measure X} [IsProbabilityMeasure μ] {ν : Measure T} [SFinite ν]

theorem probability_l2_integral_norm_le (f : Lp 𝕜 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ ‖f‖ := by
  have hf := Memℒp.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2) (Lp.memℒp f)
  rw [← L1.norm_of_fun_eq_integral_norm hf, Integrable.toL1, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memℒp f).2.ne
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1:ℝ≥0∞) ≤ 2)
      (Lp.aestronglyMeasurable f))

omit [IsProbabilityMeasure μ] in
theorem l2_integral_norm_mul_le {E G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup G]
    (f : Lp E 2 μ) (g : Lp G 2 μ) :
    (∫ x, ‖f x‖*‖g x‖ ∂μ) ≤ ‖f‖*‖g‖ := by
  let u : Lp ℝ 2 μ := (Lp.memℒp f).norm.toLp (fun x => ‖f x‖)
  let v : Lp ℝ 2 μ := (Lp.memℒp g).norm.toLp (fun x => ‖g x‖)
  have hu : ‖u‖ = ‖f‖ := by rw [Lp.norm_toLp, eLpNorm_norm]; rfl
  have hv : ‖v‖ = ‖g‖ := by rw [Lp.norm_toLp, eLpNorm_norm]; rfl
  have he : (∫ x, ‖f x‖*‖g x‖ ∂μ) = @inner ℝ (Lp ℝ 2 μ) _ u v := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(Lp.memℒp f).norm.coeFn_toLp, (Lp.memℒp g).norm.coeFn_toLp]
      with x hx hy
    change u x = ‖f x‖ at hx
    change v x = ‖g x‖ at hy
    simp [hx, hy, RCLike.inner_apply, mul_comm]
  rw [he, ← hu, ← hv]
  exact real_inner_le_norm _ _

omit [SFinite ν] in
theorem l2_representatives_joint_integrable (v : T → Lp 𝕜 2 μ)
    (hv : Integrable v ν) (F : T → X → 𝕜)
    (hF : StronglyMeasurable (Function.uncurry F))
    (hrep : ∀ t, (v t : X → 𝕜) =ᵐ[μ] F t) :
    Integrable (Function.uncurry F) (ν.prod μ) := by
  apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun t =>
      (Memℒp.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2) (Lp.memℒp (v t))).congr (hrep t)
  · apply hv.norm.mono' hF.norm.integral_prod_right'.aestronglyMeasurable
    apply Eventually.of_forall
    intro t
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    calc
      _ = ∫ x, ‖v t x‖ ∂μ := integral_congr_ae ((hrep t).symm.fun_comp norm)
      _ ≤ _ := probability_l2_integral_norm_le (v t)

private theorem l2_setIntegral_inner (f : Lp 𝕜 2 μ) (s : Set X)
    (hs : MeasurableSet s) :
    (∫ x in s, f x ∂μ) =
      @inner 𝕜 (Lp 𝕜 2 μ) _ (indicatorConstLp 2 hs (measure_ne_top μ s) 1) f := by
  rw [L2.inner_indicatorConstLp_eq_setIntegral_inner]
  simp [RCLike.inner_apply]

/-- This proves an equality of actual representatives, rather than
assuming point evaluation is a continuous functional on L². -/
theorem l2_bochner_integral_representative (v : T → Lp 𝕜 2 μ)
    (hv : Integrable v ν) (F : T → X → 𝕜)
    (hF : StronglyMeasurable (Function.uncurry F))
    (hrep : ∀ t, (v t : X → 𝕜) =ᵐ[μ] F t) :
    ((∫ t, v t ∂ν : Lp 𝕜 2 μ) : X → 𝕜) =ᵐ[μ] fun x => ∫ t, F t x ∂ν := by
  have hi := l2_representatives_joint_integrable v hv F hF hrep
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (Memℒp.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2) (Lp.memℒp _))
    hi.integral_prod_right
  intro s hs _
  rw [l2_setIntegral_inner _ s hs]
  have he := (innerSL 𝕜 (indicatorConstLp 2 hs (measure_ne_top μ s) (1:𝕜))).integral_comp_comm hv
  change (∫ t, @inner 𝕜 (Lp 𝕜 2 μ) _
      (indicatorConstLp 2 hs (measure_ne_top μ s) 1) (v t) ∂ν) =
    @inner 𝕜 (Lp 𝕜 2 μ) _ (indicatorConstLp 2 hs (measure_ne_top μ s) 1)
      (∫ t, v t ∂ν) at he
  rw [← he]
  calc
    _ = ∫ t, ∫ x in s, F t x ∂μ ∂ν := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro t
      dsimp only
      rw [← l2_setIntegral_inner (v t) s hs]
      exact integral_congr_ae (ae_restrict_of_ae (hrep t))
    _ = _ := integral_integral_swap (by
      have hh := hi.integrableOn (s := Set.univ ×ˢ s)
      simpa only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] using hh)

omit [SFinite ν] in
theorem l2_kernel_input_joint_integrable (v : T → Lp ℝ 2 μ)
    (hv : Integrable v ν) (F : T → X → ℝ)
    (hF : StronglyMeasurable (Function.uncurry F))
    (hrep : ∀ t, (v t : X → ℝ) =ᵐ[μ] F t)
    (g : X → ℂ) (hg : Memℒp g 2 μ) (hgm : StronglyMeasurable g) :
    Integrable (fun z : T × X => (F z.1 z.2 : ℂ)*g z.2) (ν.prod μ) := by
  let G := hg.toLp g
  have hQ : StronglyMeasurable (fun z : T × X => (F z.1 z.2 : ℂ)*g z.2) :=
    (Complex.continuous_ofReal.comp_stronglyMeasurable hF).mul
      (hgm.comp_measurable measurable_snd)
  apply (integrable_prod_iff hQ.aestronglyMeasurable).mpr
  constructor
  · apply Eventually.of_forall
    intro t
    have hFt : Memℒp (F t) 2 μ := (memℒp_congr_ae (hrep t)).mp (Lp.memℒp (v t))
    have hh := memℒp_one_iff_integrable.mp (hg.smul hFt
      (by simp only [div_one, one_div, ENNReal.inv_two_add_inv_two] :
        (1:ℝ≥0∞)/1 = 1/2+1/2))
    simpa only [Pi.smul_apply, Complex.real_smul] using hh
  · apply (hv.norm.mul_const ‖G‖).mono' hQ.norm.integral_prod_right'.aestronglyMeasurable
    apply Eventually.of_forall
    intro t
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    calc
      _ = ∫ x, ‖v t x‖*‖G x‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards [hrep t, hg.coeFn_toLp] with x hx hG
        change G x = g x at hG
        rw [hx, hG, norm_mul, Complex.norm_real]
      _ ≤ _ := l2_integral_norm_mul_le (v t) G

theorem integrable_swap_first_two {Y E : Type*} [MeasurableSpace Y]
    [NormedAddCommGroup E] {ξ : Measure Y} [SFinite ξ]
    {Q : T × (X × Y) → E} (hQ : Integrable Q (ν.prod (μ.prod ξ))) :
    Integrable (fun z : X × (T × Y) => Q (z.2.1, z.1, z.2.2))
      (μ.prod (ν.prod ξ)) := by
  have h₁ := (measurePreserving_prodAssoc ν μ ξ).integrable_comp_emb
    MeasurableEquiv.prodAssoc.measurableEmbedding |>.mpr hQ
  have hp := (Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod
    (MeasurePreserving.id ξ)
  have h₂ := hp.integrable_comp h₁.aestronglyMeasurable |>.mpr h₁
  apply (measurePreserving_prodAssoc μ ν ξ).integrable_comp_emb
    MeasurableEquiv.prodAssoc.measurableEmbedding |>.mp
  exact h₂

end
end Sigma
