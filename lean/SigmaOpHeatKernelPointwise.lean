import SigmaOpHeatKernelAction

namespace Sigma
noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped BigOperators Topology ENNReal
set_option maxHeartbeats 6000000

theorem modified_bessel_i1_continuous : Continuous modifiedBesselI1 := by
  rw [continuous_iff_continuousAt]
  intro t
  let M := |t|+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hMmem : t ∈ Set.Ioo (-M) M := by
    dsimp [M]
    constructor <;> linarith [neg_abs_le t, le_abs_self t]
  have hsum : Summable (modifiedBesselI1Term M) :=
    modified_bessel_i1_term_summable M
  have hbound (n : ℕ) (u : ℝ) (hu : u ∈ Set.Icc (-M) M) :
      ‖modifiedBesselI1Term u n‖ ≤ modifiedBesselI1Term M n := by
    have huabs : |u| ≤ M := abs_le.mpr hu
    have hcoef : 0 < (n.factorial:ℝ)*((n+1).factorial:ℝ) := by positivity
    simp only [modifiedBesselI1Term, Real.norm_eq_abs, abs_mul, abs_div,
      abs_pow, abs_of_pos hcoef, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hu2 : |u|/2 ≤ M/2 :=
      div_le_div_of_nonneg_right huabs (by norm_num)
    gcongr
  have hcont : ContinuousOn modifiedBesselI1 (Set.Icc (-M) M) := by
    unfold modifiedBesselI1
    apply continuousOn_tsum
      (fun n => (by
        have hc : Continuous (fun u : ℝ => modifiedBesselI1Term u n) := by
          unfold modifiedBesselI1Term
          fun_prop
        exact hc.continuousOn)) hsum
    intro n u hu
    exact hbound n u hu
  exact hcont.continuousAt (Icc_mem_nhds (Set.mem_Ioo.mp hMmem).1
    (Set.mem_Ioo.mp hMmem).2)

private theorem laguerre_row_basis_term_coe_ae {τ x : ℝ}
    (hτ : 0 < τ) (hx : 0 < x) (n : ℕ) :
    ((laguerreHilbertBasis.repr (laguerreHeatKernelRow τ x hτ hx) n •
      laguerreHilbertBasis n : LaguerreWeightedHilbert) : ℝ → ℂ) =ᵐ[
      gammaProbability] fun y =>
      (((Real.exp (-τ)^n/(n+1:ℝ))*opLaguerre n x*opLaguerre n y : ℝ) : ℂ) := by
  have hs₁ := Lp.coeFn_smul
    (laguerreHilbertBasis.repr (laguerreHeatKernelRow τ x hτ hx) n)
    (laguerreHilbertBasis n)
  have hs₂ := Lp.coeFn_smul ((Real.sqrt (n+1) : ℂ)⁻¹)
    (laguerreL2Vector n)
  have hb : (laguerreHilbertBasis n : ℝ → ℂ) =ᵐ[gammaProbability]
      fun y => ((Real.sqrt (n+1) : ℂ)⁻¹) * (opLaguerre n y : ℂ) := by
    rw [laguerre_hilbert_basis_apply, normalizedLaguerreL2Vector]
    filter_upwards [hs₂, (op_laguerre_complex_mem_l2 n).coeFn_toLp] with y h₁ h₂
    change laguerreL2Vector n y = _ at h₂
    rw [h₁, Pi.smul_apply, smul_eq_mul, h₂]
  filter_upwards [hs₁, hb] with y h₁ h₂
  rw [h₁, Pi.smul_apply, smul_eq_mul, h₂,
    laguerre_heat_kernel_row_coordinate hτ hx n]
  have hn : (n+1:ℝ) ≠ 0 := by positivity
  have hroot : Real.sqrt (n+1:ℝ)^2 = n+1 := Real.sq_sqrt (by positivity)
  have hsqrt : Real.sqrt (n+1:ℝ) ≠ 0 := by positivity
  have hreal :
      (Real.exp (-τ)^n * opLaguerre n x / Real.sqrt (n+1)) *
        (Real.sqrt (n+1))⁻¹ * opLaguerre n y =
      (Real.exp (-τ)^n/(n+1:ℝ))*opLaguerre n x*opLaguerre n y := by
    field_simp [hn, hsqrt]
  convert congrArg Complex.ofReal hreal using 1
  push_cast
  ring

private theorem laguerre_row_basis_partial_coe_ae {τ x : ℝ}
    (hτ : 0 < τ) (hx : 0 < x) (N : ℕ) :
    ((∑ n ∈ Finset.range N,
      laguerreHilbertBasis.repr (laguerreHeatKernelRow τ x hτ hx) n •
        laguerreHilbertBasis n : LaguerreWeightedHilbert) : ℝ → ℂ) =ᵐ[
      gammaProbability] fun y => ∑ n ∈ Finset.range N,
        (((Real.exp (-τ)^n/(n+1:ℝ))*opLaguerre n x*opLaguerre n y : ℝ) : ℂ) := by
  induction N with
  | zero =>
      simp only [Finset.sum_range_zero]
      exact Filter.Eventually.of_forall (fun y => by simp)
  | succ N ih =>
      simp only [Finset.sum_range_succ]
      have hadd := Lp.coeFn_add
        (∑ n ∈ Finset.range N,
          laguerreHilbertBasis.repr (laguerreHeatKernelRow τ x hτ hx) n •
            laguerreHilbertBasis n)
        (laguerreHilbertBasis.repr (laguerreHeatKernelRow τ x hτ hx) N •
          laguerreHilbertBasis N)
      filter_upwards [hadd, ih, laguerre_row_basis_term_coe_ae hτ hx N]
        with y h₁ h₂ h₃
      rw [h₁, Pi.add_apply, h₂, h₃]

/-- For each positive starting point the literal Bessel formula and the
Laguerre spectral sum agree Gamma-almost everywhere in the arrival point. -/
theorem laguerre_heat_kernel_eq_spectral_ae {τ x : ℝ}
    (hτ : 0 < τ) (hx : 0 < x) :
    (fun y : ℝ => (laguerreHeatKernel τ x y : ℂ)) =ᵐ[gammaProbability]
      fun y => (∑' n : ℕ,
        (Real.exp (-τ)^n/(n+1:ℝ))*opLaguerre n x*opLaguerre n y : ℝ) := by
  let row := laguerreHeatKernelRow τ x hτ hx
  let S : ℕ → LaguerreWeightedHilbert := fun N =>
    ∑ n ∈ Finset.range N, laguerreHilbertBasis.repr row n • laguerreHilbertBasis n
  let F : ℕ → ℝ → ℂ := fun N y => ∑ n ∈ Finset.range N,
    (((Real.exp (-τ)^n/(n+1:ℝ))*opLaguerre n x*opLaguerre n y : ℝ) : ℂ)
  let G : ℝ → ℂ := fun y => (∑' n : ℕ,
    (Real.exp (-τ)^n/(n+1:ℝ))*opLaguerre n x*opLaguerre n y : ℝ)
  have hS : Tendsto S atTop (𝓝 row) :=
    (laguerreHilbertBasis.hasSum_repr row).tendsto_sum_nat
  have hmeasure := tendstoInMeasure_of_tendsto_Lp hS
  obtain ⟨ns, hns, hae⟩ := hmeasure.exists_seq_tendsto_ae
  have hrep : ∀ᵐ y : ℝ ∂gammaProbability, ∀ N : ℕ, S N y = F N y := by
    rw [ae_all_iff]
    intro N
    exact laguerre_row_basis_partial_coe_ae hτ hx N
  have hpos : ∀ᵐ y : ℝ ∂gammaProbability, 0 < y := by
    have hn : ∀ᵐ y : ℝ ∂gammaProbability, 0 ≤ y := by
      simpa only [ae_iff, not_le] using gamma_probability_negative_ray
    have hne : ∀ᵐ y : ℝ ∂gammaProbability, y ≠ 0 := by
      rw [ae_iff]
      simpa only [not_ne_iff, Set.setOf_eq_eq_singleton] using
        gamma_probability_no_atom 0
    filter_upwards [hn, hne] with y hy hyn
    exact lt_of_le_of_ne hy (Ne.symm hyn)
  filter_upwards [hae, hrep, hpos,
    laguerre_heat_kernel_row_coe_ae hτ hx] with y hy hrep hypos hK
  have hpoint : Tendsto (fun N => F N y) atTop (𝓝 (G y)) := by
    have hlim := (laguerre_heat_series_locally_uniform hτ).tendsto_at
      (show (x,y) ∈ {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2} from ⟨hx, hypos⟩)
    convert hlim.ofReal using 1
    funext N
    simp [F]
  have hpoint' : Tendsto (fun i => F (ns i) y) atTop (𝓝 (G y)) :=
    hpoint.comp hns.tendsto_atTop
  have hrewrite : (fun i => S (ns i) y) = fun i => F (ns i) y := by
    funext i
    exact hrep (ns i)
  rw [hrewrite] at hy
  exact hK.symm.trans (tendsto_nhds_unique hy hpoint')

/-- The actual heat kernel's Bessel formula equals the locally uniform
Laguerre spectral series at every positive pair of spatial points. -/
theorem laguerre_heat_kernel_eq_spectral {τ x y : ℝ}
    (hτ : 0 < τ) (hx : 0 < x) (hy : 0 < y) :
    laguerreHeatKernel τ x y =
      ∑' n : ℕ, (Real.exp (-τ)^n/(n+1:ℝ))*
        opLaguerre n x*opLaguerre n y := by
  let F : ℝ → ℂ := fun y => (laguerreHeatKernel τ x y : ℂ)
  let G : ℝ → ℂ := fun y => (∑' n : ℕ,
    (Real.exp (-τ)^n/(n+1:ℝ))*opLaguerre n x*opLaguerre n y : ℝ)
  have hclosed : ContinuousOn (fun y => laguerreHeatKernelClosed τ x y)
      (Set.Ioi (0:ℝ)) := by
    have hd : 1-Real.exp (-τ) ≠ 0 := by
      have he : Real.exp (-τ) < 1 := by rw [Real.exp_lt_one_iff]; linarith
      linarith
    have hnum : Continuous (fun y : ℝ =>
        Real.exp (-Real.exp (-τ)*(x+y)/(1-Real.exp (-τ)))) := by fun_prop
    have hden : Continuous (fun y : ℝ =>
        (1-Real.exp (-τ))*Real.sqrt (Real.exp (-τ)*x*y)) := by fun_prop
    have harg : Continuous (fun y : ℝ =>
        2*Real.sqrt (Real.exp (-τ)*x*y)/(1-Real.exp (-τ))) := by fun_prop
    have hdenNZ : ∀ y ∈ Set.Ioi (0:ℝ),
        (1-Real.exp (-τ))*Real.sqrt (Real.exp (-τ)*x*y) ≠ 0 := by
      intro y hy
      have hypos : 0 < y := hy
      have hs : 0 < Real.sqrt (Real.exp (-τ)*x*y) := by
        apply Real.sqrt_pos.mpr
        positivity
      exact mul_ne_zero hd (ne_of_gt hs)
    unfold laguerreHeatKernelClosed
    exact (hnum.continuousOn.div hden.continuousOn hdenNZ).mul
      ((modified_bessel_i1_continuous.comp harg).continuousOn)
  have hF : ContinuousOn F (Set.Ioi (0:ℝ)) := by
    apply (Complex.continuous_ofReal.continuousOn.comp hclosed
      (Set.mapsTo_univ _ _)).congr
    intro y hy
    have hypos : 0 < y := hy
    simp [F, laguerreHeatKernel, hypos]
  have hG : ContinuousOn G (Set.Ioi (0:ℝ)) := by
    have hterms : ∀ N : ℕ, Continuous (fun z : ℝ × ℝ =>
        ∑ n ∈ Finset.range N,
          (Real.exp (-τ)^n/(n+1:ℝ))*opLaguerre n z.1*opLaguerre n z.2) := by
      intro N
      apply continuous_finset_sum
      intro n hn
      have hl : Continuous (opLaguerre n) := by
        convert (opLaguerrePolynomial n).continuous using 1
        funext u
        exact (op_laguerre_polynomial_eval n u).symm
      exact (continuous_const.mul (hl.comp continuous_fst)).mul
        (hl.comp continuous_snd)
    have hproduct := (laguerre_heat_series_locally_uniform hτ).continuousOn
      (Filter.Eventually.of_forall (fun N => (hterms N).continuousOn))
    have hmap : Set.MapsTo (fun y : ℝ => (x,y)) (Set.Ioi (0:ℝ))
        {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2} := by
      intro y hy
      exact ⟨hx, hy⟩
    have hreal := hproduct.comp
      ((continuous_const.prod_mk continuous_id).continuousOn) hmap
    exact Complex.continuous_ofReal.continuousOn.comp hreal
      (Set.mapsTo_univ _ _)
  have hAC : (volume.restrict (Set.Ioi (0:ℝ)) : Measure ℝ) ≪
      gammaProbability := by
    have hpos : ∀ᵐ u : ℝ ∂(volume.restrict (Set.Ioi (0:ℝ)) : Measure ℝ),
        gammaPDF 2 1 u ≠ 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact (ENNReal.ofReal_pos.mpr
        (gammaPDFReal_pos (by norm_num) (by norm_num) hu)).ne'
    have hmeas : Measurable (gammaPDF 2 1) := by
      simpa only [gammaPDF] using (measurable_gammaPDFReal 2 1).ennreal_ofReal
    have hm := withDensity_absolutelyContinuous'
      hmeas.aemeasurable.restrict hpos
    rw [← restrict_withDensity measurableSet_Ioi] at hm
    exact hm.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have heq : F =ᵐ[(volume.restrict (Set.Ioi (0:ℝ)) : Measure ℝ)] G :=
    hAC.ae_le (laguerre_heat_kernel_eq_spectral_ae hτ hx)
  have hevery := Measure.eqOn_open_of_ae_eq heq isOpen_Ioi hF hG
  exact Complex.ofReal_injective (hevery hy)

theorem laguerre_heat_kernel_tendsto_one {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun τ : ℝ => laguerreHeatKernel τ x y) atTop (𝓝 1) := by
  have hpositive : ∀ᶠ τ : ℝ in atTop, 0 < τ := eventually_gt_atTop 0
  apply (laguerre_heat_spectral_series_tendsto_one hx hy).congr'
  filter_upwards [hpositive] with τ hτ
  exact (laguerre_heat_kernel_eq_spectral hτ hx hy).symm

/-- The Bessel expression itself, rather than only a related spectral
representative, is the sum in the paper's weighted product L². -/
theorem laguerre_heat_kernel_product_l2_eq_spectral {τ : ℝ} (hτ : 0 < τ) :
    (laguerre_heat_kernel_mem_product_l2 hτ).toLp
      (fun z : ℝ × ℝ => laguerreHeatKernel τ z.1 z.2) =
    laguerreHeatKernelSpectralSeries (Real.exp (-τ)) := by
  have hp : ∀ᵐ u : ℝ ∂gammaProbability, 0 < u := by
    have hn : ∀ᵐ u : ℝ ∂gammaProbability, 0 ≤ u := by
      simpa only [ae_iff, not_le] using gamma_probability_negative_ray
    have hne : ∀ᵐ u : ℝ ∂gammaProbability, u ≠ 0 := by
      rw [ae_iff]
      simpa only [not_ne_iff, Set.setOf_eq_eq_singleton] using
        gamma_probability_no_atom 0
    filter_upwards [hn, hne] with u hu hun
    exact lt_of_le_of_ne hu (Ne.symm hun)
  have hprod : ∀ᵐ z : ℝ × ℝ ∂gammaProbability.prod gammaProbability,
      0 < z.1 ∧ 0 < z.2 := by
    apply (Measure.ae_prod_iff_ae_ae (show MeasurableSet
      {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2} from
        (measurableSet_lt measurable_const measurable_fst).inter
          (measurableSet_lt measurable_const measurable_snd))).2
    filter_upwards [hp] with x hx
    filter_upwards [hp] with y hy
    exact ⟨hx, hy⟩
  apply Lp.ext
  filter_upwards [hprod,
    (laguerre_heat_kernel_mem_product_l2 hτ).coeFn_toLp,
    laguerre_heat_kernel_spectral_series_represents hτ] with z hz hleft hright
  rw [hleft, hright]
  exact laguerre_heat_kernel_eq_spectral hτ hz.1 hz.2

end
end Sigma
