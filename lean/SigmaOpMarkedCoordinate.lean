import SigmaOpHeatMarkov
import SigmaOpGammaShapeThreeNativeBoundary
import Mathlib.MeasureTheory.Function.L2Space

namespace Sigma
noncomputable section
open MeasureTheory Set
open scoped ENNReal

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

private def coordinateIndicatorMem (E : Set ℝ) (hE : MeasurableSet E)
    (f : Lp ℂ 2 μ) : Memℒp (E.indicator (f : ℝ → ℂ)) 2
      μ :=
  (Lp.memℒp f).indicator hE

/-- The actual bounded Borel projection on a native weighted L² Hilbert space. -/
def coordinateIndicatorLinear (E : Set ℝ) (hE : MeasurableSet E) :
    Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (coordinateIndicatorMem μ E hE f).toLp (E.indicator (f : ℝ → ℂ))
  map_add' f g := by
    apply Lp.ext
    filter_upwards [
      (coordinateIndicatorMem μ E hE (f + g)).coeFn_toLp,
      (coordinateIndicatorMem μ E hE f).coeFn_toLp,
      (coordinateIndicatorMem μ E hE g).coeFn_toLp,
      Lp.coeFn_add f g,
      Lp.coeFn_add
        ((coordinateIndicatorMem μ E hE f).toLp (E.indicator (f : ℝ → ℂ)))
        ((coordinateIndicatorMem μ E hE g).toLp (E.indicator (g : ℝ → ℂ)))]
      with t hsum hf hg hfg hright
    rw [hsum, hright]
    simp only [Pi.add_apply]
    rw [hf, hg]
    by_cases ht : t ∈ E
    · simp only [Set.indicator_of_mem ht, hfg, Pi.add_apply]
    · simp only [Set.indicator_of_not_mem ht, add_zero]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [
      (coordinateIndicatorMem μ E hE (c • f)).coeFn_toLp,
      (coordinateIndicatorMem μ E hE f).coeFn_toLp,
      Lp.coeFn_smul c f,
      Lp.coeFn_smul c
        ((coordinateIndicatorMem μ E hE f).toLp (E.indicator (f : ℝ → ℂ)))]
      with t hleft hf hcf hright
    rw [hleft]
    simp only [RingHom.id_apply]
    rw [hright]
    simp only [Pi.smul_apply]
    rw [hf]
    by_cases ht : t ∈ E
    · simp only [Set.indicator_of_mem ht, hcf, Pi.smul_apply]
    · simp only [Set.indicator_of_not_mem ht, smul_zero]

def coordinateIndicatorOperator (E : Set ℝ) (hE : MeasurableSet E) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (coordinateIndicatorLinear μ E hE).mkContinuous 1 (by
    intro f
    change ‖(coordinateIndicatorMem μ E hE f).toLp (E.indicator (f : ℝ → ℂ))‖ ≤
      1 * ‖f‖
    rw [one_mul, Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
      (eLpNorm_indicator_le (s := E) (f : ℝ → ℂ)))


/-- The maximal weighted-L² domain of multiplication by the real coordinate. -/
def coordinateMultiplicationDomain : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | Memℒp (fun t : ℝ => (t : ℂ) * (f : ℝ → ℂ) t) 2 μ}
  zero_mem' := by
    apply (memℒp_congr_ae ?_).mpr zero_memℒp
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with t ht
    simp [ht]
  add_mem' {f g} hf hg := by
    apply (memℒp_congr_ae ?_).mpr (hf.add hg)
    filter_upwards [Lp.coeFn_add f g] with t ht
    simp only [Pi.add_apply, ht]
    ring
  smul_mem' c f hf := by
    apply (memℒp_congr_ae ?_).mpr (hf.const_mul c)
    filter_upwards [Lp.coeFn_smul c f] with t ht
    simp only [Pi.smul_apply, smul_eq_mul, ht]
    ring

/-- Literal multiplication by t on its full maximal weighted-L² domain. -/
def coordinateMultiplicationOperator :
    Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ where
  domain := coordinateMultiplicationDomain μ
  toFun :=
    { toFun := fun f => f.property.toLp
        (fun t : ℝ => (t : ℂ) * (f.val : ℝ → ℂ) t)
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [
          (f + g).property.coeFn_toLp,
          f.property.coeFn_toLp,
          g.property.coeFn_toLp,
          Lp.coeFn_add f.val g.val,
          Lp.coeFn_add
            (f.property.toLp (fun t : ℝ => (t : ℂ) * (f.val : ℝ → ℂ) t))
            (g.property.toLp (fun t : ℝ => (t : ℂ) * (g.val : ℝ → ℂ) t))]
          with t hsum hf hg hfg hright
        rw [hsum, hright]
        simp only [Pi.add_apply]
        rw [hf, hg]
        change (t : ℂ) * ((f.val + g.val : Lp ℂ 2 μ) : ℝ → ℂ) t =
          (t : ℂ) * (f.val : ℝ → ℂ) t + (t : ℂ) * (g.val : ℝ → ℂ) t
        rw [hfg]
        simp only [Pi.add_apply]
        ring
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [
          (c • f).property.coeFn_toLp,
          f.property.coeFn_toLp,
          Lp.coeFn_smul c f.val,
          Lp.coeFn_smul c
            (f.property.toLp (fun t : ℝ => (t : ℂ) * (f.val : ℝ → ℂ) t))]
          with t hleft hf hcf hright
        rw [hleft]
        simp only [RingHom.id_apply]
        rw [hright]
        simp only [Pi.smul_apply]
        rw [hf]
        change (t : ℂ) * ((c • f.val : Lp ℂ 2 μ) : ℝ → ℂ) t =
          c * ((t : ℂ) * (f.val : ℝ → ℂ) t)
        rw [hcf]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring }


/-- The literal constant-one vector in any probability-weighted L². -/
def coordinateConstantOne (μ : Measure ℝ) [IsProbabilityMeasure μ] : Lp ℂ 2 μ :=
  indicatorConstLp 2 (by measurability : MeasurableSet (Set.univ : Set ℝ))
    (measure_ne_top μ Set.univ) (1 : ℂ)

theorem coordinate_constant_one_coe (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (coordinateConstantOne μ : ℝ → ℂ) =ᵐ[μ] fun _ => (1 : ℂ) := by
  simpa only [coordinateConstantOne, Set.indicator_univ] using
    (show (indicatorConstLp 2 (by measurability : MeasurableSet (Set.univ : Set ℝ))
      (measure_ne_top μ Set.univ) (1 : ℂ) :
      ℝ → ℂ) =ᵐ[μ] Set.univ.indicator (fun _ => (1 : ℂ)) from
      indicatorConstLp_coeFn)

theorem coordinate_indicator_operator_on_constant
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (E : Set ℝ) (hE : MeasurableSet E) :
    coordinateIndicatorOperator μ E hE (coordinateConstantOne μ) =
      indicatorConstLp 2 hE (measure_ne_top μ E) (1 : ℂ) := by
  apply Lp.ext
  filter_upwards [
    (coordinateIndicatorMem μ E hE (coordinateConstantOne μ)).coeFn_toLp,
    coordinate_constant_one_coe μ,
    (show (indicatorConstLp 2 hE (measure_ne_top μ E) (1 : ℂ) : ℝ → ℂ) =ᵐ[μ]
      E.indicator (fun _ => (1 : ℂ)) from indicatorConstLp_coeFn)]
    with t hproj hone hind
  change (coordinateIndicatorMem μ E hE (coordinateConstantOne μ)).toLp
      (E.indicator (coordinateConstantOne μ : ℝ → ℂ)) t =
    indicatorConstLp 2 hE (measure_ne_top μ E) (1 : ℂ) t
  rw [hproj, hind]
  by_cases ht : t ∈ E <;> simp [ht, hone]

/-- Full marked Borel projection data recover the coordinate probability. -/
theorem coordinate_indicator_probability_general
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (E : Set ℝ) (hE : MeasurableSet E) :
    @inner ℂ (Lp ℂ 2 μ) _
      (coordinateIndicatorOperator μ E hE (coordinateConstantOne μ))
      (coordinateConstantOne μ) = ((μ E).toReal : ℂ) := by
  rw [coordinate_indicator_operator_on_constant μ E hE,
    L2.inner_indicatorConstLp_one hE (measure_ne_top μ E)]
  calc
    (∫ t : ℝ in E, (coordinateConstantOne μ : ℝ → ℂ) t ∂μ) =
        ∫ t : ℝ in E, (1 : ℂ) ∂μ := by
      apply setIntegral_congr_ae hE
      filter_upwards [coordinate_constant_one_coe μ] with t ht hmem
      exact ht
    _ = ((μ E).toReal : ℂ) := by simp

/-- Each Borel coordinate projection preserves the literal maximal domain of
coordinate multiplication. -/
theorem coordinate_indicator_preserves_multiplication_domain
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (E : Set ℝ) (hE : MeasurableSet E)
    (f : Lp ℂ 2 μ) (hf : f ∈ (coordinateMultiplicationOperator μ).domain) :
    coordinateIndicatorOperator μ E hE f ∈
      (coordinateMultiplicationOperator μ).domain := by
  change Memℒp (fun t : ℝ =>
    (t : ℂ) * (coordinateIndicatorOperator μ E hE f : ℝ → ℂ) t) 2 μ
  have hi := (show Memℒp (fun t : ℝ => (t : ℂ) * (f : ℝ → ℂ) t) 2 μ
    from hf).indicator hE
  apply (memℒp_congr_ae ?_).mpr hi
  filter_upwards [(coordinateIndicatorMem μ E hE f).coeFn_toLp] with t ht
  change (coordinateIndicatorOperator μ E hE f : ℝ → ℂ) t =
    E.indicator (f : ℝ → ℂ) t at ht
  rw [ht]
  by_cases h : t ∈ E <;> simp [h]

/-- The concrete Borel projections reduce multiplication by the coordinate,
on its exact weighted-L² domain. -/
theorem coordinate_indicator_multiplication_commute
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (E : Set ℝ) (hE : MeasurableSet E)
    (f : Lp ℂ 2 μ) (hf : f ∈ (coordinateMultiplicationOperator μ).domain) :
    coordinateIndicatorOperator μ E hE
        (coordinateMultiplicationOperator μ ⟨f, hf⟩) =
      coordinateMultiplicationOperator μ
        ⟨coordinateIndicatorOperator μ E hE f,
          coordinate_indicator_preserves_multiplication_domain μ E hE f hf⟩ := by
  apply Lp.ext
  filter_upwards [
    (coordinateIndicatorMem μ E hE
      (coordinateMultiplicationOperator μ ⟨f, hf⟩)).coeFn_toLp,
    hf.coeFn_toLp,
    (coordinate_indicator_preserves_multiplication_domain μ E hE f hf).coeFn_toLp,
    (coordinateIndicatorMem μ E hE f).coeFn_toLp]
    with t hleft hmul hright hind
  change
    ((coordinateIndicatorMem μ E hE
      (coordinateMultiplicationOperator μ ⟨f, hf⟩)).toLp
        (E.indicator (coordinateMultiplicationOperator μ ⟨f, hf⟩ : ℝ → ℂ)) :
        ℝ → ℂ) t =
    ((coordinate_indicator_preserves_multiplication_domain μ E hE f hf).toLp
        (fun t : ℝ => (t : ℂ) * (coordinateIndicatorOperator μ E hE f : ℝ → ℂ) t) :
        ℝ → ℂ) t
  change (coordinateMultiplicationOperator μ ⟨f, hf⟩ : ℝ → ℂ) t = _ at hmul
  change (coordinateIndicatorOperator μ E hE f : ℝ → ℂ) t = _ at hind
  rw [hleft, hright]
  by_cases h : t ∈ E
  · simp only [Set.indicator_of_mem h]
    rw [hmul, hind, Set.indicator_of_mem h]
  · simp only [Set.indicator_of_not_mem h]
    rw [hind, Set.indicator_of_not_mem h, mul_zero]

theorem coordinate_indicator_operator_on_one (E : Set ℝ) (hE : MeasurableSet E) :
    coordinateIndicatorOperator gammaProbability E hE (laguerreHilbertBasis 0) =
      indicatorConstLp 2 hE (measure_ne_top gammaProbability E) (1 : ℂ) := by
  apply Lp.ext
  filter_upwards [
    (coordinateIndicatorMem gammaProbability E hE (laguerreHilbertBasis 0)).coeFn_toLp,
    laguerre_basis_zero_coe,
    (show (indicatorConstLp 2 hE (measure_ne_top gammaProbability E) (1 : ℂ) :
      ℝ → ℂ) =ᵐ[gammaProbability] E.indicator (fun _ => (1 : ℂ)) from
      indicatorConstLp_coeFn)]
    with t hproj hone hind
  change (coordinateIndicatorMem gammaProbability E hE (laguerreHilbertBasis 0)).toLp
      (E.indicator (laguerreHilbertBasis 0 : ℝ → ℂ)) t =
    indicatorConstLp 2 hE (measure_ne_top gammaProbability E) (1 : ℂ) t
  rw [hproj, hind]
  by_cases ht : t ∈ E <;> simp [ht, hone]

/-- The marked Borel projection recovers the actual coordinate probability
from the retained constant vector on every measurable event. -/
theorem coordinate_indicator_probability (E : Set ℝ) (hE : MeasurableSet E) :
    @inner ℂ LaguerreWeightedHilbert _
      (coordinateIndicatorOperator gammaProbability E hE (laguerreHilbertBasis 0))
      (laguerreHilbertBasis 0) = ((gammaProbability E).toReal : ℂ) := by
  rw [coordinate_indicator_operator_on_one E hE,
    L2.inner_indicatorConstLp_one hE (measure_ne_top gammaProbability E)]
  calc
    (∫ t : ℝ in E, (laguerreHilbertBasis 0 : ℝ → ℂ) t ∂gammaProbability) =
        ∫ t : ℝ in E, (1 : ℂ) ∂gammaProbability := by
      apply setIntegral_congr_ae hE
      filter_upwards [laguerre_basis_zero_coe] with t ht hmem
      exact ht
    _ = ((gammaProbability E).toReal : ℂ) := by simp


/-- A unitary preserving the marked Borel projections and the distinguished
constant preserves the complete coordinate probability on every Borel set. -/
theorem marked_projection_unitary_preserves_probability
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hone : U (coordinateConstantOne μ) = coordinateConstantOne ν)
    (hproj : ∀ (E : Set ℝ) (hE : MeasurableSet E) (f : Lp ℂ 2 μ),
      U (coordinateIndicatorOperator μ E hE f) =
        coordinateIndicatorOperator ν E hE (U f)) : μ = ν := by
  apply Measure.ext
  intro E hE
  have hc : ((μ E).toReal : ℂ) = ((ν E).toReal : ℂ) := by
    calc
      ((μ E).toReal : ℂ) = @inner ℂ (Lp ℂ 2 μ) _
          (coordinateIndicatorOperator μ E hE (coordinateConstantOne μ))
          (coordinateConstantOne μ) :=
        (coordinate_indicator_probability_general μ E hE).symm
      _ = @inner ℂ (Lp ℂ 2 ν) _
          (U (coordinateIndicatorOperator μ E hE (coordinateConstantOne μ)))
          (U (coordinateConstantOne μ)) := (U.inner_map_map _ _).symm
      _ = @inner ℂ (Lp ℂ 2 ν) _
          (coordinateIndicatorOperator ν E hE (coordinateConstantOne ν))
          (coordinateConstantOne ν) := by rw [hproj E hE, hone]
      _ = ((ν E).toReal : ℂ) := coordinate_indicator_probability_general ν E hE
  have hr : (μ E).toReal = (ν E).toReal := Complex.ofReal_injective hc
  calc
    μ E = ENNReal.ofReal (μ E).toReal :=
      (ENNReal.ofReal_toReal (measure_ne_top μ E)).symm
    _ = ENNReal.ofReal (ν E).toReal := by rw [hr]
    _ = ν E := ENNReal.ofReal_toReal (measure_ne_top ν E)

/-- The distinguished constant is in the full multiplication domain whenever
the coordinate has a finite second moment. -/
theorem coordinate_constant_mem_multiplication_domain
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h₂ : Integrable (fun t : ℝ => t ^ 2) μ) :
    coordinateConstantOne μ ∈ (coordinateMultiplicationOperator μ).domain := by
  have ht : Memℒp (fun t : ℝ => (t : ℂ)) 2 μ := by
    apply (memℒp_two_iff_integrable_sq_norm
      (Complex.continuous_ofReal.aestronglyMeasurable)).mpr
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h₂
  change Memℒp (fun t : ℝ => (t : ℂ) * (coordinateConstantOne μ : ℝ → ℂ) t) 2 μ
  apply (memℒp_congr_ae ?_).mpr ht
  filter_upwards [coordinate_constant_one_coe μ] with t hone
  simp [hone]

/-- The first moment is the expectation of the literal coordinate mark on one. -/
theorem coordinate_multiplication_constant_expectation
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h₂ : Integrable (fun t : ℝ => t ^ 2) μ) :
    @inner ℂ (Lp ℂ 2 μ) _
      (coordinateMultiplicationOperator μ
        ⟨coordinateConstantOne μ,
          coordinate_constant_mem_multiplication_domain μ h₂⟩)
      (coordinateConstantOne μ) =
      ((∫ t : ℝ, t ∂μ : ℝ) : ℂ) := by
  rw [L2.inner_def]
  have hmul := (coordinate_constant_mem_multiplication_domain μ h₂).coeFn_toLp
  have hconst := coordinate_constant_one_coe μ
  have hae : (fun t : ℝ => @inner ℂ ℂ _
      (coordinateMultiplicationOperator μ
        ⟨coordinateConstantOne μ,
          coordinate_constant_mem_multiplication_domain μ h₂⟩ t)
      (coordinateConstantOne μ t)) =ᵐ[μ] fun t => (t : ℂ) := by
    filter_upwards [hmul, hconst] with t ht hone
    change (coordinateMultiplicationOperator μ
      ⟨coordinateConstantOne μ,
        coordinate_constant_mem_multiplication_domain μ h₂⟩ : ℝ → ℂ) t = _ at ht
    rw [ht, hone]
    simp [RCLike.inner_apply]
  rw [integral_congr_ae hae]
  exact integral_ofReal

/-- The native Gamma(2) and Gamma(3) stationary realizations cannot be
unitarily identified while also retaining their literal coordinate marks. -/
theorem gamma_shapes_no_coordinate_marked_unitary
    (U : LaguerreWeightedHilbert ≃ₗᵢ[ℂ] GammaShapeThreeWeightedHilbert)
    (hone : U (coordinateConstantOne gammaProbability) =
      coordinateConstantOne gammaShapeThreeProbability)
    (hmark : ∀ (f : LaguerreWeightedHilbert)
      (hf : f ∈ (coordinateMultiplicationOperator gammaProbability).domain),
      ∃ hf' : U f ∈ (coordinateMultiplicationOperator gammaShapeThreeProbability).domain,
        U (coordinateMultiplicationOperator gammaProbability ⟨f, hf⟩) =
          coordinateMultiplicationOperator gammaShapeThreeProbability ⟨U f, hf'⟩) :
    False := by
  have h₂ : Integrable (fun t : ℝ => t ^ 2) gammaProbability :=
    gamma_probability_monomial_integrable 2
  have h₃ : Integrable (fun t : ℝ => t ^ 2) gammaShapeThreeProbability :=
    gamma_shape_three_monomial_integrable 2
  let one₂ := coordinateConstantOne gammaProbability
  let one₃ := coordinateConstantOne gammaShapeThreeProbability
  have hd₂ := coordinate_constant_mem_multiplication_domain gammaProbability h₂
  have hd₃ := coordinate_constant_mem_multiplication_domain gammaShapeThreeProbability h₃
  obtain ⟨hd₃', he⟩ := hmark one₂ hd₂
  have hs : (⟨U one₂, hd₃'⟩ :
      (coordinateMultiplicationOperator gammaShapeThreeProbability).domain) =
      ⟨one₃, hd₃⟩ := Subtype.ext hone
  rw [hs] at he
  have hm₂ := coordinate_multiplication_constant_expectation gammaProbability h₂
  have hm₃ := coordinate_multiplication_constant_expectation gammaShapeThreeProbability h₃
  have hmeans : ((2 : ℝ) : ℂ) = ((3 : ℝ) : ℂ) := by
    rw [← gamma_probability_mean, ← gamma_shape_three_mean]
    rw [← hm₂, ← hm₃]
    calc
      @inner ℂ LaguerreWeightedHilbert _
        (coordinateMultiplicationOperator gammaProbability ⟨one₂, hd₂⟩) one₂ =
        @inner ℂ GammaShapeThreeWeightedHilbert _
          (U (coordinateMultiplicationOperator gammaProbability ⟨one₂, hd₂⟩))
          (U one₂) := (U.inner_map_map _ _).symm
      _ = @inner ℂ GammaShapeThreeWeightedHilbert _
          (coordinateMultiplicationOperator gammaShapeThreeProbability ⟨one₃, hd₃⟩)
          one₃ := by rw [he, hone]
  norm_num at hmeans

theorem gamma_shape_two_coordinate_constant_eq_basis_zero :
    coordinateConstantOne gammaProbability = laguerreHilbertBasis 0 := by
  apply Lp.ext
  filter_upwards [coordinate_constant_one_coe gammaProbability,
    laguerre_basis_zero_coe] with t hone hbasis
  exact hone.trans hbasis.symm

theorem gamma_shape_three_coordinate_constant_eq_basis_zero :
    coordinateConstantOne gammaShapeThreeProbability =
      gammaShapeThreeHilbertBasis 0 := by
  apply Lp.ext
  filter_upwards [coordinate_constant_one_coe gammaShapeThreeProbability,
    gamma_shape_three_basis_zero_coe] with t hone hbasis
  exact hone.trans hbasis.symm

/-- The precise constant-preserving unitary from the unmarked O5 boundary
cannot intertwine the two actual maximal coordinate multiplication operators. -/
theorem gamma_shape_unitary_not_coordinate_marked :
    ¬ ∀ (f : LaguerreWeightedHilbert)
      (hf : f ∈ (coordinateMultiplicationOperator gammaProbability).domain),
      ∃ hf' : gammaShapeUnitary f ∈
          (coordinateMultiplicationOperator gammaShapeThreeProbability).domain,
        gammaShapeUnitary
            (coordinateMultiplicationOperator gammaProbability ⟨f, hf⟩) =
          coordinateMultiplicationOperator gammaShapeThreeProbability
            ⟨gammaShapeUnitary f, hf'⟩ := by
  intro hmark
  apply gamma_shapes_no_coordinate_marked_unitary gammaShapeUnitary
  · rw [gamma_shape_two_coordinate_constant_eq_basis_zero,
      gamma_shape_three_coordinate_constant_eq_basis_zero]
    exact gamma_shape_unitary_basis 0
  · exact hmark

end
end Sigma
