import SigmaProbFourierUnique
import SigmaProbGammaTransforms
import SigmaProbBoundaries

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

theorem gamma_characteristic_identifies_real_line_measure (μ : Measure ℝ)
    [IsFiniteMeasure μ]
    (h : ∀ x, probabilityCharacteristic μ x = gammaCharacteristic x) :
    μ = gammaProbability := by
  apply finite_measure_characteristic_unique μ gammaProbability
  intro x
  rw [h x, gamma_probability_characteristic]

theorem linked_characteristic_identifies_real_line_probability (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hlink : ∀ x, probabilityCharacteristic μ x =
      probabilityCharacteristic μ (c*x) * residualCharacteristic c x) :
    μ = gammaProbability := by
  apply gamma_characteristic_identifies_real_line_measure μ
  exact congrFun (linked_probability_characteristic μ c hc0 hc1 hlink)

/-- All three P9 clauses are equivalent for an arbitrary probability on R.
The source law has no prior support, density or moment requirement. -/
theorem real_line_residual_characterization (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (μ = gammaProbability ↔ independentAffineSum μ (gammaResidualProbability c) c = μ) ∧
    (μ = gammaProbability ↔ ∀ x, probabilityCharacteristic μ x =
      probabilityCharacteristic μ (c*x) * residualCharacteristic c x) := by
  constructor
  · constructor
    · rintro rfl
      exact gamma_canonical_self_decomposition c hc0 hc1.le
    · exact canonical_residual_identifies_gamma μ c hc0 hc1
  · constructor
    · rintro rfl x
      exact gamma_characteristic_equation c x
    · exact linked_characteristic_identifies_real_line_probability μ c hc0 hc1

theorem unlinked_residual_observation_counterexample (c : ℝ) :
    (gammaProbability, gammaResidualProbability c).2 =
      (Measure.dirac (0 : ℝ), gammaResidualProbability c).2 ∧
    (gammaProbability, gammaResidualProbability c).1 ≠
      (Measure.dirac (0 : ℝ), gammaResidualProbability c).1 := by
  constructor
  · rfl
  · intro he
    dsimp only at he
    have hz := gamma_probability_no_atom 0
    rw [he] at hz
    simp at hz

theorem log_characteristic_as_mellin (μ : Measure ℝ)
    (hpos : ∀ᵐ t ∂μ, 0 < t) (x : ℝ) :
    probabilityCharacteristic (Measure.map Real.log μ) x =
      ∫ t : ℝ, (t : ℂ) ^ (Complex.I*(x : ℂ)) ∂μ := by
  have hm : AEStronglyMeasurable (fun t : ℝ => Complex.exp (((x*t : ℝ) : ℂ)*Complex.I))
      (Measure.map Real.log μ) :=
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
      continuous_const).cexp.aestronglyMeasurable
  rw [probabilityCharacteristic, integral_map Real.measurable_log.aemeasurable hm]
  apply integral_congr_ae
  filter_upwards [hpos] with t ht
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'),
    ← Complex.ofReal_log ht.le]
  congr 1
  push_cast
  ring

theorem gamma_mellin_on_imaginary_line (x : ℝ) :
    (∫ t : ℝ, (t : ℂ) ^ (Complex.I*(x : ℂ)) ∂gammaProbability) =
      Complex.Gamma (2+Complex.I*(x : ℂ)) := by
  have he := gamma_complex_mellin (1+Complex.I*(x : ℂ)) (by simp)
  have h1 : 1+Complex.I*(x : ℂ)-1 = Complex.I*(x : ℂ) := by ring
  have h2 : 1+Complex.I*(x : ℂ)+1 = 2+Complex.I*(x : ℂ) := by ring
  simpa only [h1, h2] using he

theorem imaginary_mellin_identifies_positive_probability (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hpos : ∀ᵐ t ∂μ, 0 < t)
    (hm : ∀ x : ℝ, (∫ t : ℝ, (t : ℂ) ^ (Complex.I*(x : ℂ)) ∂μ) =
      Complex.Gamma (2+Complex.I*(x : ℂ))) : μ = gammaProbability := by
  have hgpos := operator_integer_samples_ae_pos gammaProbability
    operator_gamma_probability_integer_samples
  have he : Measure.map Real.log μ = Measure.map Real.log gammaProbability := by
    apply finite_measure_characteristic_unique
    intro x
    rw [log_characteristic_as_mellin μ hpos, log_characteristic_as_mellin gammaProbability hgpos,
      hm, gamma_mellin_on_imaginary_line]
  have hb (ρ : Measure ℝ) (hρ : ∀ᵐ t ∂ρ, 0 < t) :
      Measure.map Real.exp (Measure.map Real.log ρ) = ρ := by
    rw [Measure.map_map Real.measurable_exp Real.measurable_log]
    calc
      Measure.map (Real.exp ∘ Real.log) ρ = Measure.map id ρ := by
        apply Measure.map_congr
        filter_upwards [hρ] with t ht
        exact Real.exp_log ht
      _ = ρ := Measure.map_id
  calc
    μ = Measure.map Real.exp (Measure.map Real.log μ) := (hb μ hpos).symm
    _ = Measure.map Real.exp (Measure.map Real.log gammaProbability) := by rw [he]
    _ = gammaProbability := hb gammaProbability hgpos

end
end Sigma
