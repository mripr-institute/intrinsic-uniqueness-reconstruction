import SigmaOpMixing
import Mathlib.MeasureTheory.Decomposition.Jordan
import Mathlib.MeasureTheory.Measure.Complex

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

/-- The usual integral of a real test against a genuine signed measure,
defined through its native Jordan decomposition. The pinned Mathlib version
does not supply a signed-measure integral notation. -/
def signedRealIntegral {α : Type*} [MeasurableSpace α]
    (μ : SignedMeasure α) (f : α → ℝ) : ℝ :=
  (∫ x, f x ∂μ.toJordanDecomposition.posPart)-
    ∫ x, f x ∂μ.toJordanDecomposition.negPart

def complexRealIntegral {α : Type*} [MeasurableSpace α]
    (μ : ComplexMeasure α) (f : α → ℝ) : ℂ :=
  ⟨signedRealIntegral μ.re f,signedRealIntegral μ.im f⟩

theorem signed_total_variation_finite {α : Type*} [MeasurableSpace α]
    (μ : SignedMeasure α) : IsFiniteMeasure μ.totalVariation := by
  unfold SignedMeasure.totalVariation
  infer_instance

theorem signed_measure_norm_le_variation {α : Type*} [MeasurableSpace α]
    (μ : SignedMeasure α) (E : Set α) (hE : MeasurableSet E) :
    ‖μ E‖≤(μ.totalVariation E).toReal := by
  have h := congrArg (fun ν : SignedMeasure α => ν E) μ.toSignedMeasure_toJordanDecomposition
  simp only [JordanDecomposition.toSignedMeasure,VectorMeasure.sub_apply,
    Measure.toSignedMeasure_apply_measurable hE] at h
  rw [← h,SignedMeasure.totalVariation,Measure.add_apply,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  simpa only [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg] using
    norm_sub_le (μ.toJordanDecomposition.posPart E).toReal (μ.toJordanDecomposition.negPart E).toReal

/-- A finite positive control measure dominates every complex-measure norm.
Hence these native complex measures have finite total variation; no density
representation or positivity of the complex measure is being assumed. -/
def complexVariationControl {α : Type*} [MeasurableSpace α] (μ : ComplexMeasure α) : Measure α :=
  μ.re.totalVariation+μ.im.totalVariation

instance complex_variation_control_finite {α : Type*} [MeasurableSpace α]
    (μ : ComplexMeasure α) : IsFiniteMeasure (complexVariationControl μ) := by
  letI := signed_total_variation_finite μ.re
  letI := signed_total_variation_finite μ.im
  unfold complexVariationControl
  infer_instance

theorem complex_measure_norm_le_control {α : Type*} [MeasurableSpace α]
    (μ : ComplexMeasure α) (E : Set α) (hE : MeasurableSet E) :
    ‖μ E‖≤(complexVariationControl μ E).toReal := by
  letI := signed_total_variation_finite μ.re
  letI := signed_total_variation_finite μ.im
  rw [complexVariationControl,Measure.add_apply,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have hre := signed_measure_norm_le_variation μ.re E hE
  have him := signed_measure_norm_le_variation μ.im E hE
  have hh : ‖μ E‖≤‖μ.re E‖+‖μ.im E‖ := by
    calc
      ‖μ E‖=‖((μ E).re:ℂ)+((μ E).im:ℂ)*Complex.I‖ := by rw [Complex.re_add_im]
      _ ≤ ‖((μ E).re:ℂ)‖+‖((μ E).im:ℂ)*Complex.I‖ := norm_add_le _ _
      _ = _ := by simp
  linarith

def nonnegativeLaplaceTest (n : ℕ) (s : OpNonnegativeRay) : ℝ :=
  Real.exp (-(n:ℝ)*(s:ℝ))

theorem nonnegative_laplace_test_integrable (μ : Measure OpNonnegativeRay)
    [IsFiniteMeasure μ] (n : ℕ) : Integrable (nonnegativeLaplaceTest n) μ := by
  apply (integrable_const (1:ℝ)).mono'
    (by exact ((continuous_const.mul continuous_subtype_val).rexp).aestronglyMeasurable)
  filter_upwards with s
  unfold nonnegativeLaplaceTest
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) s.property

/-- All integer Laplace samples, including mass at n=0, identify an actual
finite signed measure on the full closed nonnegative ray. -/
theorem operator_signed_mixing_measure_unique (μ ν : SignedMeasure OpNonnegativeRay)
    (h : ∀ n : ℕ, signedRealIntegral μ (nonnegativeLaplaceTest n)=
      signedRealIntegral ν (nonnegativeLaplaceTest n)) : μ=ν := by
  have he : μ.toJordanDecomposition.posPart+ν.toJordanDecomposition.negPart=
      ν.toJordanDecomposition.posPart+μ.toJordanDecomposition.negPart := by
    apply operator_nonnegative_mixing_measure_unique
    intro n
    change (∫ s, nonnegativeLaplaceTest n s ∂_)=∫ s, nonnegativeLaplaceTest n s ∂_
    rw [integral_add_measure (nonnegative_laplace_test_integrable _ n)
      (nonnegative_laplace_test_integrable _ n),
      integral_add_measure (nonnegative_laplace_test_integrable _ n)
      (nonnegative_laplace_test_integrable _ n)]
    have hh := h n
    unfold signedRealIntegral at hh
    linarith
  have hh : (μ.toJordanDecomposition.posPart+ν.toJordanDecomposition.negPart).toSignedMeasure=
      (ν.toJordanDecomposition.posPart+μ.toJordanDecomposition.negPart).toSignedMeasure := by
    congr 1
  rw [Measure.toSignedMeasure_add,Measure.toSignedMeasure_add] at hh
  have hμ := μ.toSignedMeasure_toJordanDecomposition
  have hν := ν.toSignedMeasure_toJordanDecomposition
  unfold JordanDecomposition.toSignedMeasure at hμ hν
  rw [← hμ,← hν]
  exact sub_eq_sub_iff_add_eq_add.mpr hh

/-- Complex-measure uniqueness reduces to the actual signed real and imaginary
measures. No positivity of the unknown measure is imposed. -/
theorem operator_complex_mixing_measure_unique (μ ν : ComplexMeasure OpNonnegativeRay)
    (h : ∀ n : ℕ, complexRealIntegral μ (nonnegativeLaplaceTest n)=
      complexRealIntegral ν (nonnegativeLaplaceTest n)) : μ=ν := by
  have hre : μ.re=ν.re := operator_signed_mixing_measure_unique _ _
    (fun n => congrArg Complex.re (h n))
  have him : μ.im=ν.im := operator_signed_mixing_measure_unique _ _
    (fun n => congrArg Complex.im (h n))
  exact ComplexMeasure.equivSignedMeasure.injective (Prod.ext hre him)

theorem signed_real_integral_positive {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) :
    signedRealIntegral μ.toSignedMeasure f=∫ x, f x ∂μ := by
  let j : JordanDecomposition α := ⟨μ,0,Measure.MutuallySingular.zero_right⟩
  have hj : j.toSignedMeasure=μ.toSignedMeasure := by
    simp [j,JordanDecomposition.toSignedMeasure]
  have he : μ.toSignedMeasure.toJordanDecomposition=j := by
    rw [← hj,j.toJordanDecomposition_toSignedMeasure]
  simp [signedRealIntegral,he,j]

theorem signed_real_integral_zero {α : Type*} [MeasurableSpace α] (f : α → ℝ) :
    signedRealIntegral (0 : SignedMeasure α) f=0 := by
  simp [signedRealIntegral,SignedMeasure.toJordanDecomposition_zero]

theorem signed_integer_sample_zero_mass (μ : SignedMeasure OpNonnegativeRay) :
    signedRealIntegral μ (nonnegativeLaplaceTest 0)=μ univ := by
  have h := congrArg (fun ν : SignedMeasure OpNonnegativeRay => ν univ)
    μ.toSignedMeasure_toJordanDecomposition
  simpa [signedRealIntegral,nonnegativeLaplaceTest,JordanDecomposition.toSignedMeasure,
    Measure.toSignedMeasure_apply_measurable] using h

theorem complex_integer_sample_zero_mass (μ : ComplexMeasure OpNonnegativeRay) :
    complexRealIntegral μ (nonnegativeLaplaceTest 0)=μ univ := by
  apply Complex.ext
  · exact signed_integer_sample_zero_mass μ.re
  · exact signed_integer_sample_zero_mass μ.im

def nonnegativeGammaCoordinate (t : ℝ) : OpNonnegativeRay := ⟨max t 0,le_max_right t 0⟩

theorem nonnegative_gamma_coordinate_measurable : Measurable nonnegativeGammaCoordinate :=
  ((continuous_id.max continuous_const).subtype_mk _).measurable

def nonnegativeGammaMixingMeasure : Measure OpNonnegativeRay :=
  gammaProbability.map nonnegativeGammaCoordinate

instance nonnegative_gamma_mixing_probability : IsProbabilityMeasure nonnegativeGammaMixingMeasure :=
  MeasureTheory.isProbabilityMeasure_map nonnegative_gamma_coordinate_measurable.aemeasurable

theorem nonnegative_gamma_mixing_on_real_line :
    nonnegativeGammaMixingMeasure.map (fun s : OpNonnegativeRay => (s:ℝ))=gammaProbability := by
  rw [nonnegativeGammaMixingMeasure,Measure.map_map measurable_subtype_coe
    nonnegative_gamma_coordinate_measurable]
  calc
    gammaProbability.map ((fun s : OpNonnegativeRay => (s:ℝ)) ∘ nonnegativeGammaCoordinate)=
        gammaProbability.map id := by
      apply Measure.map_congr
      filter_upwards [operator_integer_samples_ae_pos gammaProbability
        operator_gamma_probability_integer_samples] with t ht
      exact max_eq_left ht.le
    _ = gammaProbability := Measure.map_id

theorem nonnegative_gamma_integer_samples (n : ℕ) :
    (∫ s, nonnegativeLaplaceTest n s ∂nonnegativeGammaMixingMeasure)=(1/(1+(n:ℝ)))^2 := by
  unfold nonnegativeLaplaceTest
  rw [nonnegativeGammaMixingMeasure,integral_map
    nonnegative_gamma_coordinate_measurable.aemeasurable
    ((continuous_const.mul continuous_subtype_val).rexp).aestronglyMeasurable]
  have he : (∫ t, nonnegativeLaplaceTest n (nonnegativeGammaCoordinate t) ∂gammaProbability)=
      ∫ t, Real.exp (-(n:ℝ)*t) ∂gammaProbability := by
    apply integral_congr_ae
    filter_upwards [operator_integer_samples_ae_pos gammaProbability
      operator_gamma_probability_integer_samples] with t ht
    simp [nonnegativeLaplaceTest,nonnegativeGammaCoordinate,max_eq_left ht.le]
  unfold nonnegativeLaplaceTest at he
  rw [he]
  exact operator_gamma_probability_integer_samples n

def nonnegativeGammaComplexMeasure : ComplexMeasure OpNonnegativeRay :=
  nonnegativeGammaMixingMeasure.toSignedMeasure.toComplexMeasure 0

theorem nonnegative_gamma_complex_integer_samples (n : ℕ) :
    complexRealIntegral nonnegativeGammaComplexMeasure (nonnegativeLaplaceTest n)=
      (((1/(1+(n:ℝ)))^2 : ℝ):ℂ) := by
  apply Complex.ext
  · change signedRealIntegral nonnegativeGammaMixingMeasure.toSignedMeasure _=_
    rw [signed_real_integral_positive,nonnegative_gamma_integer_samples]
    rfl
  · change signedRealIntegral (0 : SignedMeasure OpNonnegativeRay) _=0
    exact signed_real_integral_zero _

/-- The exact scalar complex-measure inverse used by the marked integer
eigenvectors in O5. Its conclusion is equality of actual complex measures. -/
theorem operator_complex_gamma_mixing_characterization (μ : ComplexMeasure OpNonnegativeRay)
    (h : ∀ n : ℕ, complexRealIntegral μ (nonnegativeLaplaceTest n)=
      (((1/(1+(n:ℝ)))^2 : ℝ):ℂ)) : μ=nonnegativeGammaComplexMeasure := by
  apply operator_complex_mixing_measure_unique
  intro n
  exact (h n).trans (nonnegative_gamma_complex_integer_samples n).symm

theorem operator_complex_gamma_mixing_iff (μ : ComplexMeasure OpNonnegativeRay) :
    (∀ n : ℕ, complexRealIntegral μ (nonnegativeLaplaceTest n)=
      (((1/(1+(n:ℝ)))^2 : ℝ):ℂ)) ↔ μ=nonnegativeGammaComplexMeasure := by
  constructor
  · exact operator_complex_gamma_mixing_characterization μ
  · rintro rfl
    exact nonnegative_gamma_complex_integer_samples

theorem nonnegative_gamma_complex_measure_apply (E : Set OpNonnegativeRay)
    (hE : MeasurableSet E) :
    nonnegativeGammaComplexMeasure E=((nonnegativeGammaMixingMeasure E).toReal:ℂ) := by
  apply Complex.ext
  · change nonnegativeGammaMixingMeasure.toSignedMeasure E=_
    exact Measure.toSignedMeasure_apply_measurable hE
  · simp [nonnegativeGammaComplexMeasure,SignedMeasure.toComplexMeasure_apply]

end
end Sigma
