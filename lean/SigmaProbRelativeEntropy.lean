import SigmaProbPoisson
import Mathlib.MeasureTheory.Decomposition.RadonNikodym

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal NNReal

/-- The ordinary real log-Radon--Nikodym integral. Statements below also prove
its integrability and absolute continuity, so it is the finite relative entropy. -/
def finiteRelativeEntropy {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ :=
  ∫ x, Real.log ((μ.rnDeriv ν x).toReal) ∂μ

theorem rn_derivative_positive_densities {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SigmaFinite ν] (f g : α → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hfp : ∀ᵐ x ∂ν, 0 ≤ f x) (hgp : ∀ᵐ x ∂ν, 0 < g x) :
    (fun x => (((ν.withDensity (fun x => ENNReal.ofReal (f x))).rnDeriv
      (ν.withDensity (fun x => ENNReal.ofReal (g x)))) x).toReal) =ᵐ[
      ν.withDensity (fun x => ENNReal.ofReal (f x))] (fun x => f x/g x) := by
  letI : SigmaFinite (ν.withDensity (fun x => ENNReal.ofReal (f x))) :=
    SigmaFinite.withDensity_of_ne_top (ae_of_all _ (fun _ => ENNReal.ofReal_ne_top))
  have h₁ := Measure.rnDeriv_withDensity_right
    (ν.withDensity (fun x => ENNReal.ofReal (f x))) ν hg.ennreal_ofReal.aemeasurable
    (hgp.mono (fun x hx => (ENNReal.ofReal_pos.mpr hx).ne'))
    (ae_of_all _ (fun _ => ENNReal.ofReal_ne_top))
  have h₂ := Measure.rnDeriv_withDensity ν hf.ennreal_ofReal
  apply (withDensity_absolutelyContinuous ν (fun x => ENNReal.ofReal (f x))).ae_le
  filter_upwards [h₁,h₂,hfp,hgp] with x hx hy hfx hgx
  rw [hx,hy,ENNReal.toReal_mul,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hfx,ENNReal.toReal_ofReal hgx.le]
  ring

theorem positive_density_absolute_continuity {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (f g : α → ℝ) (hg : Measurable g)
    (hgp : ∀ᵐ x ∂ν, 0 < g x) :
    ν.withDensity (fun x => ENNReal.ofReal (f x)) ≪
      ν.withDensity (fun x => ENNReal.ofReal (g x)) := by
  exact (withDensity_absolutelyContinuous ν _).trans
    (withDensity_absolutelyContinuous' hg.ennreal_ofReal.aemeasurable
      (hgp.mono (fun x hx => (ENNReal.ofReal_pos.mpr hx).ne')))

instance naturalCountingMeasure_sigmaFinite : SigmaFinite (Measure.count : Measure ℕ) := by
  refine ⟨⟨{set := fun n => {n}
            set_mem := fun _ => mem_univ _
            finite := fun n => ?_
            spanning := ?_}⟩⟩
  · simp
  · ext n; simp

theorem poisson_general_mass (r : ℝ≥0) (n : ℕ) :
    (poissonPMF r n).toReal = poissonPMFReal r n := by
  change (ENNReal.ofReal _).toReal = _
  exact ENNReal.toReal_ofReal poissonPMFReal_nonneg

theorem poisson_general_recurrence (r : ℝ≥0) (n : ℕ) :
    ((n+1:ℕ):ℝ)*(poissonPMF r (n+1)).toReal =
      (r:ℝ)*(poissonPMF r n).toReal := by
  rw [poisson_general_mass,poisson_general_mass]
  unfold poissonPMFReal
  rw [Nat.factorial_succ,Nat.cast_mul,pow_succ]
  field_simp
  ring

theorem poisson_general_mean_hasSum (r : ℝ≥0) :
    HasSum (fun n:ℕ => (n:ℝ)*(poissonPMF r n).toReal) (r:ℝ) := by
  have hs : HasSum (fun n:ℕ => ((n+1:ℕ):ℝ)*(poissonPMF r (n+1)).toReal) (r:ℝ) := by
    simpa only [poisson_general_recurrence,mul_one] using (pmf_real_mass (poissonPMF r)).mul_left (r:ℝ)
  have hh := (hasSum_nat_add_iff
    (f := fun n:ℕ => (n:ℝ)*(poissonPMF r n).toReal) (g := (r:ℝ)) 1).mp hs
  simpa only [Finset.sum_range_one,Nat.cast_zero,zero_mul,add_zero] using hh

theorem poisson_general_identity_integrable (r : ℝ≥0) :
    Integrable (fun n:ℕ => (n:ℝ)) (poissonMeasure r) := by
  apply pmf_integrable_of_summable
  convert (poisson_general_mean_hasSum r).summable using 1
  funext n
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg n)]

theorem poisson_general_mean (r : ℝ≥0) :
    (∫ n:ℕ, (n:ℝ) ∂poissonMeasure r) = (r:ℝ) := by
  rw [poissonMeasure,PMF.integral_eq_tsum _ _ (poisson_general_identity_integrable r)]
  simpa only [smul_eq_mul,mul_comm] using (poisson_general_mean_hasSum r).tsum_eq

theorem poisson_measure_density (r : ℝ≥0) :
    poissonMeasure r = (Measure.count : Measure ℕ).withDensity
      (fun n => ENNReal.ofReal (poissonPMFReal r n)) := by
  apply Measure.ext_of_singleton
  intro n
  rw [poissonMeasure,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    withDensity_apply _ (measurableSet_singleton _),lintegral_singleton]
  simp only [Measure.count_singleton,mul_one]
  rfl

theorem poisson_log_likelihood (a b : ℝ≥0) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    Real.log (poissonPMFReal a n/poissonPMFReal b n) =
      (b:ℝ)-(a:ℝ)+(n:ℝ)*Real.log ((a:ℝ)/(b:ℝ)) := by
  have hfa := poissonPMFReal_pos (n := n) ha
  have hfb := poissonPMFReal_pos (n := n) hb
  have hpa : (0:ℝ)<a := ha
  have hpb : (0:ℝ)<b := hb
  rw [Real.log_div hfa.ne' hfb.ne']
  unfold poissonPMFReal
  rw [Real.log_div (mul_pos (Real.exp_pos _) (pow_pos hpa _)).ne' (by positivity),
    Real.log_div (mul_pos (Real.exp_pos _) (pow_pos hpb _)).ne' (by positivity),
    Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ hpa.ne'),
    Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ hpb.ne'),
    Real.log_exp,Real.log_exp,Real.log_pow,Real.log_pow,Real.log_div hpa.ne' hpb.ne']
  ring

theorem poisson_log_rn_derivative (a b : ℝ≥0) (ha : 0 < a) (hb : 0 < b) :
    (fun n => Real.log (((poissonMeasure a).rnDeriv (poissonMeasure b) n).toReal)) =ᵐ[
      poissonMeasure a] (fun n => (b:ℝ)-(a:ℝ)+(n:ℝ)*Real.log ((a:ℝ)/(b:ℝ))) := by
  have hh := rn_derivative_positive_densities (Measure.count : Measure ℕ)
    (poissonPMFReal a) (poissonPMFReal b) (measurable_poissonPMFReal a)
    (measurable_poissonPMFReal b) (ae_of_all _ (fun _ => poissonPMFReal_nonneg))
    (ae_of_all _ (fun _ => poissonPMFReal_pos hb))
  rw [← poisson_measure_density a,← poisson_measure_density b] at hh
  filter_upwards [hh] with n hn
  rw [hn,poisson_log_likelihood a b ha hb]

theorem poisson_relative_entropy_integrable (a b : ℝ≥0) (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun n => Real.log (((poissonMeasure a).rnDeriv (poissonMeasure b) n).toReal))
      (poissonMeasure a) := by
  apply ((integrable_const ((b:ℝ)-(a:ℝ))).add
    ((poisson_general_identity_integrable a).mul_const (Real.log ((a:ℝ)/(b:ℝ))))).congr
  exact (poisson_log_rn_derivative a b ha hb).symm

theorem poisson_relative_entropy (a b : ℝ≥0) (ha : 0 < a) (hb : 0 < b) :
    finiteRelativeEntropy (poissonMeasure a) (poissonMeasure b) =
      (a:ℝ)*SigmaBase.potential ((b:ℝ)/(a:ℝ)) := by
  rw [finiteRelativeEntropy,integral_congr_ae (poisson_log_rn_derivative a b ha hb),
    integral_add (integrable_const _) ((poisson_general_identity_integrable a).mul_const _),
    integral_const,integral_mul_right,poisson_general_mean]
  simp only [measure_univ,ENNReal.one_toReal,one_smul]
  convert SigmaPresentations.poisson_KL_orientation (show (0:ℝ)<a from ha) (show (0:ℝ)<b from hb) using 1 <;> ring

theorem poisson_mutual_absolute_continuity (a b : ℝ≥0) (ha : 0 < a) (hb : 0 < b) :
    poissonMeasure a ≪ poissonMeasure b ∧ poissonMeasure b ≪ poissonMeasure a := by
  simp only [poisson_measure_density]
  constructor
  · exact positive_density_absolute_continuity _ _ _ (measurable_poissonPMFReal b)
      (ae_of_all _ (fun _ => poissonPMFReal_pos hb))
  · exact positive_density_absolute_continuity _ _ _ (measurable_poissonPMFReal a)
      (ae_of_all _ (fun _ => poissonPMFReal_pos ha))

end
end Sigma
