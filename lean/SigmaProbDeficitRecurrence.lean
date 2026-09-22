import SigmaProbMomentUnique
import SigmaProbDeficitZetaCumulants
import Mathlib.Analysis.Calculus.FDeriv.Analytic

namespace Sigma
noncomputable section
open MeasureTheory Filter PowerSeries
open scoped Topology BigOperators

def deficitMomentSeries : PowerSeries ℝ :=
  PowerSeries.mk fun n =>
    (∫ v : ℝ, v ^ n ∂gammaDeficitProbability) / (n.factorial : ℝ)

theorem gamma_deficit_abs_exponential_integrable :
    Integrable (fun v : ℝ => Real.exp ((1 / 2 : ℝ) * |v|))
      gammaDeficitProbability := by
  apply (gamma_deficit_exponential_integrable (1 / 2) (by norm_num)).congr
  filter_upwards [gamma_deficit_nonnegative] with v hv
  rw [abs_of_nonneg hv]

theorem deficit_mgf_formal_germ :
    HasRealFormalGerm
      (fun s : ℝ => ∫ v : ℝ, Real.exp (s * v) ∂gammaDeficitProbability)
      deficitMomentSeries := by
  apply (real_formal_germ_iff _ _).mpr
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
  have hs' : |s| < 1 / 2 := by
    simpa [Real.dist_eq] using hs
  have hi : Integrable (fun v : ℝ => Real.exp (|s| * |v|))
      gammaDeficitProbability := by
    apply gamma_deficit_abs_exponential_integrable.mono'
      ((continuous_const.mul continuous_abs).rexp.aestronglyMeasurable)
    filter_upwards with v
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hs'.le (abs_nonneg v))
  have hsum := exponential_series_integral gammaDeficitProbability s hi
  convert hsum using 1
  funext n
  simp only [deficitMomentSeries, coeff_mk, opExpTerm, mul_pow, integral_div,
    integral_mul_left]
  ring

theorem gamma_deficit_algebraic_cumulant_recurrence :
    AlgebraicCumulantRecurrence gammaDeficitProbability
      (probabilityCumulant gammaDeficitProbability) := by
  let M : ℝ → ℝ := fun s => ∫ v : ℝ, Real.exp (s * v) ∂gammaDeficitProbability
  let K : ℝ → ℝ := probabilityCGF gammaDeficitProbability
  have hM : HasRealFormalGerm M deficitMomentSeries := by
    simpa [M] using deficit_mgf_formal_germ
  have hK : HasRealFormalGerm K deficitCGFFormal := by
    simpa [K] using deficit_cgf_formal_germ
  have hMd : AnalyticAt ℝ (deriv M) 0 := by
    simpa only [deriv] using
      ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).analyticAt _).comp hM.analyticAt.fderiv
  have hKd : AnalyticAt ℝ (deriv K) 0 := by
    simpa only [deriv] using
      ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).analyticAt _).comp hK.analyticAt.fderiv
  obtain ⟨DM, hDM⟩ := analytic_has_real_formal_germ (deriv M) hMd
  obtain ⟨DK, hDK⟩ := analytic_has_real_formal_germ (deriv K) hKd
  have hM0 : M 0 ≠ 0 := by simp [M]
  have hrel : deriv M =ᶠ[𝓝 0] fun s => deriv K s * M s := by
    filter_upwards [hM.analyticAt.eventually_analyticAt,
      hM.continuousAt.eventually_ne hM0] with s hMs hMne
    have hd := (hMs.differentiableAt.hasDerivAt.log hMne).deriv
    change deriv K s = deriv M s / M s at hd
    rw [hd]
    field_simp
  have hprod : HasRealFormalGerm (fun s => deriv K s * M s) (DK * deficitMomentSeries) :=
    real_formal_germ_mul hDK hM
  have hseries : DM = DK * deficitMomentSeries :=
    real_formal_germ_unique (real_formal_germ_congr hDM hrel) hprod
  intro n
  have hcoeff := congrArg (coeff ℝ n) hseries
  rw [coeff_mul] at hcoeff
  obtain ⟨rDM, hrDM⟩ := hDM
  obtain ⟨rDK, hrDK⟩ := hDK
  obtain ⟨rM, hrM⟩ := hM
  have hDMn : (n.factorial : ℝ) * coeff ℝ n DM =
      iteratedDeriv n (deriv M) 0 := by
    simpa [iteratedDeriv, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      nsmul_eq_mul] using hrDM.factorial_smul (1 : ℝ) n
  have hDKn (j : ℕ) : (j.factorial : ℝ) * coeff ℝ j DK =
      probabilityCumulant gammaDeficitProbability (j + 1) := by
    have hj : (j.factorial : ℝ) * coeff ℝ j DK =
        iteratedDeriv j (deriv K) 0 := by
      simpa [iteratedDeriv, FormalMultilinearSeries.ofScalars, smul_eq_mul,
        nsmul_eq_mul] using hrDK.factorial_smul (1 : ℝ) j
    rw [← iteratedDeriv_succ'] at hj
    simpa [probabilityCumulant, K] using hj
  have hMn (j : ℕ) : iteratedDeriv j M 0 =
      ∫ v : ℝ, v ^ j ∂gammaDeficitProbability := by
    have hj := hrM.factorial_smul (1 : ℝ) j
    have hj' : iteratedDeriv j M 0 =
        (j.factorial : ℝ) * coeff ℝ j deficitMomentSeries := by
      simpa [iteratedDeriv, FormalMultilinearSeries.ofScalars, smul_eq_mul,
        nsmul_eq_mul] using hj.symm
    rw [hj', deficitMomentSeries, coeff_mk]
    field_simp
  have hDMmoment : (n.factorial : ℝ) * coeff ℝ n DM =
      ∫ v : ℝ, v ^ (n + 1) ∂gammaDeficitProbability := by
    rw [hDMn, ← iteratedDeriv_succ']
    exact hMn (n + 1)
  have hcoeff' : coeff ℝ n DM =
      ∑ j ∈ Finset.range (n + 1),
        coeff ℝ j DK * coeff ℝ (n - j) deficitMomentSeries := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff ℝ i DK * coeff ℝ j deficitMomentSeries) n] at hcoeff
    simpa only [Nat.succ_eq_add_one] using hcoeff
  rw [← hDMmoment, hcoeff', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hfac : (Nat.choose n j : ℝ) * (j.factorial : ℝ) * ((n - j).factorial : ℝ) =
      (n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
  have hjD := hDKn j
  have hjf : (j.factorial : ℝ) ≠ 0 := by positivity
  have hnjf : ((n - j).factorial : ℝ) ≠ 0 := by positivity
  rw [show coeff ℝ (n - j) deficitMomentSeries =
      (∫ v : ℝ, v ^ (n - j) ∂gammaDeficitProbability) /
        ((n - j).factorial : ℝ) by simp [deficitMomentSeries]]
  rw [← hjD]
  calc
    (n.factorial : ℝ) *
        (coeff ℝ j DK *
          ((∫ v : ℝ, v ^ (n - j) ∂gammaDeficitProbability) /
            ((n - j).factorial : ℝ))) =
        ((Nat.choose n j : ℝ) * (j.factorial : ℝ) * ((n - j).factorial : ℝ)) *
          (coeff ℝ j DK *
            ((∫ v : ℝ, v ^ (n - j) ∂gammaDeficitProbability) /
              ((n - j).factorial : ℝ))) := by rw [hfac]
    _ = (Nat.choose n j : ℝ) * ((j.factorial : ℝ) * coeff ℝ j DK) *
          (∫ v : ℝ, v ^ (n - j) ∂gammaDeficitProbability) := by
      field_simp [hnjf]
      ring

def deficitCumulantValue (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * deficitCGFCoeff n

theorem deficit_cumulant_value_eq (n : ℕ) :
    deficitCumulantValue n = probabilityCumulant gammaDeficitProbability n := by
  exact (deficit_cumulant_coeff n).symm

theorem gamma_deficit_explicit_algebraic_cumulant_recurrence :
    AlgebraicCumulantRecurrence gammaDeficitProbability deficitCumulantValue := by
  rw [show deficitCumulantValue = probabilityCumulant gammaDeficitProbability by
    funext n
    exact deficit_cumulant_value_eq n]
  exact gamma_deficit_algebraic_cumulant_recurrence

theorem gamma_deficit_explicit_algebraic_cumulants_identify (μ : Measure ℝ)
    [IsProbabilityMeasure μ]
    (hi : ∀ n : ℕ, Integrable (fun t : ℝ => t ^ n) μ)
    (hμ : AlgebraicCumulantRecurrence μ deficitCumulantValue) :
    μ = gammaDeficitProbability := by
  exact gamma_deficit_algebraic_cumulants_identify μ deficitCumulantValue hi hμ
    gamma_deficit_explicit_algebraic_cumulant_recurrence

theorem gamma_deficit_mean :
    (∫ v : ℝ, v ∂gammaDeficitProbability) = Real.eulerMascheroniConstant := by
  have h := gamma_deficit_algebraic_cumulant_recurrence 0
  simpa [AlgebraicCumulantRecurrence, deficit_cumulant_one] using h

theorem gamma_deficit_second_moment :
    (∫ v : ℝ, v ^ 2 ∂gammaDeficitProbability) =
      Real.eulerMascheroniConstant ^ 2 + Real.pi ^ 2 / 6 - 1 := by
  have h := gamma_deficit_algebraic_cumulant_recurrence 1
  have h2 := deficit_cumulants_two_three_four.1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
    Nat.choose_one_right, Nat.cast_one, one_mul, Nat.one_sub, pow_zero, pow_one] at h
  norm_num at h
  rw [deficit_cumulant_one, h2, gamma_deficit_mean] at h
  nlinarith

theorem gamma_deficit_identity_integrable :
    Integrable (fun v : ℝ => v) gammaDeficitProbability := by
  apply ((gamma_deficit_exponential_integrable (1 / 2) (by norm_num)).const_mul 2).mono'
    continuous_id.aestronglyMeasurable
  filter_upwards [gamma_deficit_nonnegative] with v hv
  simp only [id_eq]
  rw [Real.norm_eq_abs, abs_of_nonneg hv]
  have h := Real.add_one_le_exp ((1 / 2 : ℝ) * v)
  nlinarith

theorem gamma_deficit_square_integrable :
    Integrable (fun v : ℝ => v ^ 2) gammaDeficitProbability := by
  apply ((gamma_deficit_exponential_integrable (1 / 2) (by norm_num)).const_mul 8).mono'
    (continuous_id.pow 2).aestronglyMeasurable
  filter_upwards [gamma_deficit_nonnegative] with v hv
  simp only [id_eq]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg v)]
  have h := Real.pow_div_factorial_le_exp ((1 / 2 : ℝ) * v)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hv) 2
  norm_num [Nat.factorial] at h
  nlinarith

theorem gamma_deficit_variance :
    (∫ v : ℝ, (v - Real.eulerMascheroniConstant) ^ 2
      ∂gammaDeficitProbability) = Real.pi ^ 2 / 6 - 1 := by
  have hlin : Integrable
      (fun v : ℝ => v ^ 2 - 2 * Real.eulerMascheroniConstant * v)
      gammaDeficitProbability :=
    gamma_deficit_square_integrable.sub
      (gamma_deficit_identity_integrable.const_mul (2 * Real.eulerMascheroniConstant))
  have he : (fun v : ℝ => (v - Real.eulerMascheroniConstant) ^ 2) =
      fun v => (v ^ 2 - 2 * Real.eulerMascheroniConstant * v) +
        Real.eulerMascheroniConstant ^ 2 := by
    funext v
    ring
  rw [he, integral_add hlin (integrable_const _),
    integral_sub gamma_deficit_square_integrable
      (gamma_deficit_identity_integrable.const_mul (2 * Real.eulerMascheroniConstant)),
    integral_mul_left, gamma_deficit_second_moment, gamma_deficit_mean]
  simp
  ring

end
end Sigma
