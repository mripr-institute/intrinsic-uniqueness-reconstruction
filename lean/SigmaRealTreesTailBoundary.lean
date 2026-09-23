import SigmaRealTreesProbability
import Mathlib.Analysis.SpecialFunctions.Stirling

namespace Sigma
noncomputable section
open Filter
open scoped Topology BigOperators Asymptotics

theorem borel_coefficient_stirling_ratio (n : ℕ) (hn : 0<n) :
    borelCoefficient n*(n:ℝ)*Real.sqrt (n:ℝ)=
      1/(Real.sqrt 2*Stirling.stirlingSeq n) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [borel_coefficient_formula,Stirling.stirlingSeq]
  have hsq : Real.sqrt (2*((m+1:ℕ):ℝ))=Real.sqrt 2*Real.sqrt ((m+1:ℕ):ℝ) :=
    Real.sqrt_mul (by norm_num) _
  rw [hsq,div_pow]
  have hexp : Real.exp (-((m+1:ℕ):ℝ))=(Real.exp 1^(m+1))⁻¹ := by
    rw [Real.exp_neg,← Real.exp_nat_mul]
    congr 1
    congr 1
    ring
  rw [hexp]
  have hfac : ((m+1).factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m+1)
  have hnn : ((m+1:ℕ):ℝ) ≠ 0 := by positivity
  have hsn : Real.sqrt ((m+1:ℕ):ℝ) ≠ 0 := by positivity
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  rw [pow_succ]
  ring

theorem borel_coefficient_scaled_limit :
    Tendsto (fun n : ℕ => borelCoefficient n*(n:ℝ)*Real.sqrt (n:ℝ)) atTop
      (𝓝 (1/Real.sqrt (2*Real.pi))) := by
  have h := (tendsto_const_nhds (x := (1:ℝ))).div
    (tendsto_const_nhds.mul Stirling.tendsto_stirlingSeq_sqrt_pi)
    (show Real.sqrt 2*Real.sqrt Real.pi ≠ 0 by positivity)
  have hh : Real.sqrt (2*Real.pi)=Real.sqrt 2*Real.sqrt Real.pi :=
    Real.sqrt_mul (by norm_num) _
  rw [hh]
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (borel_coefficient_stirling_ratio n hn).symm

def borelTailScale (n : ℕ) : ℝ :=
  1/(Real.sqrt (2*Real.pi)*(n:ℝ)*Real.sqrt (n:ℝ))

theorem borel_tail_scale_rpow (n : ℕ) (hn : 0<n) :
    borelTailScale n=(2*Real.pi)^(-(1/2:ℝ))*(n:ℝ)^(-(3/2:ℝ)) := by
  have hnp : (0:ℝ)<n := by exact_mod_cast hn
  have hn3 : (n:ℝ)^(3/2:ℝ)=(n:ℝ)*Real.sqrt (n:ℝ) := by
    rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hnp,Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [Real.rpow_neg (by positivity) (1/2:ℝ),Real.rpow_neg hnp.le (3/2:ℝ),hn3,
    ← Real.sqrt_eq_rpow]
  simp [borelTailScale,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]

/-- The complete Borel PMF has the exact leading Stirling tail, with its
constant (2π)^(-1/2), rather than just a radius or exponential growth rate. -/
theorem borel_tail_asymptotic : borelCoefficient ~[atTop] borelTailScale := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hp : 0<borelTailScale n := by
      unfold borelTailScale
      have hnp : (0:ℝ)<n := by exact_mod_cast hn
      positivity
    exact fun h => False.elim (hp.ne' h)
  · have h := borel_coefficient_scaled_limit.mul_const (Real.sqrt (2*Real.pi))
    have hn : Real.sqrt (2*Real.pi) ≠ 0 := by positivity
    rw [one_div_mul_cancel hn] at h
    convert h using 1
    funext n
    simp [Pi.div_apply,borelTailScale,div_eq_mul_inv,mul_comm,mul_assoc,mul_left_comm]

def borelTailPerturbation (n : ℕ) : ℝ :=
  borelCoefficient n+(if n=1 then borelCoefficient 2/2 else 0)-
    (if n=2 then borelCoefficient 2/2 else 0)

theorem borel_tail_perturbation_zero : borelTailPerturbation 0=0 := by
  simp [borelTailPerturbation,borel_coefficient_zero]

theorem borel_tail_perturbation_positive (n : ℕ) (hn : 0<n) :
    0<borelTailPerturbation n := by
  have hb : 0<borelCoefficient n := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact borel_coefficient_positive k
  have hb2 : 0<borelCoefficient 2 := borel_coefficient_positive 1
  by_cases h1 : n=1
  · subst n
    simp only [borelTailPerturbation,ite_true,show ¬(1:ℕ)=2 by decide,ite_false,sub_zero]
    positivity
  · by_cases h2 : n=2
    · subst n
      simp only [borelTailPerturbation,h1,ite_false,ite_true,zero_add,add_zero]
      linarith
    · simpa [borelTailPerturbation,h1,h2] using hb

theorem borel_tail_perturbation_nonnegative (n : ℕ) : 0≤borelTailPerturbation n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [borel_tail_perturbation_zero]
  · exact (borel_tail_perturbation_positive n hn).le

theorem borel_tail_perturbation_hasSum : HasSum borelTailPerturbation 1 := by
  have h := (borel_coefficients_summable.hasSum.add
    (hasSum_ite_eq (1:ℕ) (borelCoefficient 2/2))).sub
    (hasSum_ite_eq (2:ℕ) (borelCoefficient 2/2))
  simpa only [borel_coefficients_sum_one,add_sub_cancel_right] using h

def borelTailPerturbationPMF : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal (borelTailPerturbation n), by
    apply ENNReal.summable.hasSum_iff.mpr
    rw [← ENNReal.ofReal_tsum_of_nonneg borel_tail_perturbation_nonnegative
      borel_tail_perturbation_hasSum.summable,borel_tail_perturbation_hasSum.tsum_eq,ENNReal.ofReal_one]⟩

theorem borel_tail_perturbation_eq (n : ℕ) (hn : 3≤n) :
    borelTailPerturbation n=borelCoefficient n := by
  simp [borelTailPerturbation,show n≠1 by omega,show n≠2 by omega]

theorem borel_tail_perturbation_distinct : borelTailPerturbationPMF ≠ borelPMF := by
  intro h
  have he := congrArg (fun p : PMF ℕ => (p 1).toReal) h
  change (ENNReal.ofReal (borelTailPerturbation 1)).toReal=(ENNReal.ofReal (borelCoefficient 1)).toReal at he
  rw [ENNReal.toReal_ofReal (borel_tail_perturbation_nonnegative 1),
    ENNReal.toReal_ofReal (borel_coefficient_nonnegative 1)] at he
  have hb2 : 0<borelCoefficient 2 := borel_coefficient_positive 1
  simp only [borelTailPerturbation,ite_true,show ¬(1:ℕ)=2 by decide,ite_false,sub_zero] at he
  linarith

theorem borel_tail_perturbation_asymptotic :
    (fun n => (borelTailPerturbationPMF n).toReal) ~[atTop] borelTailScale := by
  have he : (fun n => (borelTailPerturbationPMF n).toReal) =ᶠ[atTop] borelCoefficient := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    change (ENNReal.ofReal (borelTailPerturbation n)).toReal=borelCoefficient n
    rw [ENNReal.toReal_ofReal (borel_tail_perturbation_nonnegative n),borel_tail_perturbation_eq n hn]
  exact he.isEquivalent.trans borel_tail_asymptotic

theorem borel_tail_asymptotic_rpow :
    (fun n => (borelPMF n).toReal) ~[atTop]
      (fun n => (2*Real.pi)^(-(1/2:ℝ))*(n:ℝ)^(-(3/2:ℝ))) := by
  have he : borelTailScale =ᶠ[atTop]
      (fun n => (2*Real.pi)^(-(1/2:ℝ))*(n:ℝ)^(-(3/2:ℝ))) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact borel_tail_scale_rpow n hn
  have h := borel_tail_asymptotic.congr_right he
  simpa only [borel_pmf_apply,ENNReal.toReal_ofReal (borel_coefficient_nonnegative _)] using h

theorem borel_tail_perturbation_probability_distinct :
    borelTailPerturbationPMF.toMeasure ≠ borelProbability := by
  intro h
  apply borel_tail_perturbation_distinct
  exact PMF.toMeasure_injective h

/-- Two actual positive-support probability laws with the same exact leading
Borel tail asymptotic, but distinct probabilities at finite sizes. -/
theorem borel_tail_does_not_identify_probability :
    ∃ q : PMF ℕ, q ≠ borelPMF ∧ q 0=0 ∧ (∀ n, 0<q (n+1)) ∧
      (∀ n, 3≤n → q n=borelPMF n) ∧
      ((fun n => (q n).toReal) ~[atTop]
        (fun n => (2*Real.pi)^(-(1/2:ℝ))*(n:ℝ)^(-(3/2:ℝ)))) := by
  refine ⟨borelTailPerturbationPMF,borel_tail_perturbation_distinct,?_,?_,?_,?_⟩
  · change ENNReal.ofReal (borelTailPerturbation 0)=0
    rw [borel_tail_perturbation_zero,ENNReal.ofReal_zero]
  · intro n
    exact ENNReal.ofReal_pos.mpr (borel_tail_perturbation_positive (n+1) (by omega))
  · intro n hn
    change ENNReal.ofReal (borelTailPerturbation n)=ENNReal.ofReal (borelCoefficient n)
    rw [borel_tail_perturbation_eq n hn]
  · apply borel_tail_perturbation_asymptotic.congr_right
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact borel_tail_scale_rpow n hn

end
end Sigma
