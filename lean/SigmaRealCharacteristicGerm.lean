import SigmaRealFormalGerm
import SigmaRealCharacteristicAnalytic
import SigmaRealCharacteristicChi

namespace Sigma
noncomputable section
open PowerSeries Filter
open scoped Topology

theorem real_todd_denominator_formal_germ :
    HasRealFormalGerm realToddDenominator (toddDenominator ℝ) := by
  have h := real_formal_germ_sub (real_formal_germ_const 1) (real_formal_germ_exp (-1))
  have hh := real_formal_germ_dslope h
  simpa only [map_one, neg_one_mul, realToddDenominator, toddDenominator] using hh

/-- The global real Todd quotient realizes exactly the independently
constructed formal Todd series. Its analyticity alone is not used as a proxy
for this coefficient identification: multiplication of the actual analytic
germs recovers the formal denominator identity, which determines the unit. -/
theorem real_todd_formal_germ : HasRealFormalGerm realTodd (formalTodd ℝ) := by
  obtain ⟨F,hF⟩ := analytic_has_real_formal_germ realTodd (real_todd_analytic 0)
  have hmul := real_formal_germ_mul real_todd_denominator_formal_germ hF
  have he : (fun x => realToddDenominator x*realTodd x)=(fun _ : ℝ => 1) := by
    funext x
    exact mul_inv_cancel₀ (real_todd_denominator_nonzero x)
  rw [he] at hmul
  have heq : toddDenominator ℝ*F=1 := by
    simpa using real_formal_germ_unique hmul (real_formal_germ_const 1)
  have hFid : F=formalTodd ℝ := by
    apply mul_left_cancel₀ (show toddDenominator ℝ ≠ 0 from ?_)
    · exact heq.trans (todd_denominator_mul_todd ℝ).symm
    · intro h
      have hh := congrArg (constantCoeff ℝ) h
      simp [todd_denominator_constant] at hh
  rwa [hFid] at hF

theorem real_ahat_formal_germ : HasRealFormalGerm realAhat (formalAhat ℝ) := by
  have h := real_formal_germ_mul (real_formal_germ_exp (-(1/2))) real_todd_formal_germ
  rw [formal_todd_to_ahat] at h
  convert h using 1
  funext x
  unfold realAhat
  congr 2
  ring

theorem real_lgenus_formal_germ : HasRealFormalGerm realLgenus (formalL ℝ) := by
  rw [formal_todd_to_L]
  exact real_formal_germ_sub (real_formal_germ_rescale real_todd_formal_germ 2) real_formal_germ_X

theorem real_chi_formal_germ (y : ℝ) : HasRealFormalGerm (realChi y) (formalChi ℝ y) := by
  have hl := real_formal_germ_mul (real_formal_germ_const y) real_formal_germ_X
  exact real_formal_germ_sub (real_formal_germ_rescale real_todd_formal_germ (1+y)) hl

theorem real_characteristic_inverse_formal_germs :
    HasRealFormalGerm (fun u => (realTodd u)⁻¹) (formalTodd ℝ)⁻¹ ∧
      HasRealFormalGerm (fun u => (realAhat u)⁻¹) (formalAhat ℝ)⁻¹ ∧
      HasRealFormalGerm (fun u => (realLgenus u)⁻¹) (formalL ℝ)⁻¹ ∧
      ∀ y, HasRealFormalGerm (fun u => (realChi y u)⁻¹) (formalChi ℝ y)⁻¹ := by
  refine ⟨real_formal_germ_inv real_todd_formal_germ (by rw [real_todd_zero]; norm_num),
    real_formal_germ_inv real_ahat_formal_germ ?_,
    real_formal_germ_inv real_lgenus_formal_germ ?_, fun y =>
    real_formal_germ_inv (real_chi_formal_germ y) ?_⟩
  · rw [real_characteristic_zero.1]; norm_num
  · rw [real_characteristic_zero.2.1]; norm_num
  · rw [real_characteristic_zero.2.2 y]; norm_num

/-- An independently supplied analytic function with these formal
coefficients agrees globally on any connected domain containing zero.
Neither the supplied function nor its global values are defined from the
canonical representative. -/
theorem real_formal_germ_global_recovery {f g : ℝ → ℝ} {F : PowerSeries ℝ}
    {U : Set ℝ} (hf : HasRealFormalGerm f F) (hg : HasRealFormalGerm g F)
    (hfU : AnalyticOnNhd ℝ f U) (hgU : AnalyticOnNhd ℝ g U)
    (hU : IsPreconnected U) (h0 : 0 ∈ U) : Set.EqOn f g U := by
  apply real_analytic_global_recovery hfU hgU hU h0
  filter_upwards [(real_formal_germ_iff _ _).mp hf,
    (real_formal_germ_iff _ _).mp hg] with x hx hy
  exact hx.unique hy

end
end Sigma
