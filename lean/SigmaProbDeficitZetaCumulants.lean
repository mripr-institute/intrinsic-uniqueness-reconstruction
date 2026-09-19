import SigmaProbDeficitCGFSeries
import SigmaRealFormalGerm

namespace Sigma
noncomputable section
open MeasureTheory Filter PowerSeries
open scoped Topology BigOperators

def deficitCGFCoeff : ℕ → ℝ
  | 0 => 0
  | 1 => Real.eulerMascheroniConstant
  | n+2 => (naturalZeta (n+2)-1/((n:ℝ)+1))/((n:ℝ)+2)

def deficitCGFFormal : PowerSeries ℝ := PowerSeries.mk deficitCGFCoeff

theorem deficit_cgf_full_series (s : ℝ) (hs : |s|<1) :
    HasSum (fun n => deficitCGFCoeff n*s^n) (probabilityCGF gammaDeficitProbability s) := by
  apply (hasSum_nat_add_iff' 2).mp
  simpa [deficitCGFCoeff,Finset.sum_range_succ,probabilityCGF,div_mul_eq_mul_div] using
    deficit_cgf_zeta_series s hs

theorem deficit_cgf_formal_germ :
    HasRealFormalGerm (probabilityCGF gammaDeficitProbability) deficitCGFFormal := by
  apply (real_formal_germ_iff _ _).mpr
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1)] with s hs
  simpa only [deficitCGFFormal,coeff_mk] using
    deficit_cgf_full_series s (by simpa [Real.dist_eq] using hs)

theorem deficit_cumulant_coeff (n : ℕ) :
    probabilityCumulant gammaDeficitProbability n=(n.factorial:ℝ)*deficitCGFCoeff n := by
  obtain ⟨r,hr⟩ := deficit_cgf_formal_germ
  have h := hr.factorial_smul (1:ℝ) n
  simpa [probabilityCumulant,iteratedDeriv,deficitCGFFormal,
    FormalMultilinearSeries.ofScalars,coeff_mk, nsmul_eq_mul] using h.symm

theorem deficit_cumulant_one :
    probabilityCumulant gammaDeficitProbability 1=Real.eulerMascheroniConstant := by
  simp [deficit_cumulant_coeff,deficitCGFCoeff]

theorem deficit_cumulant_zeta (n : ℕ) :
    probabilityCumulant gammaDeficitProbability (n+2)=
      ((n+1).factorial:ℝ)*(naturalZeta (n+2)-1/((n:ℝ)+1)) := by
  rw [deficit_cumulant_coeff,deficitCGFCoeff,Nat.factorial_succ]
  push_cast
  have hn : (n:ℝ)+2 ≠ 0 := by positivity
  field_simp
  ring

theorem natural_zeta_two : naturalZeta 2=Real.pi^2/6 := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa [naturalZeta] using h.tsum_eq

theorem natural_zeta_four : naturalZeta 4=Real.pi^4/90 := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_four
  simpa [naturalZeta] using h.tsum_eq

theorem deficit_cumulants_two_three_four :
    probabilityCumulant gammaDeficitProbability 2=Real.pi^2/6-1 ∧
      probabilityCumulant gammaDeficitProbability 3=2*naturalZeta 3-1 ∧
      probabilityCumulant gammaDeficitProbability 4=Real.pi^4/15-2 := by
  have h2 := deficit_cumulant_zeta 0
  have h3 := deficit_cumulant_zeta 1
  have h4 := deficit_cumulant_zeta 2
  norm_num [natural_zeta_two,natural_zeta_four,Nat.factorial] at h2 h3 h4
  constructor
  · exact h2
  constructor <;> linarith

end
end Sigma
