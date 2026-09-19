import SigmaProbEulerProduct
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace Sigma
noncomputable section
open Filter
open scoped Topology BigOperators

def naturalZeta (n : ℕ) : ℝ := ∑' k : ℕ, 1/((k:ℝ)+1)^n

theorem natural_zeta_summable (n : ℕ) (hn : 1<n) :
    Summable (fun k : ℕ => 1/((k:ℝ)+1)^n) := by
  simpa only [Nat.cast_add,Nat.cast_one] using
    (summable_nat_add_iff 1 (f := fun k : ℕ => 1/(k:ℝ)^n)).mpr (Real.summable_one_div_nat_pow.mpr hn)

theorem natural_zeta_riemann (n : ℕ) (hn : 1<n) :
    (naturalZeta n : ℂ)=riemannZeta n := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by exact_mod_cast hn : 1<(n:ℂ).re)]
  rw [naturalZeta, Complex.ofReal_tsum]
  apply tsum_congr
  intro k
  simp [Complex.cpow_natCast]

theorem euler_log_gamma_column (s : ℝ) (n : ℕ) :
    (∑' k, eulerLogGammaDoubleTerm s k n)=naturalZeta (n+2)*s^(n+2)/((n:ℝ)+2) := by
  simp only [eulerLogGammaDoubleTerm,div_pow]
  have he (k : ℕ) : s^(n+2)/((k:ℝ)+1)^(n+2)/((n:ℝ)+2)=
      (1/((k:ℝ)+1)^(n+2))*(s^(n+2)/((n:ℝ)+2)) := by ring
  simp_rw [he]
  rw [tsum_mul_right,naturalZeta]
  ring

/-- The convergent Euler/zeta expansion of log Gamma on |s|<1. Its double
sum exchange is justified by absolute convergence proved independently. -/
theorem log_gamma_zeta_series (s : ℝ) (hs : |s|<1) :
    HasSum (fun n : ℕ => naturalZeta (n+2)*s^(n+2)/((n:ℝ)+2))
      (Real.log (Real.Gamma (1-s))-Real.eulerMascheroniConstant*s) := by
  have hd := euler_log_gamma_double_summable s hs
  have hrow : (∑' k, ∑' n, eulerLogGammaDoubleTerm s k n)=
      Real.log (Real.Gamma (1-s))-Real.eulerMascheroniConstant*s := by
    simp_rw [(euler_log_gamma_term_series s hs _).tsum_eq]
    exact (log_gamma_euler_product s (lt_of_le_of_lt (le_abs_self s) hs)).tsum_eq
  have hcol := hd.prod_symm.prod.hasSum
  change HasSum (fun n => ∑' k, eulerLogGammaDoubleTerm s k n)
    (∑' n, ∑' k, eulerLogGammaDoubleTerm s k n) at hcol
  rw [tsum_comm (f := eulerLogGammaDoubleTerm s) hd] at hcol
  rw [hrow] at hcol
  simpa only [euler_log_gamma_column] using hcol

end
end Sigma
