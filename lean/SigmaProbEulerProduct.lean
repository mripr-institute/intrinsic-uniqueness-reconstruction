import SigmaProbEuler
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.ZetaValues

namespace Sigma
noncomputable section
open Filter
open scoped Topology BigOperators

def eulerLogGammaTerm (s : ℝ) (k : ℕ) : ℝ :=
  -Real.log (1-s/((k:ℝ)+1))-s/((k:ℝ)+1)

theorem euler_log_gamma_term_nonneg (s : ℝ) (hs : s<1) (k : ℕ) :
    0 ≤ eulerLogGammaTerm s k := by
  have hk : 0 < (k:ℝ)+1 := by positivity
  have hpos : 0 < 1-s/((k:ℝ)+1) := by
    have hn : 0 ≤ (k:ℝ) := by positivity
    have he := (div_lt_one hk).mpr (show s<(k:ℝ)+1 by linarith)
    linarith
  have h := Real.log_le_sub_one_of_pos hpos
  unfold eulerLogGammaTerm
  linarith

theorem euler_log_gamma_partial (s : ℝ) (hs : s<1) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), eulerLogGammaTerm s k) =
      Real.BohrMollerup.logGammaSeq (1-s) n-Real.BohrMollerup.logGammaSeq 1 n+
        s*(Real.log n-(harmonic (n+1):ℝ)) := by
  have he (k : ℕ) : eulerLogGammaTerm s k=
      Real.log (1+(k:ℝ))-Real.log (1-s+(k:ℝ))-s*(1+(k:ℝ))⁻¹ := by
    have hk : 0 < 1+(k:ℝ) := by positivity
    have hsk : 0 < 1-s+(k:ℝ) := by
      have hn : 0 ≤ (k:ℝ) := by positivity
      linarith
    have hd : 1-s/((k:ℝ)+1)=(1-s+(k:ℝ))/(1+(k:ℝ)) := by field_simp; ring
    rw [eulerLogGammaTerm, hd, Real.log_div hsk.ne' hk.ne']
    simp only [div_eq_mul_inv]
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, harmonic_real_sum]
  unfold Real.BohrMollerup.logGammaSeq
  ring

/-- Euler's log-Gamma product as an actual convergent infinite sum. The
convergence follows from the proved Gamma limit, not from a formal identity. -/
theorem log_gamma_euler_product (s : ℝ) (hs : s<1) :
    HasSum (eulerLogGammaTerm s)
      (Real.log (Real.Gamma (1-s))-Real.eulerMascheroniConstant*s) := by
  have h := ((Real.BohrMollerup.tendsto_log_gamma (by linarith : 0<1-s)).sub
    (Real.BohrMollerup.tendsto_log_gamma (by norm_num : (0:ℝ)<1))).add
    (harmonic_log_slope_tendsto.const_mul s)
  have ht : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n+1), eulerLogGammaTerm s k)
      atTop (𝓝 (Real.log (Real.Gamma (1-s))-Real.eulerMascheroniConstant*s)) := by
    simp only [Real.Gamma_one, Real.log_one, sub_zero] at h
    convert h using 1
    · funext n
      exact euler_log_gamma_partial s hs n
    · congr 1
      ring
  apply (hasSum_iff_tendsto_nat_of_nonneg (euler_log_gamma_term_nonneg s hs) _).mpr
  exact (tendsto_add_atTop_iff_nat 1).mp ht

def eulerLogGammaDoubleTerm (s : ℝ) (k n : ℕ) : ℝ :=
  (s/((k:ℝ)+1))^(n+2)/((n:ℝ)+2)

theorem euler_log_gamma_term_series (s : ℝ) (hs : |s|<1) (k : ℕ) :
    HasSum (eulerLogGammaDoubleTerm s k) (eulerLogGammaTerm s k) := by
  have hk : 0 < (k:ℝ)+1 := by positivity
  have hx : |s/((k:ℝ)+1)|<1 := by
    rw [abs_div, abs_of_pos hk]
    apply (div_lt_one hk).mpr
    have hn : 0 ≤ (k:ℝ) := by positivity
    linarith
  have h := (hasSum_nat_add_iff' 1).mpr (Real.hasSum_pow_div_log_of_abs_lt_one hx)
  change HasSum (fun n : ℕ => (s/((k:ℝ)+1))^(n+2)/((n:ℝ)+2)) (eulerLogGammaTerm s k)
  simpa [eulerLogGammaTerm,Nat.cast_add,Nat.cast_one, add_assoc,
    show (1:ℝ)+1=2 by norm_num] using h

/-- Absolute convergence of the double Euler/logarithm expansion, including
negative arguments. The positive product at |s| controls the full double sum. -/
theorem euler_log_gamma_double_summable (s : ℝ) (hs : |s|<1) :
    Summable (fun kn : ℕ×ℕ => eulerLogGammaDoubleTerm s kn.1 kn.2) := by
  have ha : abs (abs s)<1 := by simpa using hs
  have hp : Summable (fun kn : ℕ×ℕ => eulerLogGammaDoubleTerm |s| kn.1 kn.2) := by
    apply (summable_prod_of_nonneg (fun kn => by
      unfold eulerLogGammaDoubleTerm
      positivity)).mpr
    constructor
    · intro k
      exact (euler_log_gamma_term_series |s| ha k).summable
    · simpa only [(euler_log_gamma_term_series |s| ha _).tsum_eq] using
        (log_gamma_euler_product |s| hs).summable
  apply Summable.of_norm
  convert hp using 1
  funext kn
  simp [eulerLogGammaDoubleTerm,Real.norm_eq_abs,abs_div,abs_pow,
    abs_of_nonneg (show 0 ≤ (kn.1:ℝ)+1 by positivity),
    abs_of_nonneg (show 0 ≤ (kn.2:ℝ)+2 by positivity)]

end
end Sigma
