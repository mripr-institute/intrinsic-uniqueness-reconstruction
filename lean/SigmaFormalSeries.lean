import SigmaPresentations
import Mathlib.RingTheory.PowerSeries.Derivative

/-! Genuine formal power-series coefficient uniqueness over ℚ.
Todd existence and the residue identity are not assumed or asserted here.
-/
namespace SigmaPresentations
noncomputable section
open PowerSeries

/-- If two unit series agree below n, their kth powers differ in degree n
by k times their degree-n difference. This proves triangularity rather than
taking it as a hypothesis. -/
theorem coefficient_power_difference (F G : PowerSeries ℚ)
    (hF : constantCoeff ℚ F = 1) (hG : constantCoeff ℚ G = 1)
    (n k : ℕ) (hlow : ∀ m < n, coeff ℚ m F = coeff ℚ m G) :
    coeff ℚ n (F ^ k - G ^ k) =
      (k : ℚ) * (coeff ℚ n F - coeff ℚ n G) := by
  have hdvd : (X : PowerSeries ℚ) ^ n ∣ F - G := by
    apply X_pow_dvd_iff.mpr
    intro m hm
    simp [hlow m hm]
  obtain ⟨D, hD⟩ := hdvd
  have hc : coeff ℚ n (F - G) = constantCoeff ℚ D := by
    rw [hD]
    simpa using coeff_X_pow_mul D n 0
  let S : PowerSeries ℚ := ∑ i ∈ Finset.range k, F ^ i * G ^ (k - 1 - i)
  have hS : constantCoeff ℚ S = (k : ℚ) := by
    simp [S, hF, hG]
  calc
    coeff ℚ n (F ^ k - G ^ k) = coeff ℚ n (X ^ n * (D * S)) := by
      congr 1
      rw [← (Commute.all F G).mul_geom_sum₂ k, hD]
      simp only [S]
      ring
    _ = constantCoeff ℚ (D * S) := by
      simpa using coeff_X_pow_mul (D * S) n 0
    _ = (k : ℚ) * (coeff ℚ n F - coeff ℚ n G) := by
      rw [map_mul, hS, ← hc, map_sub]
      ring

/-- The complete k=0 Todd coefficient tower has at most one normalized solution. -/
theorem todd_tower_unique (F G : PowerSeries ℚ)
    (hF : constantCoeff ℚ F = 1) (hG : constantCoeff ℚ G = 1)
    (hFtower : ∀ n > 0, coeff ℚ n (F ^ (n + 1)) = 1)
    (hGtower : ∀ n > 0, coeff ℚ n (G ^ (n + 1)) = 1) : F = G := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa using hF.trans hG.symm
    · have hd := coefficient_power_difference F G hF hG n (n + 1) ih
      have hpos : 0 < n := Nat.pos_of_ne_zero hn
      rw [map_sub, hFtower n hpos, hGtower n hpos, sub_self] at hd
      have hk : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      exact sub_eq_zero.mp ((mul_eq_zero.mp hd.symm).resolve_left hk)

/-- Even without prescribed right sides, equality of all tower observations
identifies the complete normalized series. -/
theorem todd_observations_injective (F G : PowerSeries ℚ)
    (hF : constantCoeff ℚ F = 1) (hG : constantCoeff ℚ G = 1)
    (hobs : ∀ n > 0, coeff ℚ n (F ^ (n + 1)) = coeff ℚ n (G ^ (n + 1))) :
    F = G := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa using hF.trans hG.symm
    · have hd := coefficient_power_difference F G hF hG n (n + 1) ih
      rw [map_sub, hobs n (Nat.pos_of_ne_zero hn), sub_self] at hd
      have hk : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      exact sub_eq_zero.mp ((mul_eq_zero.mp hd.symm).resolve_left hk)

/-- Uniqueness for the normalized formal logarithm's differential equation.
Derivation of that equation from a two-variable formal group law is separate. -/
theorem normalized_formal_log_ode_unique (F G : PowerSeries ℚ)
    (hzero : constantCoeff ℚ F = constantCoeff ℚ G)
    (hF : (1 + X) * PowerSeries.derivative ℚ F = 1)
    (hG : (1 + X) * PowerSeries.derivative ℚ G = 1) : F = G := by
  apply PowerSeries.derivative.ext _ hzero
  apply mul_left_cancel₀ (show (1 + X : PowerSeries ℚ) ≠ 0 from ?_)
  · exact hF.trans hG.symm
  · intro hz
    have hc := congrArg (constantCoeff ℚ) hz
    norm_num at hc

def formalLog : PowerSeries ℚ := PowerSeries.mk fun n =>
  match n with
  | 0 => 0
  | n + 1 => (-1 : ℚ) ^ n / ((n + 1 : ℕ) : ℚ)

theorem formalLog_constant : constantCoeff ℚ formalLog = 0 := by
  simp [formalLog]

theorem formalLog_derivative_coeff (n : ℕ) :
    coeff ℚ n (PowerSeries.derivative ℚ formalLog) = (-1 : ℚ) ^ n := by
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  simp [coeff_derivative, formalLog, hn]

theorem formalLog_ode :
    (1 + X) * PowerSeries.derivative ℚ formalLog = 1 := by
  apply PowerSeries.ext
  intro n
  rw [add_mul, one_mul, map_add]
  cases n with
  | zero =>
    rw [formalLog_derivative_coeff]
    simp
  | succ n =>
    rw [coeff_succ_X_mul, formalLog_derivative_coeff, formalLog_derivative_coeff]
    simp [coeff_one, pow_succ]

theorem normalized_formal_log_ode_reconstruction (F : PowerSeries ℚ)
    (hzero : constantCoeff ℚ F = 0)
    (hF : (1 + X) * PowerSeries.derivative ℚ F = 1) : F = formalLog := by
  exact normalized_formal_log_ode_unique F formalLog
    (hzero.trans formalLog_constant.symm) hF formalLog_ode

/-- The constant-one mark removes the second branch of the A-hat quadratic. -/
theorem formal_unit_quadratic_branch_unique (W V B : PowerSeries ℚ)
    (hW : constantCoeff ℚ W = 1) (hV : constantCoeff ℚ V = 1)
    (hB : constantCoeff ℚ B = 0)
    (hWeq : W ^ 2 - B * W = 1) (hVeq : V ^ 2 - B * V = 1) : W = V := by
  have hp : (W - V) * (W + V - B) = 0 := by
    linear_combination hWeq - hVeq
  have hn : W + V - B ≠ 0 := by
    intro hz
    have hc := congrArg (constantCoeff ℚ) hz
    norm_num [hW, hV, hB] at hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hn)

end
end SigmaPresentations
