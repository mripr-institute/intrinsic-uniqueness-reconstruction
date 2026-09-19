import SigmaAutomorphisms
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Sigma
noncomputable section
open Set

def starN : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n+1, x => star (starN n x) x

theorem starN_domain {n : ℕ} {x : ℝ} (hx : -1 < x) :
    -1 < starN n x := by
  induction n with
  | zero => norm_num [starN]
  | succ n ih =>
      rw [starN]
      exact SigmaBase.star_closed ih hx

theorem groupPower_nat_nseries {n : ℕ} {x : ℝ} (hx : -1 < x) :
    starN n x = groupPower (n : ℝ) x := by
  induction n with
  | zero => simp [starN, groupPower]
  | succ n ih =>
      rw [starN, ih]
      unfold groupPower
      have hpos : 0 < 1+x := by linarith
      rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by norm_num,
        add_mul, Real.exp_add]
      simp only [one_mul, Real.exp_log hpos]
      unfold star SigmaBase.star
      ring

theorem groupPower_nat_nseries_hom {n : ℕ} {x y : ℝ}
    (hx : -1 < x) (hy : -1 < y) :
    groupPower (n : ℝ) (star x y) =
      star (groupPower (n : ℝ) x) (groupPower (n : ℝ) y) :=
  groupPower_hom (n : ℝ) hx hy

theorem groupPower_rpow (c x : ℝ) (hx : -1 < x) :
    groupPower c x=(1+x)^c-1 := by
  rw [Real.rpow_def_of_pos (by linarith : 0 < 1+x)]
  simp only [groupPower, mul_comm]

/-- Negative integer repetition is the group inverse of positive repetition. -/
def starZ : ℤ → ℝ → ℝ
  | .ofNat n, x => starN n x
  | .negSucc n, x => SigmaBase.invStar (starN (n+1) x)

theorem groupPower_neg (c x : ℝ) :
    groupPower (-c) x=SigmaBase.invStar (groupPower c x) := by
  unfold groupPower SigmaBase.invStar
  rw [neg_mul, Real.exp_neg]
  have hp := (Real.exp_pos (c*Real.log (1+x))).ne'
  field_simp

theorem groupPower_int_nseries (n : ℤ) (x : ℝ) (hx : -1 < x) :
    starZ n x=groupPower (n : ℝ) x := by
  cases n with
  | ofNat n => exact groupPower_nat_nseries hx
  | negSucc n =>
      rw [starZ, groupPower_nat_nseries hx, Int.cast_negSucc, ← groupPower_neg]

theorem starZ_formula (n : ℤ) (x : ℝ) (hx : -1 < x) :
    starZ n x=(1+x)^n-1 := by
  rw [groupPower_int_nseries n x hx, groupPower_rpow _ _ hx, Real.rpow_intCast]

theorem starZ_domain (n : ℤ) (x : ℝ) (hx : -1 < x) : -1 < starZ n x := by
  rw [groupPower_int_nseries n x hx]
  exact groupPower_closed _ _

theorem starZ_composition (m n : ℤ) (x : ℝ) (hx : -1 < x) :
    starZ m (starZ n x)=starZ (m*n) x := by
  rw [groupPower_int_nseries _ _ (starZ_domain n x hx),
    groupPower_int_nseries n x hx, groupPower_composition,
    groupPower_int_nseries _ x hx, Int.cast_mul]

theorem groupPower_hasDerivAt_zero (c : ℝ) : HasDerivAt (groupPower c) c 0 := by
  have hh := ((((hasDerivAt_id (0 : ℝ)).const_add 1).log (by norm_num)).const_mul c).exp.sub_const 1
  simpa [groupPower] using hh

theorem groupPower_calibration (c : ℝ) : deriv (groupPower c) 0=1 ↔ c=1 := by
  rw [(groupPower_hasDerivAt_zero c).deriv]

end
end Sigma
