import SigmaAutomorphisms

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

end
end Sigma
