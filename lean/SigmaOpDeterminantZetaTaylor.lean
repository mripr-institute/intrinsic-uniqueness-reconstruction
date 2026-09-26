import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.LocallyUniformLimit

namespace Sigma
noncomputable section
open Set
open scoped Topology

/-- A first-order Taylor remainder bound obtained by applying the mean value inequality twice. -/
theorem zeta_norm_taylor_one_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g h : ℝ → E) (a b C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ t ∈ Set.uIcc a b, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Set.uIcc a b, HasDerivAt g (h t) t)
    (hb : ∀ t ∈ Set.uIcc a b, ‖h t‖ ≤ C) :
    ‖f b - f a - (b-a) • g a‖ ≤ C * |b-a|^2 := by
  have hg' (t : ℝ) (ht : t ∈ Set.uIcc a b) : ‖g t - g a‖ ≤ C * |b-a| := by
    have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hg x hx).hasDerivWithinAt) hb (convex_Icc (min a b) (max a b))
      (Set.left_mem_uIcc : a ∈ Set.uIcc a b) ht
    have ht' : |t-a| ≤ |b-a| := by
      change min a b ≤ t ∧ t ≤ max a b at ht
      rcases le_total a b with hab | hba
      · rw [min_eq_left hab, max_eq_right hab] at ht
        rw [abs_of_nonneg (sub_nonneg.mpr ht.1), abs_of_nonneg (sub_nonneg.mpr hab)]
        linarith
      · rw [min_eq_right hba, max_eq_left hba] at ht
        rw [abs_of_nonpos (sub_nonpos.mpr ht.2), abs_of_nonpos (sub_nonpos.mpr hba)]
        linarith
    exact hh.trans (mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using ht') hC)
  have hF (t : ℝ) (ht : t ∈ Set.uIcc a b) :
      HasDerivAt (fun t : ℝ => f t - f a - (t-a) • g a) (g t - g a) t := by
    simpa only [one_smul] using ((hf t ht).sub_const (f a)).sub
      (((hasDerivAt_id t).sub_const a).smul_const (g a))
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hF x hx).hasDerivWithinAt) hg' (convex_Icc (min a b) (max a b))
    (Set.left_mem_uIcc : a ∈ Set.uIcc a b) (Set.right_mem_uIcc : b ∈ Set.uIcc a b)
  simpa only [sub_self, zero_smul, sub_zero, Real.norm_eq_abs, pow_two, mul_assoc] using hh

theorem positive_real_complex_power_hasDerivAt (s : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (x : ℂ)^s) (s*(x : ℂ)^(s-1)) x := by
  simpa only [mul_one] using
    ((hasDerivAt_id (x : ℂ)).cpow_const (Complex.ofReal_mem_slitPlane.mpr hx)).comp_ofReal

/-- Uniform second-order decay for the regularized shifted Dirichlet-series term. -/
theorem zeta_power_taylor_bound (s : ℂ) (x y L R : ℝ)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hL : -1 < L) (hs : L ≤ s.re) (hR : ‖s‖ ≤ R) :
    ‖(y : ℂ)^(-s) - (x : ℂ)^(-s) + s * (x : ℂ)^(-s-1) * (y-x : ℝ)‖ ≤
      R*(R+1) * (min x y)^(-L-2) * |y-x|^2 := by
  have hR0 : 0 ≤ R := (norm_nonneg s).trans hR
  let f : ℝ → ℂ := fun t => (t : ℂ)^(-s)
  let g : ℝ → ℂ := fun t => -s * (t : ℂ)^(-s-1)
  let h : ℝ → ℂ := fun t => s*(s+1) * (t : ℂ)^(-s-2)
  have htpos (t : ℝ) (ht : t ∈ Set.uIcc x y) : 0 < t := by
    have hh : 1 ≤ min x y := le_min hx hy
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hh.trans ht.1)
  have hf (t : ℝ) (ht : t ∈ Set.uIcc x y) : HasDerivAt f (g t) t :=
    positive_real_complex_power_hasDerivAt (-s) t (htpos t ht)
  have hg (t : ℝ) (ht : t ∈ Set.uIcc x y) : HasDerivAt g (h t) t := by
    have hd := (positive_real_complex_power_hasDerivAt (-s-1) t (htpos t ht)).const_mul (-s)
    convert hd using 1
    dsimp [h]
    rw [show -s-1-1 = -s-2 by ring]
    ring
  have hb (t : ℝ) (ht : t ∈ Set.uIcc x y) :
      ‖h t‖ ≤ R*(R+1) * (min x y)^(-L-2) := by
    have hm : 1 ≤ min x y := le_min hx hy
    have hm0 : 0 < min x y := by linarith
    have hp := Real.rpow_le_rpow_of_nonpos hm0 ht.1 (by linarith : -s.re-2 ≤ 0)
    have he := Real.rpow_le_rpow_of_exponent_le hm (by linarith : -s.re-2 ≤ -L-2)
    have hn : ‖s+1‖ ≤ R+1 := (norm_add_le s 1).trans (by simpa using add_le_add_right hR 1)
    change ‖s*(s+1)*(t : ℂ)^(-s-2)‖ ≤ _
    rw [norm_mul, norm_mul, Complex.norm_eq_abs ((t : ℂ)^(-s-2)),
      Complex.abs_cpow_eq_rpow_re_of_pos (htpos t ht)]
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]
    exact mul_le_mul (mul_le_mul hR hn (norm_nonneg _) hR0) (hp.trans he)
      (Real.rpow_nonneg (htpos t ht).le _) (mul_nonneg hR0 (by linarith))
  have hC : 0 ≤ R*(R+1) * (min x y)^(-L-2) := by positivity
  have hh := zeta_norm_taylor_one_le f g h x y _ hC hf hg hb
  convert hh using 1
  congr 1
  simp only [f, g, Complex.real_smul]
  push_cast
  ring

end
end Sigma
