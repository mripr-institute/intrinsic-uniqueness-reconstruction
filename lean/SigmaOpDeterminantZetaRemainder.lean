import SigmaOpDeterminantZetaTaylor
import SigmaProbEulerProduct
import Mathlib.Analysis.Complex.Convex

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology BigOperators

/-- The second-order corrected shifted spectral term. -/
def zetaRegularTerm (a : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  ((n : ℂ)+(a : ℂ))^(-s) - ((n : ℂ)+1)^(-s) +
    s*((a : ℂ)-1)*((n : ℂ)+1)^(-s-1)

theorem zeta_regular_term_differentiable (a : ℝ) (ha : 0 < a) (n : ℕ) :
    Differentiable ℂ (zetaRegularTerm a n) := by
  have hn : (n : ℂ)+(a : ℂ) ≠ 0 := by
    exact_mod_cast (show ((n : ℝ)+a) ≠ 0 by positivity)
  have hn1 : (n : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  exact ((differentiable_id.neg.const_cpow (Or.inl hn)).sub
    (differentiable_id.neg.const_cpow (Or.inl hn1))).add
    ((differentiable_id.mul_const _).mul
      ((differentiable_id.neg.sub_const 1).const_cpow (Or.inl hn1)))

theorem zeta_regular_term_tail_bound (a : ℝ) (ha : 0 < a) (n : ℕ) (s : ℂ)
    (hs : -(1/2 : ℝ) ≤ s.re) (hnorm : ‖s‖ ≤ 4) :
    ‖zetaRegularTerm a (n+1) s‖ ≤ 20*|a-1|^2 * ((n : ℝ)+1)^(-(3/2 : ℝ)) := by
  have hx : 1 ≤ (n : ℝ)+2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hy : 1 ≤ (n : ℝ)+1+a := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have h := zeta_power_taylor_bound s ((n : ℝ)+2) ((n : ℝ)+1+a) (-(1/2)) 4
    hx hy (by norm_num) hs hnorm
  have hmin : (n : ℝ)+1 ≤ min ((n : ℝ)+2) ((n : ℝ)+1+a) := by
    apply le_min <;> linarith
  have he := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (n : ℝ)+1)
    hmin (by norm_num : -(3/2 : ℝ) ≤ 0)
  have hsub : ((n : ℝ)+1+a)-((n : ℝ)+2) = a-1 := by ring
  norm_num only [show -( -(1/2 : ℝ))-2 = -(3/2 : ℝ) by norm_num,
    show (4 : ℝ)*(4+1)=20 by norm_num] at h
  rw [hsub] at h
  have ht : (((n : ℝ)+1+a : ℝ) : ℂ)^(-s) - (((n : ℝ)+2 : ℝ) : ℂ)^(-s) +
      s*(((n : ℝ)+2 : ℝ) : ℂ)^(-s-1)*(a-1 : ℝ) = zetaRegularTerm a (n+1) s := by
    simp only [zetaRegularTerm]
    push_cast
    ring
  rw [ht] at h
  calc
    _ ≤ 20 * (min ((n : ℝ)+2) ((n : ℝ)+1+a))^(-(3/2 : ℝ)) * |a-1|^2 := h
    _ ≤ 20 * ((n : ℝ)+1)^(-(3/2 : ℝ)) * |a-1|^2 := by gcongr
    _ = _ := by ring

def zetaRegularSeries (a : ℝ) (s : ℂ) : ℂ :=
  zetaRegularTerm a 0 s + ∑' n : ℕ, zetaRegularTerm a (n+1) s

def zetaRegularRegion : Set ℂ := {s | -(1/2 : ℝ) < s.re ∧ ‖s‖ < 4}

theorem zeta_regular_region_open : IsOpen zetaRegularRegion :=
  (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_norm continuous_const)

theorem zeta_regular_region_zero : (0 : ℂ) ∈ zetaRegularRegion := by
  norm_num [zetaRegularRegion]

theorem zeta_regular_majorant_summable (a : ℝ) :
    Summable (fun n : ℕ => 20*|a-1|^2 * ((n : ℝ)+1)^(-(3/2 : ℝ))) := by
  have h := (summable_nat_add_iff 1 (f := fun n : ℕ => (n : ℝ)^(-(3/2 : ℝ)))).mpr
    (Real.summable_nat_rpow.mpr (by norm_num))
  simpa only [Nat.cast_add, Nat.cast_one] using h.mul_left (20*|a-1|^2)

theorem zeta_regular_series_differentiableOn (a : ℝ) (ha : 0 < a) :
    DifferentiableOn ℂ (zetaRegularSeries a) zetaRegularRegion := by
  exact (zeta_regular_term_differentiable a ha 0).differentiableOn.add
    (Complex.differentiableOn_tsum_of_summable_norm (zeta_regular_majorant_summable a)
      (fun n => (zeta_regular_term_differentiable a ha (n+1)).differentiableOn)
      zeta_regular_region_open (fun n s hs => zeta_regular_term_tail_bound a ha n s hs.1.le hs.2.le))

theorem zeta_regular_term_deriv_zero (a : ℝ) (ha : 0 < a) (n : ℕ) :
    deriv (zetaRegularTerm a n) 0 = (eulerLogGammaTerm (1-a) n : ℂ) := by
  have hn : (n : ℂ)+(a : ℂ) ≠ 0 := by
    exact_mod_cast (show ((n : ℝ)+a) ≠ 0 by positivity)
  have hn1 : (n : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h0 := (hasDerivAt_id (0 : ℂ)).neg
  have hd := ((h0.const_cpow (Or.inl hn)).sub (h0.const_cpow (Or.inl hn1))).add
    (((hasDerivAt_id (0 : ℂ)).mul_const ((a : ℂ)-1)).mul
      ((h0.sub_const 1).const_cpow (Or.inl hn1)))
  have hp : 0 < (n : ℝ)+a := by positivity
  have hp1 : 0 < (n : ℝ)+1 := by positivity
  have hratio : 1-(1-a)/((n : ℝ)+1) = ((n : ℝ)+a)/((n : ℝ)+1) := by field_simp; ring
  change deriv (fun s : ℂ => ((n : ℂ)+(a : ℂ))^(-s) - ((n : ℂ)+1)^(-s) +
    s*((a : ℂ)-1)*((n : ℂ)+1)^(-s-1)) 0 = _
  have hd' := hd.deriv
  simp only [id_eq] at hd'
  rw [hd']
  simp only [id_eq, neg_zero, Complex.cpow_zero, zero_mul, one_mul, mul_neg_one,
    zero_sub, Complex.cpow_neg_one, mul_one, add_zero, sub_neg_eq_add, mul_zero, zero_add]
  rw [eulerLogGammaTerm, hratio, Real.log_div hp.ne' hp1.ne']
  push_cast
  rw [Complex.ofReal_log hp.le, Complex.ofReal_log hp1.le]
  push_cast
  ring

theorem zeta_regular_series_deriv_zero (a : ℝ) (ha : 0 < a) :
    deriv (zetaRegularSeries a) 0 =
      ((Real.log (Real.Gamma a)+Real.eulerMascheroniConstant*(a-1) : ℝ) : ℂ) := by
  have ht := Complex.hasSum_deriv_of_summable_norm (zeta_regular_majorant_summable a)
    (fun n => (zeta_regular_term_differentiable a ha (n+1)).differentiableOn)
    zeta_regular_region_open (fun n s hs => zeta_regular_term_tail_bound a ha n s hs.1.le hs.2.le)
    zeta_regular_region_zero
  simp only [zeta_regular_term_deriv_zero a ha] at ht
  have hg := (Complex.ofRealCLM.hasSum (log_gamma_euler_product (1-a) (by linarith)))
  have hg' := (hasSum_nat_add_iff' 1).mpr hg
  have he := ht.unique hg'
  have hd := (zeta_regular_term_differentiable a ha 0 0).hasDerivAt.add
    ((Complex.differentiableOn_tsum_of_summable_norm (zeta_regular_majorant_summable a)
      (fun n => (zeta_regular_term_differentiable a ha (n+1)).differentiableOn)
      zeta_regular_region_open (fun n s hs => zeta_regular_term_tail_bound a ha n s hs.1.le hs.2.le))
      |>.differentiableAt (zeta_regular_region_open.mem_nhds zeta_regular_region_zero)).hasDerivAt
  change deriv (fun s => zetaRegularTerm a 0 s + ∑' n : ℕ, zetaRegularTerm a (n+1) s) 0 = _
  rw [hd.deriv, zeta_regular_term_deriv_zero a ha, he]
  simp only [Finset.sum_range_one, Complex.ofRealCLM_apply, add_sub_cancel_left]
  push_cast
  rw [show 1-(1-a)=a by ring]
  ring

end
end Sigma
