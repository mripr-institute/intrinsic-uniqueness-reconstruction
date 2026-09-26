import SigmaOpDeterminantZeta
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Analysis.Complex.CauchyIntegral

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology BigOperators

theorem hurwitz_half_duplication_series (s : ℂ) (hs : 1 < s.re) :
    HurwitzZeta.hurwitzZeta ((1/2 : ℝ) : UnitAddCircle) s =
      ((2 : ℂ)^s-1) * riemannZeta s := by
  let f : ℕ → ℂ := fun n => 1 / (n : ℂ)^s
  have hZ : HasSum f (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs]
    exact (Complex.summable_one_div_nat_cpow.mpr hs).hasSum
  have he : HasSum (fun n => f (2*n)) (((2 : ℂ)^s)⁻¹ * riemannZeta s) := by
    convert hZ.mul_left (((2 : ℂ)^s)⁻¹) using 1
    funext n
    simpa only [f, Nat.cast_mul, Nat.cast_ofNat, one_div, mul_inv] using
      congrArg Inv.inv (Complex.natCast_mul_natCast_cpow 2 n s)
  have hh := (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re
    (a := (1/2 : ℝ)) (by constructor <;> norm_num) hs).mul_left (((2 : ℂ)^s)⁻¹)
  have ho : HasSum (fun n => f (2*n+1))
      ((((2 : ℂ)^s)⁻¹) * HurwitzZeta.hurwitzZeta ((1/2 : ℝ) : UnitAddCircle) s) := by
    convert hh using 1
    funext n
    have hp := Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (show (0 : ℝ) ≤ (n : ℝ)+1/2 by positivity) s
    have hc : (2 : ℂ)*((((n : ℝ)+1/2 : ℝ) : ℂ)) = ((2*n+1 : ℕ) : ℂ) := by
      push_cast; ring
    norm_num only [Complex.ofReal_ofNat] at hp
    rw [hc] at hp
    change 1 / ((2*n+1 : ℕ) : ℂ)^s = _
    rw [hp]
    push_cast
    simp only [one_div, mul_inv]
  have h := hZ.unique (he.even_add_odd ho)
  have hn : (2 : ℂ)^s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    exact Complex.exp_ne_zero _
  field_simp at h
  linear_combination -h

theorem hurwitz_half_duplication (s : ℂ) (hs : s ≠ 1) :
    HurwitzZeta.hurwitzZeta ((1/2 : ℝ) : UnitAddCircle) s =
      ((2 : ℂ)^s-1) * riemannZeta s := by
  let U := {s : ℂ | s ≠ 1}
  have hU : IsOpen U := isOpen_compl_singleton
  have hf : AnalyticOnNhd ℂ (HurwitzZeta.hurwitzZeta ((1/2 : ℝ) : UnitAddCircle)) U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact (HurwitzZeta.differentiableAt_hurwitzZeta _ hz).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (fun z : ℂ => ((2 : ℂ)^z-1)*riemannZeta z) U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact ((differentiableAt_id.const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))).sub_const 1
      |>.mul (differentiableAt_riemannZeta hz)).differentiableWithinAt
  have hUc : IsPreconnected U := by
    exact (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg hUc (show (2 : ℂ) ∈ U by norm_num [U]) _ hs
  filter_upwards [hV] with z hz using hurwitz_half_duplication_series z hz

theorem hurwitz_half_deriv_zero :
    deriv (HurwitzZeta.hurwitzZeta ((1/2 : ℝ) : UnitAddCircle)) 0 =
      -Complex.log 2 / 2 := by
  have hc := ((hasDerivAt_id (0 : ℂ)).const_cpow
    (Or.inl (by norm_num : (2 : ℂ) ≠ 0))).sub_const 1
  have hz := (differentiableAt_riemannZeta (by norm_num : (0 : ℂ) ≠ 1)).hasDerivAt
  have hd := hc.mul hz
  have he : HurwitzZeta.hurwitzZeta ((1/2 : ℝ) : UnitAddCircle) =ᶠ[𝓝 (0 : ℂ)]
      (fun z : ℂ => ((2 : ℂ)^z-1)*riemannZeta z) := by
    filter_upwards [eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ 1)] with z hz
      using hurwitz_half_duplication z hz
  have h := (hd.congr_of_eventuallyEq he).deriv
  convert h using 1
  simp [riemannZeta_zero]
  ring

theorem laguerre_hurwitz_zeta_half (s : ℂ) :
    laguerreHurwitzZeta (1/2) s =
      HurwitzZeta.hurwitzZeta ((1/2 : ℝ) : UnitAddCircle) s := by
  norm_num [laguerreHurwitzZeta, laguerreHurwitzBase, laguerreHurwitzShift]

/-- An absolute normalization at the half shift, obtained without assuming Lerch's formula. -/
theorem laguerre_zeta_determinant_half :
    laguerreZetaDeterminant (1/2) = (Real.sqrt 2 : ℂ) := by
  unfold laguerreZetaDeterminant
  rw [show laguerreHurwitzZeta (1/2) =
    HurwitzZeta.hurwitzZeta ((1/2 : ℝ) : UnitAddCircle) from funext laguerre_hurwitz_zeta_half,
    hurwitz_half_deriv_zero]
  rw [neg_div, neg_neg]
  have hr : (Real.exp (Real.log 2 / 2) : ℝ) = Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [← Complex.ofReal_ofNat 2, ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
  exact_mod_cast hr

theorem laguerre_zeta_determinant_half_gamma :
    laguerreZetaDeterminant (1/2) =
      ((Real.sqrt (2*Real.pi) / Real.Gamma (1/2) : ℝ) : ℂ) := by
  rw [laguerre_zeta_determinant_half, Real.Gamma_one_half_eq,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr Real.pi_pos).ne']

end
end Sigma

