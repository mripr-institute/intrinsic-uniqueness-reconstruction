import SigmaOpHeatKernelRowL2
import SigmaOpHeatKernelGeneratingIdentity

namespace Sigma
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
set_option maxHeartbeats 6000000

private theorem laguerre_heat_kernel_row_generating_inner {τ x z : ℝ}
    (hτ : 0 < τ) (hx : 0 < x) (hz : 0 ≤ z) (hz' : z < 1/4) :
    @inner ℂ LaguerreWeightedHilbert _
      (laguerreHeatKernelRow τ x hτ hx)
      (laguerreGeneratingVector z hz hz') =
    (laguerreGeneratingFunction (Real.exp (-τ)*z) x : ℂ) := by
  have hr : 0 < Real.exp (-τ) ∧ Real.exp (-τ) < 1 := by
    constructor
    · exact Real.exp_pos _
    · rw [Real.exp_lt_one_iff]; linarith
  have hd : 0 < 1-Real.exp (-τ) := by linarith
  have hβ : 0 ≤ Real.exp (-τ)/(1-Real.exp (-τ))+z/(1-z) :=
    add_nonneg (div_nonneg hr.1.le hd.le) (div_nonneg hz (by linarith))
  have htransform := laguerre_heat_kernel_generating_transform hτ hx
    (lt_trans hz' (by norm_num : (1/4:ℝ) < 1)) hβ
  have hreal : Integrable
      (fun y : ℝ => laguerreHeatKernel τ x y * laguerreGeneratingFunction z y)
      gammaProbability := by
    apply Integrable.of_integral_ne_zero
    rw [htransform]
    unfold laguerreGeneratingFunction
    have hrz : Real.exp (-τ)*z < 1 := by nlinarith
    have hden : 0 < 1-Real.exp (-τ)*z := by linarith
    positivity
  rw [L2.inner_def]
  have hrow := laguerre_heat_kernel_row_coe_ae hτ hx
  have hgen := (laguerre_generating_function_mem_l2 hz hz').coeFn_toLp
  have hcongr :
      (fun y : ℝ => @inner ℂ ℂ _
        (laguerreHeatKernelRow τ x hτ hx y)
        (laguerreGeneratingVector z hz hz' y)) =ᵐ[gammaProbability]
      (fun y => ((laguerreHeatKernel τ x y * laguerreGeneratingFunction z y : ℝ) : ℂ)) := by
    filter_upwards [hrow, hgen] with y h₁ h₂
    change (laguerreGeneratingVector z hz hz' : ℝ → ℂ) y = _ at h₂
    rw [h₁, h₂]
    simp [RCLike.inner_apply, Complex.conj_ofReal, Complex.ofReal_mul]
  rw [integral_congr_ae hcongr]
  change (∫ y : ℝ, Complex.ofRealCLM
    (laguerreHeatKernel τ x y * laguerreGeneratingFunction z y) ∂gammaProbability) =
    Complex.ofRealCLM (laguerreGeneratingFunction (Real.exp (-τ)*z) x)
  rw [Complex.ofRealCLM.integral_comp_comm hreal]
  exact congrArg Complex.ofReal htransform

theorem laguerre_heat_kernel_row_coordinate {τ x : ℝ}
    (hτ : 0 < τ) (hx : 0 < x) (n : ℕ) :
    laguerreHilbertBasis.repr (laguerreHeatKernelRow τ x hτ hx) n =
      (((Real.exp (-τ))^n * opLaguerre n x / Real.sqrt (n+1) : ℝ) : ℂ) := by
  let row := laguerreHeatKernelRow τ x hτ hx
  let r := Real.exp (-τ)
  let b : ℕ → ℂ := fun k => star (laguerreHilbertBasis.repr row k) *
    Complex.ofReal ((k+1:ℝ)/Real.sqrt (k+1))
  let c : ℕ → ℂ := fun k => Complex.ofReal (r^k * opLaguerre k x)
  have hr : 0 < r ∧ r < 1 := by
    constructor
    · exact Real.exp_pos _
    · dsimp [r]; rw [Real.exp_lt_one_iff]; linarith
  have hfsquare : Summable (fun k => ‖laguerreHilbertBasis.repr row k‖^2) := by
    have hs := (laguerreHilbertBasis.repr row).property.summable
      (by norm_num : 0 < (2:ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs
  have hgeo : Summable (fun k : ℕ => (k+1:ℝ)*(1/4:ℝ)^(2*k)) := by
    have hq : ‖(1/16:ℝ)‖ < 1 := by norm_num
    have hs := (hasSum_choose_mul_geometric_of_norm_lt_one (1:ℕ) hq).summable
    have heq : (fun k : ℕ => (k+1:ℝ)*(1/4:ℝ)^(2*k)) =
        fun k => ((k+1).choose 1:ℝ)*(1/16:ℝ)^k := by
      funext k
      rw [pow_mul]
      norm_num
    rw [heq]
    exact hs
  have hb : Summable (fun k => ‖b k‖*(1/4:ℝ)^k) := by
    apply Summable.of_nonneg_of_le
      (fun k => mul_nonneg (norm_nonneg _) (by positivity))
      (fun k => ?_) (hfsquare.add hgeo)
    let u : ℝ := ‖laguerreHilbertBasis.repr row k‖
    let v : ℝ := Real.sqrt (k+1)*(1/4:ℝ)^k
    have hk : 0 < (k+1:ℝ) := by positivity
    have hroot : Real.sqrt (k+1)^2 = k+1 := Real.sq_sqrt (by positivity)
    have hcoef : (k+1:ℝ)/Real.sqrt (k+1) = Real.sqrt (k+1) := by
      field_simp [ne_of_gt (Real.sqrt_pos.mpr hk)]
    have hnorm : ‖b k‖*(1/4:ℝ)^k = u*v := by
      simp [b, u, v, norm_mul, Complex.norm_real, hcoef,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      ring
    have hv2 : v^2 = (k+1:ℝ)*(1/4:ℝ)^(2*k) := by
      dsimp [v]
      rw [mul_pow, hroot, ← pow_mul]
      rw [show k*2=2*k by omega]
    rw [hnorm]
    nlinarith [sq_nonneg (u-v)]
  have hc : Summable (fun k => ‖c k‖*(1/4:ℝ)^k) := by
    have hsum : Summable (fun k : ℕ => (2*Real.exp x)*(1/2:ℝ)^k) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    apply Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (by positivity))
      (fun k => ?_) hsum
    have hL := op_laguerre_geometric_bound
      (t := (1:ℝ)) (M := x) (x := x) (by norm_num) hx.le hx.le le_rfl k
    have hpow : r^k ≤ 1 := by simpa using pow_le_one₀ hr.1.le hr.2.le
    simp only [c, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_mul, abs_of_nonneg (pow_nonneg hr.1.le k)]
    have hbasic : r^k * |opLaguerre k x| ≤ 2^(k+1)*Real.exp x := by
      calc
        _ ≤ 1*|opLaguerre k x| :=
          mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
        _ ≤ 2^(k+1)*Real.exp x := by
          norm_num at hL ⊢
          exact hL
    calc
      r^k * |opLaguerre k x| * (1/4:ℝ)^k ≤
          (2^(k+1)*Real.exp x)*(1/4:ℝ)^k :=
        mul_le_mul_of_nonneg_right hbasic (by positivity)
      _ = (2*Real.exp x)*(1/2:ℝ)^k := by
        rw [pow_succ]
        calc
          (2^k*2*Real.exp x)*(1/4:ℝ)^k =
              (2*Real.exp x)*((2:ℝ)^k*(1/4:ℝ)^k) := by ring
          _ = (2*Real.exp x)*(1/2:ℝ)^k := by
            rw [← mul_pow]
            norm_num
  have ha : Summable (fun k => ‖b k-c k‖*(1/4:ℝ)^k) := by
    apply Summable.of_nonneg_of_le
      (fun k => mul_nonneg (norm_nonneg _) (by positivity))
      (fun k => ?_) (hb.add hc)
    calc
      ‖b k-c k‖*(1/4:ℝ)^k ≤ (‖b k‖+‖c k‖)*(1/4:ℝ)^k :=
        mul_le_mul_of_nonneg_right (norm_sub_le _ _) (by positivity)
      _ = ‖b k‖*(1/4:ℝ)^k+‖c k‖*(1/4:ℝ)^k := by ring
  have hcoeff := power_series_coefficients_zero (R := (1/4:ℝ)) (by norm_num) ha
    (by
      intro z hz hz'
      have hinner : (∑' k : ℕ, b k*(z:ℂ)^k) =
          @inner ℂ LaguerreWeightedHilbert _ row
            (laguerreGeneratingVector z hz.le hz') := by
        rw [← laguerreHilbertBasis.repr.inner_map_map, lp.inner_eq_tsum]
        apply tsum_congr
        intro k
        rw [laguerre_generating_vector_coordinate hz.le hz' k]
        simp [b, RCLike.inner_apply, Complex.conj_ofReal, mul_assoc]
      have hrz : 0 < r*z ∧ r*z < 1/4 := by
        constructor
        · exact mul_pos hr.1 hz
        · nlinarith [mul_nonneg (sub_nonneg.mpr hr.2.le) hz.le]
      have hseries : (∑' k : ℕ, c k*(z:ℂ)^k) =
          (laguerreGeneratingFunction (r*z) x : ℂ) := by
        rw [laguerre_generating_function_eq_tsum hrz.1 hrz.2 hx]
        have hqsum : Summable (fun k : ℕ => (r*z)^k * opLaguerre k x) := by
          apply Summable.of_norm_bounded (fun k => ‖c k‖*(1/4:ℝ)^k) hc
          intro k
          have hzpow : z^k ≤ (1/4:ℝ)^k :=
            pow_le_pow_left₀ hz.le hz'.le k
          have hc0 : ‖c k‖ = r^k * |opLaguerre k x| := by
            simp only [c, Complex.norm_real, Real.norm_eq_abs]
            change |r^k * opLaguerre k x| = _
            rw [abs_mul, abs_of_nonneg (pow_nonneg hr.1.le k)]
          rw [Real.norm_eq_abs, mul_pow]
          simp only [abs_mul, abs_of_nonneg (pow_nonneg hr.1.le k),
            abs_of_nonneg (pow_nonneg hz.le k), hc0]
          calc
            r^k*z^k*|opLaguerre k x| =
                (r^k*|opLaguerre k x|)*z^k := by ring
            _ ≤ (r^k*|opLaguerre k x|)*(1/4:ℝ)^k :=
              mul_le_mul_of_nonneg_left hzpow (by positivity)
        change (∑' k : ℕ, c k*(z:ℂ)^k) =
          Complex.ofRealCLM (∑' k : ℕ, (r*z)^k * opLaguerre k x)
        rw [Complex.ofRealCLM.map_tsum hqsum]
        apply tsum_congr
        intro k
        simp [c, mul_pow, Complex.ofReal_mul, Complex.ofReal_pow]
        ring
      have hbz : Summable (fun k => b k*(z:ℂ)^k) := by
        apply Summable.of_norm_bounded (fun k => ‖b k‖*(1/4:ℝ)^k) hb
        intro k
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg z)
            (by rw [abs_of_nonneg hz.le]; exact hz'.le) k) (norm_nonneg _)
      have hcz : Summable (fun k => c k*(z:ℂ)^k) := by
        apply Summable.of_norm_bounded (fun k => ‖c k‖*(1/4:ℝ)^k) hc
        intro k
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
        simp only [c, Complex.norm_real, Real.norm_eq_abs]
        change |r^k * opLaguerre k x| * |z|^k ≤
          |r^k * opLaguerre k x| * (1/4:ℝ)^k
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg z)
            (by rw [abs_of_nonneg hz.le]; exact hz'.le) k) (abs_nonneg _)
      rw [show (fun k : ℕ => (b k-c k)*(z:ℂ)^k) =
          (fun k => b k*(z:ℂ)^k-c k*(z:ℂ)^k) by funext k; ring]
      rw [tsum_sub hbz hcz, hinner, hseries]
      exact sub_eq_zero.mpr (by
        simpa only [row, r] using
          laguerre_heat_kernel_row_generating_inner hτ hx hz.le hz'))
  have hn := hcoeff n
  have hsqrt : Real.sqrt (n+1:ℝ) ≠ 0 := by positivity
  have hcoef : (n+1:ℝ)/Real.sqrt (n+1) = Real.sqrt (n+1) := by
    field_simp [hsqrt]
  simp only [b, c, sub_eq_zero] at hn
  rw [hcoef] at hn
  have hstar := congrArg star hn
  simp only [star_mul, star_star] at hstar
  simp [Complex.star_def] at hstar
  have hden : (Real.sqrt (n+1:ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsqrt
  change laguerreHilbertBasis.repr row n =
    (↑(r^n * opLaguerre n x / Real.sqrt (n+1)) : ℂ)
  rw [Complex.ofReal_div]
  apply (eq_div_iff hden).2
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, mul_comm] using hstar

end
end Sigma
