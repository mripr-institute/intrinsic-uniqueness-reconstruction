import SigmaOpHeatKernel
import SigmaOpLaguerreComplete
import SigmaOpCanonicalInverse
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace Sigma
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
open Filter
open scoped Topology
set_option maxHeartbeats 6000000

private theorem power_series_constant_coefficient_zero {a : ℕ → ℂ} {R : ℝ}
    (hR : 0 < R) (hs : Summable (fun n => ‖a n‖ * R^n))
    (hzero : ∀ z : ℝ, 0 < z → z < R →
      (∑' n : ℕ, a n * (z : ℂ)^n) = 0) : a 0 = 0 := by
  have hRwithin : ∀ᶠ z : ℝ in 𝓝[>] (0 : ℝ), z < R :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hR)
  have hgensummable (n : ℕ) : Tendsto (fun z : ℝ => a n * (z : ℂ)^n)
      (𝓝[>] 0) (𝓝 (if n = 0 then a 0 else 0)) := by
    by_cases hn : n = 0
    · subst n
      simpa only [pow_zero, mul_one, if_pos rfl] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => a 0) (𝓝[>] 0) (𝓝 (a 0)))
    · have hz : Tendsto (fun z : ℝ => (z : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hp : Tendsto (fun z : ℝ => (z : ℂ)^n) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
        simpa [hn] using hz.pow n
      have hmul : Tendsto (fun z : ℝ => a n * (z : ℂ)^n) (𝓝[>] 0)
          (𝓝 (a n * (0 : ℂ))) :=
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => a n) (𝓝[>] 0) (𝓝 (a n))).mul
          hp
      simpa only [if_neg hn, mul_zero] using hmul
  have hbound : ∀ᶠ z : ℝ in 𝓝[>] 0, ∀ n : ℕ,
      ‖a n * (z : ℂ)^n‖ ≤ ‖a n‖ * R^n := by
    filter_upwards [eventually_mem_nhdsWithin, hRwithin] with z hz0 hzR
    intro n
    rw [norm_mul, norm_pow, Complex.norm_real]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg (a n))
    exact pow_le_pow_left₀ (abs_nonneg z)
      (by rw [abs_of_nonneg hz0.le]; exact hzR.le) n
  have hlim : Tendsto (fun z : ℝ => ∑' n : ℕ, a n * (z : ℂ)^n)
      (𝓝[>] 0) (𝓝 (a 0)) := by
    simpa using (tendsto_tsum_of_dominated_convergence
      (𝓕 := 𝓝[>] (0 : ℝ))
      (f := fun z n => a n * (z : ℂ)^n)
      (g := fun n => if n = 0 then a 0 else 0)
      (bound := fun n => ‖a n‖ * R^n) hs hgensummable hbound)
  have hzeroevent : (fun z : ℝ => ∑' n : ℕ, a n * (z : ℂ)^n) =ᶠ[𝓝[>] 0]
      fun _ => 0 := by
    filter_upwards [eventually_mem_nhdsWithin, hRwithin] with z hz hzR
    simpa using hzero z hz hzR
  have hlim0 : Tendsto (fun z : ℝ => ∑' n : ℕ, a n * (z : ℂ)^n)
      (𝓝[>] 0) (𝓝 0) := tendsto_const_nhds.congr' hzeroevent.symm
  exact tendsto_nhds_unique hlim hlim0

theorem power_series_coefficients_zero {a : ℕ → ℂ} {R : ℝ}
    (hR : 0 < R) (hs : Summable (fun n => ‖a n‖ * R^n))
    (hzero : ∀ z : ℝ, 0 < z → z < R →
      (∑' n : ℕ, a n * (z : ℂ)^n) = 0) : ∀ n, a n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      let k := n
      have hshift : Summable (fun j : ℕ => ‖a (j+k)‖ * R^(j+k)) :=
        hs.comp_injective (by
          intro i j hij
          exact Nat.add_right_cancel hij)
      have hshifted : Summable (fun j : ℕ => ‖a (j+k)‖ * R^j) := by
        apply (hshift.mul_left (R⁻¹^k)).congr
        intro j
        rw [pow_add]
        field_simp [ne_of_gt hR]
        ring
      have hzeroShift : ∀ z : ℝ, 0 < z → z < R →
          (∑' j : ℕ, a (j+k) * (z : ℂ)^j) = 0 := by
        intro z hz hzR
        have hseries : Summable (fun i : ℕ => a i * (z : ℂ)^i) := by
          apply Summable.of_norm_bounded (fun i : ℕ => ‖a i‖ * R^i) hs
          intro i
          rw [norm_mul, norm_pow, Complex.norm_real]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg (a i))
          exact pow_le_pow_left₀ (abs_nonneg z)
            (by rw [abs_of_nonneg hz.le]; exact hzR.le) i
        have hfull : (∑' i : ℕ, a i * (z : ℂ)^i) = 0 := hzero z hz hzR
        rw [← sum_add_tsum_nat_add k hseries] at hfull
        have hfinite : (∑ i ∈ Finset.range k, a i * (z : ℂ)^i) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          rw [ih i (Finset.mem_range.mp hi)]
          simp
        rw [hfinite, zero_add] at hfull
        have hfactor : (fun j : ℕ => a (j+k) * (z : ℂ)^(j+k)) =
            fun j => (z : ℂ)^k * (a (j+k) * (z : ℂ)^j) := by
          funext j
          rw [pow_add]
          ring
        rw [hfactor, tsum_mul_left] at hfull
        have hzpow : (z : ℂ)^k ≠ 0 := pow_ne_zero k (by exact_mod_cast hz.ne')
        exact (mul_eq_zero.mp hfull).resolve_left hzpow
      have := power_series_constant_coefficient_zero hR hshifted hzeroShift
      simpa [k] using this

private theorem gamma_probability_exp_monomial_integrable {s : ℝ} (hs : -1 < s)
    (k : ℕ) : Integrable (fun y : ℝ => Real.exp (-(s*y))*y^k) gammaProbability := by
  apply Integrable.of_integral_ne_zero
  rw [gamma_probability_exp_monomial_integral k hs]
  apply div_ne_zero
  · positivity
  · exact pow_ne_zero _ (ne_of_gt (by linarith))

private theorem even_factorial_bound (m : ℕ) :
    ((2*m).factorial : ℝ) ≤ 4^m * (m.factorial:ℝ) * ((m+1).factorial:ℝ) := by
  have hchooseNat : (2*m).choose m ≤ 4^m := by
    calc
      (2*m).choose m ≤ ∑ k ∈ Finset.range (2*m+1), (2*m).choose k :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
      _ = 2^(2*m) := by rw [Nat.sum_range_choose]
      _ = 4^m := by rw [pow_mul]; norm_num
  have hchoose : ((2*m).choose m:ℝ) ≤ 4^m := by exact_mod_cast hchooseNat
  have hfactor : ((2*m).choose m:ℝ) * (m.factorial:ℝ) * (m.factorial:ℝ) =
      ((2*m).factorial:ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2*m by omega)
    have h' : (2*m).choose m * m.factorial * m.factorial = (2*m).factorial := by
      simpa only [show 2*m-m=m by omega] using h
    exact_mod_cast h'
  have hfactle : (m.factorial:ℝ) ≤ ((m+1).factorial:ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    have hmf : (0:ℝ) ≤ (m.factorial:ℝ) := by positivity
    nlinarith [mul_nonneg hmf (sub_nonneg.mpr (show (0:ℝ) ≤ (m:ℝ) by exact_mod_cast Nat.zero_le m))]
  calc
    ((2*m).factorial:ℝ) = ((2*m).choose m:ℝ) * (m.factorial:ℝ) * (m.factorial:ℝ) := hfactor.symm
    _ ≤ 4^m * (m.factorial:ℝ) * (m.factorial:ℝ) := by gcongr
    _ ≤ 4^m * (m.factorial:ℝ) * ((m+1).factorial:ℝ) := by gcongr

private theorem modified_bessel_i1_term_le_exp_coefficient {t : ℝ}
    (ht : 0 ≤ t) (m : ℕ) :
    modifiedBesselI1Term t m ≤ (t/2) * (t^(2*m) / ((2*m).factorial:ℝ)) := by
  have hden : 0 < (m.factorial:ℝ) * ((m+1).factorial:ℝ) := by positivity
  have hfac : 0 < ((2*m).factorial:ℝ) := by positivity
  have hfour : (2:ℝ)^(2*m) = 4^m := by rw [pow_mul]; norm_num
  have hp : (t/2)^(2*m) = t^(2*m) / 4^m := by
    rw [div_pow, hfour]
  have hcoef : 1 / (4^m * (m.factorial:ℝ) * ((m+1).factorial:ℝ)) ≤
      ((2*m).factorial:ℝ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hfac (even_factorial_bound m)
  rw [modifiedBesselI1Term]
  rw [hp]
  have htmon : 0 ≤ t^(2*m) := pow_nonneg ht _
  have hcalc : (t/2) * ((t^(2*m)/4^m) /
      ((m.factorial:ℝ)*((m+1).factorial:ℝ))) =
      (t/2) * (t^(2*m) *
        (1/(4^m*(m.factorial:ℝ)*((m+1).factorial:ℝ)))) := by
    rw [div_div]
    simp only [div_eq_mul_inv, one_div]
    ring
  rw [hcalc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hcoef htmon) (by positivity)

private theorem modified_bessel_i1_le_mul_exp {t : ℝ} (ht : 0 ≤ t) :
    modifiedBesselI1 t ≤ (t/2) * Real.exp t := by
  let e : ℕ → ℝ := fun n => t^n / (n.factorial:ℝ)
  have he : Summable e := by
    simpa only [e] using (NormedSpace.expSeries_div_hasSum_exp ℝ t).summable
  have hdouble : Function.Injective (fun m : ℕ => 2*m) := by
    intro i j hij
    change 2*i = 2*j at hij
    exact Nat.mul_left_cancel (by norm_num : 0 < 2) hij
  have heven : Summable (fun m : ℕ => e (2*m)) := he.comp_injective hdouble
  have hle : (∑' m : ℕ, e (2*m)) ≤ Real.exp t := by
    calc
      (∑' m : ℕ, e (2*m)) ≤ ∑' n : ℕ, e n :=
        tsum_le_tsum_of_inj (fun m => 2*m) hdouble
          (fun _ _ => div_nonneg (pow_nonneg ht _) (Nat.cast_nonneg _))
          (fun _ => le_rfl) heven he
      _ = Real.exp t := by
        simpa only [e, ← Real.exp_eq_exp_ℝ] using
          (NormedSpace.expSeries_div_hasSum_exp ℝ t).tsum_eq
  have hterm : ∀ m, modifiedBesselI1Term t m ≤ (t/2) * e (2*m) := by
    intro m
    simpa [e] using modified_bessel_i1_term_le_exp_coefficient ht m
  have hupper : Summable (fun m : ℕ => (t/2) * e (2*m)) := heven.mul_left (t/2)
  calc
    modifiedBesselI1 t = ∑' m, modifiedBesselI1Term t m := rfl
    _ ≤ ∑' m, (t/2) * e (2*m) :=
      tsum_le_tsum hterm (modified_bessel_i1_term_summable t) hupper
    _ = (t/2) * ∑' m, e (2*m) := tsum_mul_left
    _ ≤ (t/2) * Real.exp t := by
      exact mul_le_mul_of_nonneg_left hle (by positivity)

private theorem modified_bessel_i1_measurable : Measurable modifiedBesselI1 := by
  apply measurable_of_tendsto_metrizable
  · intro N
    change Measurable (fun t : ℝ => ∑ m ∈ Finset.range N, modifiedBesselI1Term t m)
    apply Finset.measurable_sum
    intro m hm
    have hc : Continuous (fun t : ℝ => modifiedBesselI1Term t m) := by
      change Continuous (fun t : ℝ =>
        (t/2) * ((t/2)^(2*m) / ((m.factorial:ℝ)*((m+1).factorial:ℝ))))
      fun_prop
    exact hc.measurable
  · rw [tendsto_pi_nhds]
    intro t
    exact (modified_bessel_i1_term_summable t).hasSum.tendsto_sum_nat

theorem laguerre_heat_kernel_measurable (τ : ℝ) :
    Measurable (fun z : ℝ × ℝ => laguerreHeatKernel τ z.1 z.2) := by
  have hI : Measurable modifiedBesselI1 := modified_bessel_i1_measurable
  refine Measurable.ite (measurableSet_lt measurable_const measurable_snd) ?_ measurable_const
  unfold laguerreHeatKernelClosed
  have harg : Measurable (fun z : ℝ × ℝ =>
      2*Real.sqrt (Real.exp (-τ)*z.1*z.2)/(1-Real.exp (-τ))) := by fun_prop
  have hnum : Measurable (fun z : ℝ × ℝ =>
      Real.exp (-Real.exp (-τ)*(z.1+z.2)/(1-Real.exp (-τ)))) := by fun_prop
  have hden : Measurable (fun z : ℝ × ℝ =>
      (1-Real.exp (-τ))*Real.sqrt (Real.exp (-τ)*z.1*z.2)) := by fun_prop
  exact (hnum.div hden).mul (hI.comp harg)

theorem laguerre_heat_kernel_closed_growth_bound {τ x y : ℝ}
    (hτ : 0 < τ) (hx : 0 < x) (hy : 0 < y) :
    laguerreHeatKernelClosed τ x y ≤
      ((1-Real.exp (-τ))⁻¹)^2 *
        Real.exp ((Real.sqrt (Real.exp (-τ))/(1+Real.sqrt (Real.exp (-τ))))*(x+y)) := by
  let r := Real.exp (-τ)
  let d := 1-r
  let s := Real.sqrt r
  let v := Real.sqrt (r*x*y)
  let u := 2*v/d
  have hr : 0 < r ∧ r < 1 := by
    constructor
    · exact Real.exp_pos _
    · rw [Real.exp_lt_one_iff]
      linarith
  have hd : 0 < d := sub_pos.mpr hr.2
  have hs : 0 < s ∧ s < 1 := by
    constructor
    · exact Real.sqrt_pos.mpr hr.1
    · have hs2 : s^2=r := Real.sq_sqrt hr.1.le
      nlinarith [Real.sqrt_nonneg r]
  have hv : 0 < v := Real.sqrt_pos.mpr (mul_pos (mul_pos hr.1 hx) hy)
  have hu : 0 < u := div_pos (mul_pos (by norm_num) hv) hd
  have hcross : 2*v ≤ s*(x+y) := by
    have hvEq : v = s * Real.sqrt x * Real.sqrt y := by
      dsimp [v, s]
      rw [show r*x*y = r*(x*y) by ring, Real.sqrt_mul hr.1.le,
        Real.sqrt_mul hx.le y]
      ring
    rw [hvEq]
    have hAM : 2*Real.sqrt x*Real.sqrt y ≤ x+y := by
      nlinarith [sq_nonneg (Real.sqrt x-Real.sqrt y), Real.sq_sqrt hx.le,
        Real.sq_sqrt hy.le, Real.sqrt_nonneg x, Real.sqrt_nonneg y]
    calc
      2*(s*Real.sqrt x*Real.sqrt y) = s*(2*Real.sqrt x*Real.sqrt y) := by ring
      _ ≤ s*(x+y) := mul_le_mul_of_nonneg_left hAM hs.1.le
  have hratio : (-r*(x+y)+2*v)/d ≤ (s/(1+s))*(x+y) := by
    apply (div_le_iff₀ hd).2
    have hdEq : d = (1-s)*(1+s) := by
      dsimp [d, s]
      nlinarith [Real.sq_sqrt hr.1.le]
    have hrs : r = s^2 := (Real.sq_sqrt hr.1.le).symm
    have hsMul : -r*(x+y)+2*v ≤ (s-r)*(x+y) := by nlinarith [hcross]
    have hfactor : s-r = d*(s/(1+s)) := by
      rw [hdEq, hrs]
      field_simp [ne_of_gt (by linarith : (1:ℝ)+s > 0)]
      ring
    calc
      -r*(x+y)+2*v ≤ (s-r)*(x+y) := hsMul
      _ = (s/(1+s)) * d * (x+y) := by rw [hfactor]; ring
      _ = (s/(1+s)*(x+y))*d := by ring
  have hI := modified_bessel_i1_le_mul_exp (le_of_lt hu)
  have hI' : modifiedBesselI1 u ≤ (v/d)*Real.exp u := by
    have huHalf : u/2 = v/d := by
      dsimp [u]
      ring
    rw [huHalf] at hI
    exact hI
  have hkernel : laguerreHeatKernelClosed τ x y =
      (Real.exp (-r*(x+y)/d)/(d*v))*modifiedBesselI1 u := by
    simp [laguerreHeatKernelClosed, r, d, s, v, u]
  have hbound : laguerreHeatKernelClosed τ x y ≤
      (d⁻¹)^2 * Real.exp ((-r*(x+y)+2*v)/d) := by
    rw [hkernel]
    calc
      (Real.exp (-r*(x+y)/d)/(d*v))*modifiedBesselI1 u ≤
      (Real.exp (-r*(x+y)/d)/(d*v))*((v/d)*Real.exp u) :=
        mul_le_mul_of_nonneg_left hI' (by positivity)
      _ = (d⁻¹)^2*Real.exp ((-r*(x+y)+2*v)/d) := by
        have hcoeff : (1/(d*v))*(v/d) = (d⁻¹)^2 := by
          field_simp [ne_of_gt hd, ne_of_gt hv]
          ring
        have hexp : -r*(x+y)/d + u = (-r*(x+y)+2*v)/d := by
          dsimp [u]
          ring
        calc
          _ = ((1/(d*v))*(v/d)) *
              (Real.exp (-r*(x+y)/d)*Real.exp u) := by ring
          _ = (d⁻¹)^2*Real.exp ((-r*(x+y)+2*v)/d) := by
            rw [hcoeff, ← Real.exp_add, hexp]
  have hrate : s/(1+s) < 1/2 := by
    rw [div_lt_iff₀ (by linarith : 0 < 1+s)]
    nlinarith
  calc
    laguerreHeatKernelClosed τ x y ≤ (d⁻¹)^2 * Real.exp ((-r*(x+y)+2*v)/d) := hbound
    _ ≤ (d⁻¹)^2 * Real.exp ((s/(1+s))*(x+y)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.exp_le_exp.mpr hratio
    _ = ((1-Real.exp (-τ))⁻¹)^2 *
        Real.exp ((Real.sqrt (Real.exp (-τ))/(1+Real.sqrt (Real.exp (-τ))))*(x+y)) := by
      simp [r, d, s]

/-- The closed kernel is an actual vector in the Gamma-weighted product `L²`. -/
theorem laguerre_heat_kernel_mem_product_l2 {τ : ℝ} (hτ : 0 < τ) :
    Memℒp (fun z : ℝ × ℝ => laguerreHeatKernel τ z.1 z.2) 2
      (gammaProbability.prod gammaProbability) := by
  let r := Real.exp (-τ)
  let c := Real.sqrt r / (1+Real.sqrt r)
  let D := ((1-r)⁻¹)^2
  have hr : 0 < r ∧ r < 1 := by
    constructor
    · exact Real.exp_pos _
    · rw [Real.exp_lt_one_iff]; linarith
  have hs : Real.sqrt r < 1 := by
    nlinarith [Real.sq_sqrt hr.1.le, Real.sqrt_nonneg r]
  have hc : c < 1/2 := by
    dsimp [c]
    rw [div_lt_iff₀ (by positivity : 0 < 1+Real.sqrt r)]
    nlinarith
  have hβ : -1 < -(2*c) := by linarith
  have hExpInt : Integrable (fun x : ℝ => Real.exp ((2*c)*x))
      gammaProbability := by
    apply Integrable.of_integral_ne_zero
    have h := gamma_probability_laplace (s := -(2*c)) hβ
    simpa only [neg_mul, neg_neg] using
      (show (∫ x : ℝ, Real.exp ((2*c)*x) ∂gammaProbability) ≠ 0 by
        rw [show (fun x : ℝ => Real.exp ((2*c)*x)) =
          (fun x : ℝ => Real.exp (-(-(2*c)*x))) by funext x; congr 1; ring,
          h]
        have hden : 0 < 1 + -(2*c) := by linarith
        positivity)
  have hboundInt : Integrable (fun z : ℝ × ℝ =>
      D^2 * (Real.exp ((2*c)*z.1) * Real.exp ((2*c)*z.2)))
      (gammaProbability.prod gammaProbability) :=
    (hExpInt.prod_mul hExpInt).const_mul _
  have hp : ∀ᵐ x : ℝ ∂gammaProbability, 0 < x := by
    have hn : ∀ᵐ x : ℝ ∂gammaProbability, 0 ≤ x := by
      simpa only [ae_iff, not_le] using gamma_probability_negative_ray
    have hne : ∀ᵐ x : ℝ ∂gammaProbability, x ≠ 0 := by
      rw [ae_iff]
      simpa only [not_ne_iff, Set.setOf_eq_eq_singleton] using
        gamma_probability_no_atom 0
    filter_upwards [hn, hne] with x hx hxn
    exact lt_of_le_of_ne hx (Ne.symm hxn)
  have hprod : ∀ᵐ z : ℝ × ℝ ∂gammaProbability.prod gammaProbability,
      0 < z.1 ∧ 0 < z.2 := by
    apply (Measure.ae_prod_iff_ae_ae (show MeasurableSet
      {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2} from
        (measurableSet_lt measurable_const measurable_fst).inter
          (measurableSet_lt measurable_const measurable_snd))).2
    filter_upwards [hp] with x hx
    filter_upwards [hp] with y hy
    exact ⟨hx, hy⟩
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ × ℝ => laguerreHeatKernel τ z.1 z.2)
      (gammaProbability.prod gammaProbability) :=
    (laguerre_heat_kernel_measurable τ).aestronglyMeasurable
  apply (memℒp_two_iff_integrable_sq_norm hmeas).mpr
  apply Integrable.mono' hboundInt
  · exact (laguerre_heat_kernel_measurable τ).norm.pow_const 2 |>.aestronglyMeasurable
  · filter_upwards [hprod] with z hz
    have hKpos : 0 ≤ laguerreHeatKernel τ z.1 z.2 := by
      rw [laguerreHeatKernel, if_pos hz.2]
      exact (laguerre_heat_kernel_closed_pos hτ hz.1 hz.2).le
    have hKbound : laguerreHeatKernel τ z.1 z.2 ≤
        D * Real.exp (c*(z.1+z.2)) := by
      rw [laguerreHeatKernel, if_pos hz.2]
      simpa only [D, c, r] using
        laguerre_heat_kernel_closed_growth_bound hτ hz.1 hz.2
    have hsq : (laguerreHeatKernel τ z.1 z.2)^2 ≤
        (D * Real.exp (c*(z.1+z.2)))^2 := by
      gcongr
    rw [Real.norm_of_nonneg (sq_nonneg (‖laguerreHeatKernel τ z.1 z.2‖)),
      Real.norm_eq_abs, sq_abs]
    calc
      (laguerreHeatKernel τ z.1 z.2)^2 ≤
          (D * Real.exp (c*(z.1+z.2)))^2 := hsq
      _ = D^2 * (Real.exp ((2*c)*z.1) * Real.exp ((2*c)*z.2)) := by
        rw [mul_pow, pow_two (Real.exp (c*(z.1+z.2))), ← Real.exp_add]
        congr 1
        rw [← Real.exp_add]
        congr 1
        ring

/-- A tunable geometric coefficient bound on compact positive intervals. -/
theorem op_laguerre_geometric_bound {t M x : ℝ} (ht : 0 < t)
    (hM : 0 ≤ M) (hx : 0 ≤ x) (hxM : x ≤ M) (n : ℕ) :
    |opLaguerre n x| ≤ ((1+t)^(n+1)/t) * Real.exp (M/t) := by
  have hchoose (k : ℕ) (hk : k ≤ n) :
      ((n+1).choose (k+1):ℝ) * t^(k+1) ≤ (1+t)^(n+1) := by
    have hsingle : ((n+1).choose (k+1):ℝ) * t^(k+1) ≤
        ∑ j ∈ Finset.range (n+2),
          ((n+1).choose j:ℝ) * t^j := by
      exact Finset.single_le_sum (s := Finset.range (n+2))
        (f := fun j => ((n+1).choose j:ℝ) * t^j)
        (fun j hj => by positivity) (Finset.mem_range.mpr (by omega))
    calc
      ((n+1).choose (k+1):ℝ) * t^(k+1) ≤
          ∑ j ∈ Finset.range (n+2), ((n+1).choose j:ℝ) * t^j := hsingle
      _ = (1+t)^(n+1) := by
        rw [show (1+t) = (t+1) by ring, add_pow]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [one_pow, mul_one]
        ring
  have hterm (k : ℕ) (hk : k ≤ n) :
      |opLaguerreCoefficient n k * x^k| ≤
        ((1+t)^(n+1)/t) * ((M/t)^k/(k.factorial:ℝ)) := by
    have hc : 0 ≤ ((n+1).choose (k+1):ℝ) := Nat.cast_nonneg _
    have hf : 0 < (k.factorial:ℝ) := by positivity
    have hchoose' : ((n+1).choose (k+1):ℝ) ≤
        (1+t)^(n+1)/t^(k+1) := by
      exact (le_div_iff₀ (pow_pos ht _)).mpr (hchoose k hk)
    have hpow : x^k ≤ M^k := pow_le_pow_left₀ hx hxM k
    have hterm' : ((n+1).choose (k+1):ℝ) * x^k/(k.factorial:ℝ) ≤
        ((1+t)^(n+1)/t^(k+1)) * M^k/(k.factorial:ℝ) := by
      gcongr
    have halg : ((1+t)^(n+1)/t^(k+1)) * M^k/(k.factorial:ℝ) =
        ((1+t)^(n+1)/t) * ((M/t)^k/(k.factorial:ℝ)) := by
      simp only [div_eq_mul_inv, mul_pow, inv_pow, pow_succ]
      ring
    have habs : |opLaguerreCoefficient n k * x^k| =
        ((n+1).choose (k+1):ℝ) * x^k/(k.factorial:ℝ) := by
      simp only [opLaguerreCoefficient, abs_mul, abs_div, abs_pow,
        abs_of_nonneg hx, abs_of_nonneg hc,
        abs_of_nonneg (le_of_lt hf), abs_pow, abs_neg, abs_one,
        one_pow, one_mul]
      ring
    rw [habs]
    exact hterm'.trans_eq halg
  have hseries : Summable (fun k : ℕ => (M/t)^k/(k.factorial:ℝ)) := by
    simpa only [← Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ℝ (M/t)).summable
  have hpartial :
      (∑ k ∈ Finset.range (n+1), (M/t)^k/(k.factorial:ℝ)) ≤
        Real.exp (M/t) := by
    calc
      _ ≤ ∑' k : ℕ, (M/t)^k/(k.factorial:ℝ) :=
        sum_le_tsum _ (fun k hk => div_nonneg (pow_nonneg (div_nonneg hM ht.le) _)
          (Nat.cast_nonneg _)) hseries
      _ = Real.exp (M/t) := by
        simpa only [← Real.exp_eq_exp_ℝ] using
          (NormedSpace.expSeries_div_hasSum_exp ℝ (M/t)).tsum_eq
  calc
    |opLaguerre n x| ≤
        ∑ k ∈ Finset.range (n+1), |opLaguerreCoefficient n k * x^k| := by
      simpa only [opLaguerre, Real.norm_eq_abs] using
        (norm_sum_le (Finset.range (n+1))
          (fun k => opLaguerreCoefficient n k * x^k))
    _ ≤ ∑ k ∈ Finset.range (n+1),
        ((1+t)^(n+1)/t) * ((M/t)^k/(k.factorial:ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hterm k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    _ = ((1+t)^(n+1)/t) *
        (∑ k ∈ Finset.range (n+1), (M/t)^k/(k.factorial:ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ ((1+t)^(n+1)/t) * Real.exp (M/t) := by
      exact mul_le_mul_of_nonneg_left hpartial (div_nonneg (pow_nonneg (by linarith) _) ht.le)

/-- The paper's spectral series converges uniformly on every bounded
positive rectangle, by a tunable geometric Laguerre coefficient bound. -/
theorem laguerre_heat_series_uniform_on_box {r M : ℝ}
    (hr : 0 < r) (hr' : r < 1) (hM : 0 ≤ M) :
    TendstoUniformlyOn
      (fun N : ℕ => fun z : ℝ × ℝ =>
        ∑ n ∈ Finset.range N,
          (r^n/(n+1:ℝ)) * opLaguerre n z.1 * opLaguerre n z.2)
      (fun z : ℝ × ℝ =>
        ∑' n : ℕ, (r^n/(n+1:ℝ)) * opLaguerre n z.1 * opLaguerre n z.2)
      atTop {z : ℝ × ℝ | 0 ≤ z.1 ∧ z.1 ≤ M ∧ 0 ≤ z.2 ∧ z.2 ≤ M} := by
  let d := 1-r
  let t := d/4
  let q := 1+t
  let ρ := r*q^2
  let B := (q/t * Real.exp (M/t))^2
  have hd : 0 < d ∧ d < 1 := by dsimp [d]; constructor <;> linarith
  have ht : 0 < t := div_pos hd.1 (by norm_num)
  have hq : 0 < q := by dsimp [q]; linarith
  have hqbound : q^2 ≤ 1+d := by
    dsimp [q, t]
    have hdd : d^2 ≤ d := by nlinarith [mul_nonneg hd.1.le (sub_nonneg.mpr hd.2.le)]
    nlinarith
  have hρ : 0 ≤ ρ ∧ ρ < 1 := by
    constructor
    · dsimp [ρ]; positivity
    · have hmul : r*q^2 ≤ r*(1+d) :=
        mul_le_mul_of_nonneg_left hqbound hr.le
      have hsquare : 0 < d^2 := sq_pos_of_pos hd.1
      dsimp [ρ, d] at *
      nlinarith
  have hsum : Summable (fun n : ℕ => B*ρ^n) :=
    (summable_geometric_of_lt_one hρ.1 hρ.2).mul_left B
  apply tendstoUniformlyOn_tsum_nat hsum
  intro n z hz
  have hx : |opLaguerre n z.1| ≤ q^(n+1)/t * Real.exp (M/t) := by
    simpa only [q] using op_laguerre_geometric_bound ht hM hz.1 hz.2.1 n
  have hy : |opLaguerre n z.2| ≤ q^(n+1)/t * Real.exp (M/t) := by
    simpa only [q] using op_laguerre_geometric_bound ht hM hz.2.2.1 hz.2.2.2 n
  have hD : 0 ≤ q/t * Real.exp (M/t) := by positivity
  have hLx : |opLaguerre n z.1| ≤ (q/t * Real.exp (M/t))*q^n := by
    calc
      |opLaguerre n z.1| ≤ q^(n+1)/t * Real.exp (M/t) := hx
      _ = (q/t * Real.exp (M/t))*q^n := by rw [pow_succ]; ring
  have hLy : |opLaguerre n z.2| ≤ (q/t * Real.exp (M/t))*q^n := by
    calc
      |opLaguerre n z.2| ≤ q^(n+1)/t * Real.exp (M/t) := hy
      _ = (q/t * Real.exp (M/t))*q^n := by rw [pow_succ]; ring
  have hden : (1:ℝ) ≤ (n+1:ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hcoef : r^n/(n+1:ℝ) ≤ r^n := by
    exact (div_le_iff₀ (by linarith)).2 (by
      nlinarith [mul_nonneg (pow_nonneg hr.le n) (sub_nonneg.mpr hden)])
  have hcoef0 : 0 ≤ r^n/(n+1:ℝ) := by positivity
  change ‖(r^n/(n+1:ℝ))*opLaguerre n z.1*opLaguerre n z.2‖ ≤ B*ρ^n
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hcoef0]
  have hproduct : |opLaguerre n z.1| * |opLaguerre n z.2| ≤
      ((q/t*Real.exp (M/t))*q^n)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hLx) (abs_nonneg (opLaguerre n z.2)),
      mul_nonneg (sub_nonneg.mpr hLy)
        (show 0 ≤ (q/t*Real.exp (M/t))*q^n by positivity)]
  calc
    r^n/(n+1:ℝ) * |opLaguerre n z.1| * |opLaguerre n z.2| ≤
        r^n * (((q/t*Real.exp (M/t))*q^n)^2) := by
      calc
        _ = (r^n/(n+1:ℝ)) *
            (|opLaguerre n z.1| * |opLaguerre n z.2|) := by ring
        _ ≤ r^n * (|opLaguerre n z.1| * |opLaguerre n z.2|) :=
          mul_le_mul_of_nonneg_right hcoef
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ ≤ r^n * (((q/t*Real.exp (M/t))*q^n)^2) :=
          mul_le_mul_of_nonneg_left hproduct (pow_nonneg hr.le n)
    _ = B*ρ^n := by
      change r^n * (((q/t*Real.exp (M/t))*q^n)^2) =
        (q/t*Real.exp (M/t))^2 * (r*q^2)^n
      have hpow : (q^n)^2 = (q^2)^n := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      rw [mul_pow r (q^2) n,
        mul_pow (q/t*Real.exp (M/t)) (q^n) 2, hpow]
      ring

/-- Local uniform convergence of the exact paper spectral series on
the positive quadrant, including arbitrary heat times `τ > 0`. -/
theorem laguerre_heat_series_locally_uniform {τ : ℝ} (hτ : 0 < τ) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun z : ℝ × ℝ =>
        ∑ n ∈ Finset.range N,
          (Real.exp (-τ)^n/(n+1:ℝ)) * opLaguerre n z.1 * opLaguerre n z.2)
      (fun z : ℝ × ℝ =>
        ∑' n : ℕ, (Real.exp (-τ)^n/(n+1:ℝ)) *
          opLaguerre n z.1 * opLaguerre n z.2)
      atTop {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2} := by
  have hopen : IsOpen {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2} :=
    (isOpen_Ioi.preimage continuous_fst).inter
      (isOpen_Ioi.preimage continuous_snd)
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).2
  intro K hK hcompact
  obtain ⟨Mx, hMx⟩ := (hcompact.image continuous_fst).bddAbove
  obtain ⟨My, hMy⟩ := (hcompact.image continuous_snd).bddAbove
  let M := max 0 (max Mx My)
  have hM : 0 ≤ M := le_max_left _ _
  have hsub : K ⊆ {z : ℝ × ℝ |
      0 ≤ z.1 ∧ z.1 ≤ M ∧ 0 ≤ z.2 ∧ z.2 ≤ M} := by
    intro z hz
    have hzpos := hK hz
    have hxmax : z.1 ≤ Mx := hMx ⟨z, hz, rfl⟩
    have hymax : z.2 ≤ My := hMy ⟨z, hz, rfl⟩
    exact ⟨hzpos.1.le, le_trans hxmax (le_trans (le_max_left _ _) (le_max_right _ _)),
      hzpos.2.le, le_trans hymax (le_trans (le_max_right _ _) (le_max_right _ _))⟩
  exact (laguerre_heat_series_uniform_on_box (Real.exp_pos _)
    (by rw [Real.exp_lt_one_iff]; linarith) hM).mono hsub

private theorem op_laguerre_zero (n : ℕ) : opLaguerre n 0 = (n+1:ℝ) := by
  unfold opLaguerre
  rw [Finset.sum_eq_single 0]
  · simp [opLaguerreCoefficient]
  · intro k hk hk0
    simp [hk0]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

/-- The Laguerre generating series is uniformly convergent on bounded
positive intervals, obtained from the two-variable kernel estimate at `y=0`. -/
theorem laguerre_generating_series_uniform_on_box {q M : ℝ}
    (hq : 0 < q) (hq' : q < 1) (hM : 0 ≤ M) :
    TendstoUniformlyOn
      (fun N : ℕ => fun x : ℝ =>
        ∑ n ∈ Finset.range N, q^n * opLaguerre n x)
      (fun x : ℝ => ∑' n : ℕ, q^n * opLaguerre n x)
      atTop (Set.Icc 0 M) := by
  have h := laguerre_heat_series_uniform_on_box hq hq' hM
  have hcomp : Set.MapsTo (fun x : ℝ => (x, (0:ℝ))) (Set.Icc 0 M)
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ z.1 ≤ M ∧ 0 ≤ z.2 ∧ z.2 ≤ M} := by
    intro x hx
    exact ⟨hx.1, hx.2, le_rfl, hM⟩
  have h' := (h.comp (fun x : ℝ => (x, (0:ℝ)))).mono hcomp
  convert h' using 1
  · funext N x
    apply Finset.sum_congr rfl
    intro n hn
    rw [op_laguerre_zero]
    field_simp [(by positivity : (n+1:ℝ) ≠ 0)]
  · funext x
    apply tsum_congr
    intro n
    rw [op_laguerre_zero]
    field_simp [(by positivity : (n+1:ℝ) ≠ 0)]

theorem laguerre_generating_function_mem_l2 {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1/4) :
    Memℒp (fun y : ℝ => (laguerreGeneratingFunction z y : ℂ)) 2 gammaProbability := by
  have hden : 0 < 1-z := by linarith
  have hs0 : 0 ≤ 2*z/(1-z) := div_nonneg (by positivity) hden.le
  have hs : -1 < 2*z/(1-z) := by linarith
  have hg : Continuous (fun y : ℝ => laguerreGeneratingFunction z y) := by
    unfold laguerreGeneratingFunction
    fun_prop
  have hc : Continuous (fun y : ℝ => (laguerreGeneratingFunction z y : ℂ)) :=
    Complex.continuous_ofReal.comp hg
  apply (memℒp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hgpos (y : ℝ) : 0 ≤ laguerreGeneratingFunction z y := by
    unfold laguerreGeneratingFunction
    positivity
  have hpoint : (fun y : ℝ => ‖(laguerreGeneratingFunction z y : ℂ)‖^2) =
      fun y => (1-z)⁻¹^4 * (Real.exp (-((2*z/(1-z))*y))) := by
    funext y
    have he : (-y*z/(1-z)) + (-y*z/(1-z)) = -((2*z/(1-z))*y) := by
      field_simp [hden.ne']
      ring
    calc
      ‖(laguerreGeneratingFunction z y : ℂ)‖^2 =
          laguerreGeneratingFunction z y ^ 2 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hgpos y)]
      _ = (1-z)⁻¹^4 * Real.exp ((-y*z/(1-z))+(-y*z/(1-z))) := by
            unfold laguerreGeneratingFunction
            rw [mul_pow, ← pow_mul, pow_two, ← Real.exp_add]
      _ = _ := by rw [he]
  rw [hpoint]
  simpa only [pow_zero, mul_one] using
    (gamma_probability_exp_monomial_integrable hs 0).const_mul ((1-z)⁻¹^4)

def laguerreGeneratingVector (z : ℝ) (hz : 0 ≤ z) (hz' : z < 1/4) :
    LaguerreWeightedHilbert :=
  (laguerre_generating_function_mem_l2 hz hz').toLp
    (fun y : ℝ => (laguerreGeneratingFunction z y : ℂ))

private theorem laguerre_generating_function_monomial_integral {z : ℝ}
    (hz : 0 ≤ z) (hz' : z < 1/4) (k : ℕ) :
    (∫ y : ℝ, y^k * laguerreGeneratingFunction z y ∂gammaProbability) =
      ((k+1).factorial:ℝ) * (1-z)^k := by
  have hden : 0 < 1-z := by linarith
  let s := z/(1-z)
  have hs0 : 0 ≤ s := by dsimp [s]; exact div_nonneg hz hden.le
  have hs : -1 < s := by linarith
  have h1s : 1+s = (1-z)⁻¹ := by
    dsimp [s]
    field_simp [hden.ne']
  have hfun : (fun y : ℝ => y^k * laguerreGeneratingFunction z y) =
      fun y => (1-z)⁻¹^2 * (Real.exp (-(s*y))*y^k) := by
    funext y
    dsimp [laguerreGeneratingFunction]
    have he : -y*z/(1-z) = -(s*y) := by dsimp [s]; ring
    rw [he]
    ring
  rw [hfun, integral_mul_left, gamma_probability_exp_monomial_integral k hs, h1s]
  field_simp [hden.ne']
  ring

private theorem laguerre_generating_function_laguerre_integral {z : ℝ}
    (hz : 0 ≤ z) (hz' : z < 1/4) (n : ℕ) :
    (∫ y : ℝ, opLaguerre n y * laguerreGeneratingFunction z y ∂gammaProbability) =
      (n+1:ℝ)*z^n := by
  have hi (k : ℕ) : Integrable
      (fun y : ℝ => opLaguerreCoefficient n k *
        (y^k * laguerreGeneratingFunction z y)) gammaProbability := by
    have hnonzero : (∫ y : ℝ, y^k * laguerreGeneratingFunction z y ∂gammaProbability) ≠ 0 := by
      rw [laguerre_generating_function_monomial_integral hz hz' k]
      exact mul_ne_zero (by positivity) (pow_ne_zero k (ne_of_gt (by linarith)))
    exact (Integrable.of_integral_ne_zero hnonzero).const_mul _
  have hsum : (fun y : ℝ => opLaguerre n y * laguerreGeneratingFunction z y) =
      fun y => ∑ k ∈ Finset.range (n+1), opLaguerreCoefficient n k *
        (y^k * laguerreGeneratingFunction z y) := by
    funext y
    simp only [opLaguerre, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsum, integral_finset_sum (Finset.range (n+1)) (fun k _ => hi k)]
  simp_rw [integral_mul_left, laguerre_generating_function_monomial_integral hz hz']
  calc
    _ = ∑ k ∈ Finset.range (n+1),
        (opLaguerreCoefficient n k * ((k+1).factorial:ℝ)) * (1-z)^k := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = ∑ k ∈ Finset.range (n+1),
        (n+1:ℝ) * ((-1:ℝ)^k * (n.choose k:ℝ)) * (1-z)^k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [opLaguerre_coefficient_factorial]
    _ = (n+1:ℝ) * ∑ k ∈ Finset.range (n+1),
        (-1:ℝ)^k * (n.choose k:ℝ) * (1-z)^k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = (n+1:ℝ)*z^n := by
          have hbin : ∑ k ∈ Finset.range (n+1),
              (-1:ℝ)^k * (n.choose k:ℝ) * (1-z)^k = z^n := by
            have hsub := sub_pow (1-z) (1:ℝ) n
            rw [show (1-z)-1 = -z by ring, neg_pow] at hsub
            have hfactor :
                (∑ k ∈ Finset.range (n+1),
                  (-1:ℝ)^(k+n) * (1-z)^k * (1:ℝ)^(n-k) * (n.choose k:ℝ)) =
                (-1:ℝ)^n * ∑ k ∈ Finset.range (n+1),
                  (-1:ℝ)^k * (n.choose k:ℝ) * (1-z)^k := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k hk
              rw [show k+n=n+k by omega, pow_add]
              simp only [one_pow]
              ring
            rw [hfactor] at hsub
            exact (mul_left_cancel₀ (pow_ne_zero n (by norm_num)) hsub).symm
          rw [hbin]

theorem laguerre_generating_vector_coordinate {z : ℝ} (hz : 0 ≤ z)
    (hz' : z < 1/4) (n : ℕ) :
    laguerreHilbertBasis.repr (laguerreGeneratingVector z hz hz') n =
      (Complex.ofReal ((n+1:ℝ)/Real.sqrt (n+1))) * (z:ℂ)^n := by
  rw [HilbertBasis.repr_apply_apply, laguerre_hilbert_basis_apply,
    normalizedLaguerreL2Vector]
  rw [inner_smul_left]
  simp only [map_inv₀, Complex.conj_ofReal]
  rw [laguerre_l2_inner_integral]
  have hfun :
      (laguerreGeneratingVector z hz hz' : ℝ → ℂ) =ᵐ[gammaProbability]
        fun y => (laguerreGeneratingFunction z y : ℂ) :=
    (laguerre_generating_function_mem_l2 hz hz').coeFn_toLp
  rw [show (∫ y : ℝ, (opLaguerre n y : ℂ) *
      (laguerreGeneratingVector z hz hz' : ℝ → ℂ) y ∂gammaProbability) =
      Complex.ofReal ((n+1:ℝ)*z^n) by
        rw [integral_congr_ae]
        · have hs : -1 < z/(1-z) := by
            have hd : 0 < 1-z := by linarith
            rw [lt_div_iff₀ hd]
            linarith
          have hi : Integrable (fun y : ℝ => opLaguerre n y * laguerreGeneratingFunction z y)
              gammaProbability := by
            let F : ℕ → ℝ → ℝ := fun k y =>
              opLaguerreCoefficient n k * (y^k * laguerreGeneratingFunction z y)
            have hbase (k : ℕ) :
                Integrable (fun y : ℝ => y^k * laguerreGeneratingFunction z y)
                  gammaProbability := by
              have he (y : ℝ) : -y*z/(1-z) = -(z/(1-z)*y) := by
                field_simp [ne_of_gt (show 0 < 1-z by linarith)]
                ring
              have h0 := (gamma_probability_exp_monomial_integrable hs k).const_mul
                ((1-z)⁻¹^2)
              apply h0.congr
              filter_upwards with y
              unfold laguerreGeneratingFunction
              rw [he]
              ring
            have hsum : (fun y : ℝ => opLaguerre n y * laguerreGeneratingFunction z y) =
                fun y => ∑ k ∈ Finset.range (n+1), F k y := by
              funext y
              simp only [F, opLaguerre, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro k hk
              ring
            rw [hsum]
            apply integrable_finset_sum
            intro k hk
            exact (hbase k).const_mul _
          have hc := Complex.ofRealCLM.integral_comp_comm hi
          rw [hc]
          exact congrArg Complex.ofReal
            (laguerre_generating_function_laguerre_integral hz hz' n)
        · filter_upwards [hfun] with y hy
          rw [hy]
          simp]
  have hn : 0 < (n+1:ℝ) := by positivity
  field_simp [ne_of_gt (Real.sqrt_pos.mpr hn)]
  have hreal : (n+1:ℝ)*z^n =
      Real.sqrt (n+1)*z^n*Real.sqrt (n+1) := by
    calc
      (n+1:ℝ)*z^n = Real.sqrt (n+1)^2*z^n := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ (n+1:ℝ))]
      _ = Real.sqrt (n+1)*z^n*Real.sqrt (n+1) := by ring
  exact_mod_cast hreal

theorem laguerre_generating_vector_heat_action {z τ : ℝ} (hz : 0 ≤ z)
    (hz' : z < 1/4) (hτ : 0 < τ) :
    laguerreHeatOperator τ hτ.le (laguerreGeneratingVector z hz hz') =
      laguerreGeneratingVector (Real.exp (-τ)*z)
        (mul_nonneg (Real.exp_nonneg _) hz)
        (by have hr : Real.exp (-τ) < 1 := by
              rw [Real.exp_lt_one_iff]
              linarith
            nlinarith [Real.exp_pos (-τ), hz', hz]) := by
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext n
  rw [laguerre_heat_coordinate, laguerre_generating_vector_coordinate,
    laguerre_generating_vector_coordinate]
  have hr : Real.exp (-τ*(n:ℝ)) = (Real.exp (-τ))^n := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hr]
  push_cast
  rw [mul_pow]
  ring

private def laguerreSmallGeneratingSet : Set LaguerreWeightedHilbert :=
  Set.range (fun z : {x : ℝ // 0 < x ∧ x < (1/4:ℝ)} =>
    laguerreGeneratingVector z.1 (le_of_lt z.2.1) z.2.2)

private def laguerreSmallGeneratingSpan : Submodule ℂ LaguerreWeightedHilbert :=
  Submodule.span ℂ laguerreSmallGeneratingSet

/-- Positive-parameter generating vectors are total in the actual Gamma-weighted
Laguerre Hilbert space. This follows from coefficient uniqueness of their
explicit complete-basis coordinates, not from a scalar proxy. -/
theorem laguerre_generating_vectors_dense :
    laguerreSmallGeneratingSpan.topologicalClosure = ⊤ := by
  have horth : laguerreSmallGeneratingSpanᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro f hf
    let a : ℕ → ℂ := fun n => star (laguerreHilbertBasis.repr f n) *
      Complex.ofReal ((n+1:ℝ)/Real.sqrt (n+1))
    have hfsquare : Summable (fun n => ‖laguerreHilbertBasis.repr f n‖^2) := by
      have hs := (laguerreHilbertBasis.repr f).property.summable
        (by norm_num : 0 < (2:ℝ≥0∞).toReal)
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs
    have hgeo : Summable (fun n : ℕ => (n+1:ℝ)*(1/4:ℝ)^(2*n)) := by
      have hq : ‖(1/16:ℝ)‖ < 1 := by norm_num
      have hs := (hasSum_choose_mul_geometric_of_norm_lt_one (1:ℕ) hq).summable
      have heq : (fun n : ℕ => (n+1:ℝ)*(1/4:ℝ)^(2*n)) =
          fun n => ((n+1).choose 1:ℝ)*(1/16:ℝ)^n := by
        funext n
        rw [pow_mul]
        norm_num
      rw [heq]
      exact hs
    have hweight : Summable (fun n => ‖a n‖*(1/4:ℝ)^n) := by
      apply Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (by positivity))
        (fun n => ?_) (hfsquare.add hgeo)
      let u : ℝ := ‖laguerreHilbertBasis.repr f n‖
      let v : ℝ := Real.sqrt (n+1)*(1/4:ℝ)^n
      have hn : 0 < (n+1:ℝ) := by positivity
      have hroot : Real.sqrt (n+1)^2 = n+1 :=
        Real.sq_sqrt (by positivity : 0 ≤ (n+1:ℝ))
      have hcoef : (n+1:ℝ)/Real.sqrt (n+1) = Real.sqrt (n+1) := by
        field_simp [ne_of_gt (Real.sqrt_pos.mpr hn)]
      have hnorm : ‖a n‖*(1/4:ℝ)^n = u*v := by
        simp [a, u, v, norm_mul, Complex.norm_real, hcoef,
          abs_of_nonneg (Real.sqrt_nonneg _)]
        ring
      have hv2 : v^2 = (n+1:ℝ)*(1/4:ℝ)^(2*n) := by
        dsimp [v]
        rw [mul_pow, hroot, ← pow_mul]
        rw [show n*2=2*n by omega]
      have hu : 0 ≤ u := by positivity
      have hv : 0 ≤ v := by positivity
      rw [hnorm]
      nlinarith [sq_nonneg (u-v)]
    have hrepr (z : ℝ) (hz : 0 ≤ z) (hz' : z < 1/4) :
        (∑' n : ℕ, a n*(z:ℂ)^n) =
          @inner ℂ LaguerreWeightedHilbert _ f (laguerreGeneratingVector z hz hz') := by
      rw [← laguerreHilbertBasis.repr.inner_map_map, lp.inner_eq_tsum]
      apply tsum_congr
      intro n
      rw [laguerre_generating_vector_coordinate hz hz' n]
      simp [a, RCLike.inner_apply, Complex.conj_ofReal, mul_assoc]
    have hcoeff : ∀ n, a n = 0 := by
      apply power_series_coefficients_zero (R:=1/4) (by norm_num) hweight
      intro z hz hz'
      have hv : laguerreGeneratingVector z (le_of_lt hz) hz' ∈ laguerreSmallGeneratingSpan :=
        Submodule.subset_span ⟨⟨z, ⟨hz, hz'⟩⟩, rfl⟩
      have h0 := hf _ hv
      rw [hrepr z (le_of_lt hz) hz']
      exact inner_eq_zero_symm.mp h0
    have hcoord (n : ℕ) : laguerreHilbertBasis.repr f n = 0 := by
      have hm : star (laguerreHilbertBasis.repr f n) *
          Complex.ofReal ((n+1:ℝ)/Real.sqrt (n+1)) = 0 := by
        simpa [a] using hcoeff n
      have hc : Complex.ofReal ((n+1:ℝ)/Real.sqrt (n+1)) ≠ 0 := by
        apply Complex.ofReal_ne_zero.mpr
        positivity
      rcases mul_eq_zero.mp hm with hstar | hzero
      · have := congrArg star hstar
        simpa using this
      · exact (hc hzero).elim
    apply laguerreHilbertBasis.repr.injective
    apply lp.ext
    funext n
    simpa using hcoord n
  rw [← Submodule.orthogonal_orthogonal_eq_closure, horth]
  simp

private theorem lp_coe_ae_eq_of_eq {α E : Type*} [MeasurableSpace α]
    {p : ℝ≥0∞} {μ : Measure α} [NormedAddCommGroup E] {f g : Lp E p μ}
    (h : f = g) : (f : α → E) =ᵐ[μ] (g : α → E) := by
  have hv : f.1 = g.1 := congrArg Subtype.val h
  rw [← f.1.mk_coeFn, ← g.1.mk_coeFn] at hv
  exact AEEqFun.mk_eq_mk.mp hv

/-- The closed kernel's integral transform agrees with the actual native heat
operator on the generating family of the complete Laguerre basis. -/
theorem laguerre_heat_kernel_transform_is_semigroup_on_generators
    {τ z : ℝ} (hτ : 0 < τ) (hz : 0 ≤ z) (hz' : z < 1/4) :
    (fun x => ((∫ y : ℝ, laguerreHeatKernel τ x y * laguerreGeneratingFunction z y
      ∂gammaProbability : ℝ) : ℂ)) =ᵐ[gammaProbability]
      fun x => ((laguerreHeatOperator τ hτ.le
        (laguerreGeneratingVector z hz hz') x : ℂ)) := by
  let rz := Real.exp (-τ)*z
  have hr : 0 < Real.exp (-τ) ∧ Real.exp (-τ) < 1 := by
    constructor
    · exact Real.exp_pos _
    · rw [Real.exp_lt_one_iff]
      linarith
  have hrz : 0 ≤ rz := mul_nonneg hr.1.le hz
  have hrz' : rz < 1/4 := by
    dsimp [rz]
    have hle : Real.exp (-τ) * z ≤ z := by
      nlinarith [mul_nonneg hz (sub_nonneg.mpr hr.2.le)]
    linarith
  have hd : 0 < 1-Real.exp (-τ) := by linarith
  have hbeta : 0 ≤ Real.exp (-τ)/(1-Real.exp (-τ))+z/(1-z) :=
    add_nonneg (div_nonneg hr.1.le hd.le) (div_nonneg hz (by linarith))
  have hvec := laguerre_generating_vector_heat_action hz hz' hτ
  have hrep : (laguerreHeatOperator τ hτ.le (laguerreGeneratingVector z hz hz') :
      ℝ → ℂ) =ᵐ[gammaProbability]
      fun x => (laguerreGeneratingFunction rz x : ℂ) := by
    exact (lp_coe_ae_eq_of_eq hvec).trans
      ((laguerre_generating_function_mem_l2 hrz hrz').coeFn_toLp)
  have hpos : ∀ᵐ x : ℝ ∂gammaProbability, 0 < x := by
    have hnonneg : ∀ᵐ x : ℝ ∂gammaProbability, 0 ≤ x := by
      simpa only [ae_iff, not_le] using gamma_probability_negative_ray
    have hne : ∀ᵐ x : ℝ ∂gammaProbability, x ≠ 0 := by
      rw [ae_iff]
      simpa only [not_ne_iff, Set.setOf_eq_eq_singleton] using gamma_probability_no_atom 0
    filter_upwards [hnonneg, hne] with x hx hxn
    exact lt_of_le_of_ne hx (Ne.symm hxn)
  filter_upwards [hpos, hrep] with x hx hfx
  have hk := laguerre_heat_kernel_generating_transform hτ hx
    (lt_trans hz' (by norm_num : (1/4:ℝ) < 1)) hbeta
  exact (congrArg Complex.ofReal hk).trans hfx.symm

abbrev LaguerreProductHilbert := Lp ℝ 2 (gammaProbability.prod gammaProbability)

private theorem laguerre_product_square_integrable (n : ℕ) :
    Integrable (fun z : ℝ × ℝ =>
      (opLaguerre n z.1)^2 * (opLaguerre n z.2)^2)
      (gammaProbability.prod gammaProbability) := by
  have h1 : Integrable (fun x : ℝ => (opLaguerre n x)^2) gammaProbability := by
    convert gamma_polynomial_integrable ((opLaguerrePolynomial n)^2) using 1
    funext x
    rw [Polynomial.eval_pow, ← op_laguerre_polynomial_eval]
  exact h1.prod_mul h1

private def laguerreHeatKernelSpectralTermFun (r : ℝ) (n : ℕ) (z : ℝ × ℝ) : ℝ :=
  (r^n/(n+1:ℝ)) * (opLaguerre n z.1) * (opLaguerre n z.2)

private theorem laguerre_heat_kernel_spectral_term_mem (r : ℝ) (n : ℕ) :
    Memℒp (laguerreHeatKernelSpectralTermFun r n) 2
      (gammaProbability.prod gammaProbability) := by
  have hm : AEStronglyMeasurable (laguerreHeatKernelSpectralTermFun r n)
      (gammaProbability.prod gammaProbability) := by
    change AEStronglyMeasurable (fun z : ℝ × ℝ =>
      (r^n/(n+1:ℝ)) * (opLaguerre n z.1) * (opLaguerre n z.2)) _
    have hl : Continuous (fun x : ℝ => opLaguerre n x) := by
      convert (opLaguerrePolynomial n).continuous using 1
      funext x
      exact (op_laguerre_polynomial_eval n x).symm
    have hc : Continuous (fun z : ℝ × ℝ =>
        (r^n/(n+1:ℝ)) * (opLaguerre n z.1) * (opLaguerre n z.2)) :=
      (continuous_const.mul (hl.comp continuous_fst)).mul (hl.comp continuous_snd)
    exact hc.aestronglyMeasurable
  apply (memℒp_two_iff_integrable_sq hm).mpr
  have hp := (laguerre_product_square_integrable n).const_mul
    ((r^n/(n+1:ℝ))^2)
  convert hp using 1
  funext z
  simp only [laguerreHeatKernelSpectralTermFun]
  ring

/-- The nth summand of the paper's Laguerre spectral kernel, regarded as an
actual vector in the weighted product L² space. -/
def laguerreHeatKernelSpectralTerm (r : ℝ) (n : ℕ) : LaguerreProductHilbert :=
  (laguerre_heat_kernel_spectral_term_mem r n).toLp
    (laguerreHeatKernelSpectralTermFun r n)

theorem laguerre_heat_kernel_spectral_term_norm {r : ℝ} (hr : 0 ≤ r)
    (n : ℕ) : ‖laguerreHeatKernelSpectralTerm r n‖ = r^n := by
  have hnormsq : ‖laguerreHeatKernelSpectralTerm r n‖^2 = r^(2*n) := by
    have hns := norm_sq_eq_inner (𝕜 := ℝ) (laguerreHeatKernelSpectralTerm r n)
    rw [hns, L2.inner_def]
    rw [integral_congr_ae]
    · rw [integral_mul_left, integral_prod_mul]
      have ho := op_laguerre_pair_integral n n
      simp only [if_pos rfl] at ho
      rw [ho]
      have hc : ((r^n/(n+1:ℝ)) * (r^n/(n+1:ℝ))) *
          ((n+1:ℝ)*(n+1)) = r^(2*n) := by
        have hn : (n+1:ℝ) ≠ 0 := by positivity
        field_simp
        calc
          r^n*r^n = (r^n)^2 := by rw [← pow_two]
          _ = r^(n*2) := by rw [pow_mul]
          _ = r^(2*n) := by rw [Nat.mul_comm]
      exact hc
    · have hrep := (laguerre_heat_kernel_spectral_term_mem r n).coeFn_toLp
      filter_upwards [hrep] with z hz
      change laguerreHeatKernelSpectralTerm r n z = _ at hz
      rw [hz]
      simp only [laguerreHeatKernelSpectralTermFun]
      simp [RCLike.inner_apply]
      ring
  have hnonneg : 0 ≤ ‖laguerreHeatKernelSpectralTerm r n‖ := norm_nonneg _
  have hrpow : 0 ≤ r^n := pow_nonneg hr n
  have hsq : r^(2*n) = (r^n)^2 := by
    calc
      r^(2*n) = r^(n*2) := by rw [Nat.mul_comm]
      _ = (r^n)^2 := by rw [pow_mul]
  rw [hsq] at hnormsq
  nlinarith [hnormsq]

/-- The spectral kernel series converges in the exact weighted product L²
space, with the paper's sharp geometric norm estimate. -/
theorem laguerre_heat_kernel_spectral_series_summable {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (laguerreHeatKernelSpectralTerm r) := by
  have hn : Summable (fun n : ℕ => ‖laguerreHeatKernelSpectralTerm r n‖) := by
    simpa only [laguerre_heat_kernel_spectral_term_norm hr0] using
      (summable_geometric_of_lt_one hr0 hr1)
  exact hn.of_norm

def laguerreHeatKernelSpectralSeries (r : ℝ) : LaguerreProductHilbert :=
  ∑' n : ℕ, laguerreHeatKernelSpectralTerm r n

theorem laguerre_heat_kernel_spectral_series_tendsto {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      laguerreHeatKernelSpectralTerm r n) atTop
      (𝓝 (laguerreHeatKernelSpectralSeries r)) :=
  (laguerre_heat_kernel_spectral_series_summable hr0 hr1).hasSum.tendsto_sum_nat

private theorem laguerre_spectral_partial_sum_coe_ae (r : ℝ) (N : ℕ) :
    ((∑ n ∈ Finset.range N, laguerreHeatKernelSpectralTerm r n :
      LaguerreProductHilbert) : ℝ × ℝ → ℝ) =ᵐ[
      gammaProbability.prod gammaProbability]
      fun z => ∑ n ∈ Finset.range N,
        (r^n/(n+1:ℝ)) * opLaguerre n z.1 * opLaguerre n z.2 := by
  induction N with
  | zero =>
      simp only [Finset.sum_range_zero]
      exact Filter.Eventually.of_forall (fun z => by simp)
  | succ N ih =>
      simp only [Finset.sum_range_succ]
      have hadd := Lp.coeFn_add
        (∑ n ∈ Finset.range N, laguerreHeatKernelSpectralTerm r n)
        (laguerreHeatKernelSpectralTerm r N)
      have hterm := (laguerre_heat_kernel_spectral_term_mem r N).coeFn_toLp
      filter_upwards [hadd, ih, hterm] with z h₁ h₂ h₃
      change laguerreHeatKernelSpectralTerm r N z = _ at h₃
      simp only [laguerreHeatKernelSpectralTermFun] at h₃
      rw [h₁, Pi.add_apply, h₂, h₃]

/-- The locally uniformly convergent pointwise spectral series is the
representative of the already constructed weighted product-`L²` sum. -/
theorem laguerre_heat_kernel_spectral_series_represents {τ : ℝ} (hτ : 0 < τ) :
    (laguerreHeatKernelSpectralSeries (Real.exp (-τ)) : ℝ × ℝ → ℝ) =ᵐ[
      gammaProbability.prod gammaProbability]
      (fun z => ∑' n : ℕ,
        (Real.exp (-τ)^n/(n+1:ℝ)) * opLaguerre n z.1 * opLaguerre n z.2) := by
  let r := Real.exp (-τ)
  let μ := gammaProbability.prod gammaProbability
  let S : ℕ → LaguerreProductHilbert := fun N =>
    ∑ n ∈ Finset.range N, laguerreHeatKernelSpectralTerm r n
  let f : ℕ → ℝ × ℝ → ℝ := fun N z =>
    ∑ n ∈ Finset.range N,
      (r^n/(n+1:ℝ)) * opLaguerre n z.1 * opLaguerre n z.2
  let g : ℝ × ℝ → ℝ := fun z =>
    ∑' n : ℕ, (r^n/(n+1:ℝ)) * opLaguerre n z.1 * opLaguerre n z.2
  have hS : Tendsto S atTop (𝓝 (laguerreHeatKernelSpectralSeries r)) :=
    laguerre_heat_kernel_spectral_series_tendsto (Real.exp_pos _).le
      (by dsimp [r]; rw [Real.exp_lt_one_iff]; linarith)
  have hmeasure := tendstoInMeasure_of_tendsto_Lp hS
  obtain ⟨ns, hns, hae⟩ := hmeasure.exists_seq_tendsto_ae
  have hrepr : ∀ᵐ z : ℝ × ℝ ∂μ, ∀ N : ℕ, S N z = f N z := by
    rw [ae_all_iff]
    intro N
    exact laguerre_spectral_partial_sum_coe_ae r N
  have hpositive : ∀ᵐ z : ℝ × ℝ ∂μ, 0 < z.1 ∧ 0 < z.2 := by
    have hp : ∀ᵐ x : ℝ ∂gammaProbability, 0 < x := by
      have hn : ∀ᵐ x : ℝ ∂gammaProbability, 0 ≤ x := by
        simpa only [ae_iff, not_le] using gamma_probability_negative_ray
      have hne : ∀ᵐ x : ℝ ∂gammaProbability, x ≠ 0 := by
        rw [ae_iff]
        simpa only [not_ne_iff, Set.setOf_eq_eq_singleton] using
          gamma_probability_no_atom 0
      filter_upwards [hn, hne] with x hx hxn
      exact lt_of_le_of_ne hx (Ne.symm hxn)
    apply (Measure.ae_prod_iff_ae_ae (show MeasurableSet
      {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2} from
        (measurableSet_lt measurable_const measurable_fst).inter
          (measurableSet_lt measurable_const measurable_snd))).2
    filter_upwards [hp] with x hx
    filter_upwards [hp] with y hy
    exact ⟨hx, hy⟩
  filter_upwards [hae, hrepr, hpositive] with z hz hrep hpos
  have hpoint : Tendsto (fun N => f N z) atTop (𝓝 (g z)) :=
    (laguerre_heat_series_locally_uniform hτ).tendsto_at hpos
  have hsubseq : Tendsto ns atTop atTop := hns.tendsto_atTop
  have hpoint' : Tendsto (fun i => f (ns i) z) atTop (𝓝 (g z)) :=
    hpoint.comp hsubseq
  have hrewrite : (fun i => S (ns i) z) = fun i => f (ns i) z := by
    funext i
    exact hrep (ns i)
  rw [hrewrite] at hz
  change (laguerreHeatKernelSpectralSeries r : ℝ × ℝ → ℝ) z = g z
  exact tendsto_nhds_unique hz hpoint'

/-- The pointwise spectral kernel has the paper's large-time limit. -/
theorem laguerre_heat_spectral_series_tendsto_one {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun τ : ℝ => ∑' n : ℕ,
      (Real.exp (-τ)^n/(n+1:ℝ)) * opLaguerre n x * opLaguerre n y)
      atTop (𝓝 1) := by
  let M := max x y
  let t : ℝ := 1/4
  let q : ℝ := 1+t
  let C := q/t * Real.exp (M/t)
  let ρ : ℝ := (1/2)*q^2
  have hM : 0 ≤ M := le_trans hx.le (le_max_left _ _)
  have hq : 0 < q := by dsimp [q, t]; norm_num
  have hρ : 0 ≤ ρ ∧ ρ < 1 := by dsimp [ρ, q, t]; norm_num
  have hX (n : ℕ) : |opLaguerre n x| ≤ C*q^n := by
    have h := op_laguerre_geometric_bound
      (t := t) (M := M) (x := x) (by norm_num [t]) hM hx.le
      (le_max_left _ _) n
    calc
      |opLaguerre n x| ≤ q^(n+1)/t * Real.exp (M/t) := by simpa [q] using h
      _ = C*q^n := by dsimp [C]; rw [pow_succ]; ring
  have hY (n : ℕ) : |opLaguerre n y| ≤ C*q^n := by
    have h := op_laguerre_geometric_bound
      (t := t) (M := M) (x := y) (by norm_num [t]) hM hy.le
      (le_max_right _ _) n
    calc
      |opLaguerre n y| ≤ q^(n+1)/t * Real.exp (M/t) := by simpa [q] using h
      _ = C*q^n := by dsimp [C]; rw [pow_succ]; ring
  have hC : 0 ≤ C := by dsimp [C, q, t]; positivity
  have hsum : Summable (fun n : ℕ => C^2*ρ^n) :=
    (summable_geometric_of_lt_one hρ.1 hρ.2).mul_left _
  have hr : Tendsto (fun τ : ℝ => Real.exp (-τ)) atTop (𝓝 0) := by
    exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hlim (n : ℕ) :
      Tendsto (fun τ : ℝ => (Real.exp (-τ)^n/(n+1:ℝ)) *
        opLaguerre n x * opLaguerre n y) atTop
        (𝓝 (if n = 0 then 1 else 0)) := by
    by_cases hn : n = 0
    · subst n
      simp [opLaguerre_first_three]
    · have hpow : Tendsto (fun τ : ℝ => Real.exp (-τ)^n) atTop (𝓝 0) := by
        simpa [hn] using hr.pow n
      have h := (hpow.div_const (n+1:ℝ)).mul_const (opLaguerre n x)
      have h' := h.mul_const (opLaguerre n y)
      simpa [hn] using h'
  have hevent : ∀ᶠ τ : ℝ in atTop, Real.exp (-τ) ≤ 1/2 :=
    (hr.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/2))).mono
      (fun τ h => h)
  have hbound : ∀ᶠ τ : ℝ in atTop, ∀ n : ℕ,
      ‖(Real.exp (-τ)^n/(n+1:ℝ)) * opLaguerre n x * opLaguerre n y‖ ≤
        C^2*ρ^n := by
    filter_upwards [hevent] with τ hτ n
    have hnonneg : 0 ≤ Real.exp (-τ)^n/(n+1:ℝ) := by positivity
    have hden : (1:ℝ) ≤ (n+1:ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hcoef : Real.exp (-τ)^n/(n+1:ℝ) ≤ (1/2:ℝ)^n := by
      have hp : Real.exp (-τ)^n ≤ (1/2:ℝ)^n :=
        pow_le_pow_left₀ (Real.exp_nonneg _) hτ n
      calc
        _ ≤ Real.exp (-τ)^n := by
          have hp0 : 0 ≤ Real.exp (-τ)^n := pow_nonneg (Real.exp_nonneg (-τ)) n
          exact (div_le_iff₀ (by positivity)).2 (by
            nlinarith [mul_nonneg hp0
              (show 0 ≤ (n+1:ℝ)-1 by linarith)])
        _ ≤ (1/2:ℝ)^n := hp
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hnonneg]
    have hproduct : |opLaguerre n x| * |opLaguerre n y| ≤ (C*q^n)^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (hX n)) (abs_nonneg (opLaguerre n y)),
        mul_nonneg (sub_nonneg.mpr (hY n))
          (show 0 ≤ C*q^n by positivity)]
    calc
      Real.exp (-τ)^n/(n+1:ℝ) * |opLaguerre n x| * |opLaguerre n y| ≤
          (1/2:ℝ)^n * (C*q^n)^2 := by
        calc
          _ = (Real.exp (-τ)^n/(n+1:ℝ)) *
              (|opLaguerre n x| * |opLaguerre n y|) := by ring
          _ ≤ (1/2:ℝ)^n *
              (|opLaguerre n x| * |opLaguerre n y|) :=
            mul_le_mul_of_nonneg_right hcoef
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _ ≤ (1/2:ℝ)^n * (C*q^n)^2 :=
            mul_le_mul_of_nonneg_left hproduct (by positivity)
      _ = C^2*ρ^n := by
        change (1/2:ℝ)^n*(C*q^n)^2 = C^2*((1/2:ℝ)*q^2)^n
        have hpow : (q^n)^2 = (q^2)^n := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        rw [mul_pow (1/2:ℝ) (q^2) n, mul_pow C (q^n) 2, hpow]
        ring
  have hmain := tendsto_tsum_of_dominated_convergence hsum hlim hbound
  simpa only [tsum_ite_eq, op_laguerre_zero, Nat.cast_one, zero_add] using hmain

end
end Sigma
