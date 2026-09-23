import SigmaProbCausalConvolution
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The causal Green-kernel clause of final:P5, expressed by its action on
smooth compactly supported test functions on the whole real line. -/

namespace Sigma
noncomputable section
open Filter
open MeasureTheory
open scoped ContDiff Topology
set_option maxHeartbeats 800000

def p5TestFunction : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f}
  zero_mem' := by
    refine ⟨contDiff_const, HasCompactSupport.of_support_subset_isCompact isCompact_empty ?_⟩
    simp
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, HasCompactSupport.add hf.2 hg.2⟩
  smul_mem' := by
    intro c f hf
    refine ⟨?_, ?_⟩
    · simpa using hf.1.const_smul c
    · change HasCompactSupport ((fun _ : ℝ => c) * f)
      exact HasCompactSupport.mul_left hf.2

abbrev P5TestFunction := ↥p5TestFunction

def p5TestDeriv : P5TestFunction →ₗ[ℝ] P5TestFunction where
  toFun f := ⟨deriv (f : ℝ → ℝ), by
      exact (contDiff_infty_iff_deriv (𝕜 := ℝ) (f₂ := (f : ℝ → ℝ))).mp f.property.1 |>.2,
    f.property.2.deriv⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact deriv_add
      ((contDiff_infty_iff_deriv.mp f.property.1).1.differentiableAt)
      ((contDiff_infty_iff_deriv.mp g.property.1).1.differentiableAt)
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change deriv (fun y : ℝ => c * (f : ℝ → ℝ) y) x = c * deriv (f : ℝ → ℝ) x
    exact deriv_const_mul_field c

def p5TestAdjointOperator (f : P5TestFunction) : P5TestFunction :=
  p5TestDeriv (p5TestDeriv f) - 2 • p5TestDeriv f + f

def p5DistributionDerivative (T : P5TestFunction →ₗ[ℝ] ℝ) :
    P5TestFunction →ₗ[ℝ] ℝ := -(T.comp p5TestDeriv)

def p5DistributionShift (T : P5TestFunction →ₗ[ℝ] ℝ) :
    P5TestFunction →ₗ[ℝ] ℝ := p5DistributionDerivative T + T

def p5DistributionGreenOperator (T : P5TestFunction →ₗ[ℝ] ℝ) :
    P5TestFunction →ₗ[ℝ] ℝ := p5DistributionShift (p5DistributionShift T)

theorem p5DistributionGreenOperator_apply (T : P5TestFunction →ₗ[ℝ] ℝ)
    (f : P5TestFunction) :
    p5DistributionGreenOperator T f = T (p5TestAdjointOperator f) := by
  simp [p5DistributionGreenOperator, p5DistributionShift, p5DistributionDerivative,
    p5TestAdjointOperator, p5TestDeriv, map_sub]
  ring

@[simp] theorem p5TestDeriv_apply (f : P5TestFunction) (x : ℝ) :
    (p5TestDeriv f : ℝ → ℝ) x = deriv (f : ℝ → ℝ) x := rfl

theorem p5TestAdjointOperator_apply (f : P5TestFunction) (x : ℝ) :
    (p5TestAdjointOperator f : ℝ → ℝ) x =
      deriv (deriv (f : ℝ → ℝ)) x - 2 * deriv (f : ℝ → ℝ) x + (f : ℝ → ℝ) x := by
  simp [p5TestAdjointOperator, p5TestDeriv, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]

def p5DiracFunctional : P5TestFunction →ₗ[ℝ] ℝ where
  toFun f := (f : ℝ → ℝ) 0
  map_add' f g := by change (f : ℝ → ℝ) 0 + (g : ℝ → ℝ) 0 = _; rfl
  map_smul' c f := by change c * (f : ℝ → ℝ) 0 = _; rfl

def p5NegativeTest (f : P5TestFunction) : Prop :=
  ∃ a : ℝ, a < 0 ∧ ∀ x, a ≤ x → (f : ℝ → ℝ) x = 0

theorem continuous_causalGammaGreen : Continuous causalGammaGreen := by
  have he : causalGammaGreen = fun t : ℝ => max t 0 * Real.exp (-(max t 0)) := by
    funext t
    by_cases ht : 0 ≤ t
    · simp [causalGammaGreen, ht]
    · have ht' : t < 0 := lt_of_not_ge ht
      simp [causalGammaGreen, ht, max_eq_right (le_of_lt ht')]
  rw [he]
  fun_prop

@[ext]
structure P5CausalDistribution where
  apply : P5TestFunction →ₗ[ℝ] ℝ
  causal : ∀ f, p5NegativeTest f → apply f = 0

def p5CausalGreen : P5CausalDistribution where
  apply := {
    toFun := fun f => ∫ t : ℝ, causalGammaGreen t * (f : ℝ → ℝ) t
    map_add' := by
      intro f g
      have hf : Integrable (fun t : ℝ => causalGammaGreen t * (f : ℝ → ℝ) t) := by
        apply (continuous_causalGammaGreen.mul f.property.1.continuous).integrable_of_hasCompactSupport
        exact HasCompactSupport.mul_left f.property.2
      have hg : Integrable (fun t : ℝ => causalGammaGreen t * (g : ℝ → ℝ) t) := by
        apply (continuous_causalGammaGreen.mul g.property.1.continuous).integrable_of_hasCompactSupport
        exact HasCompactSupport.mul_left g.property.2
      change (∫ t : ℝ, causalGammaGreen t * ((f : ℝ → ℝ) t + (g : ℝ → ℝ) t)) =
        (∫ t : ℝ, causalGammaGreen t * (f : ℝ → ℝ) t) +
          ∫ t : ℝ, causalGammaGreen t * (g : ℝ → ℝ) t
      rw [← integral_add hf hg]
      congr 1
      funext t
      ring
    map_smul' := by
      intro c f
      have hf : Integrable (fun t : ℝ => causalGammaGreen t * (f : ℝ → ℝ) t) := by
        apply (continuous_causalGammaGreen.mul f.property.1.continuous).integrable_of_hasCompactSupport
        exact HasCompactSupport.mul_left f.property.2
      change (∫ t : ℝ, causalGammaGreen t * (c * (f : ℝ → ℝ) t)) = _
      calc
        _ = ∫ t : ℝ, c * (causalGammaGreen t * (f : ℝ → ℝ) t) := by
          congr 1
          funext t
          ring
        _ = c * ∫ t : ℝ, causalGammaGreen t * (f : ℝ → ℝ) t := integral_mul_left c _
  }
  causal := by
    intro f hf
    obtain ⟨a, ha, hzero⟩ := hf
    change (∫ t : ℝ, causalGammaGreen t * (f : ℝ → ℝ) t) = 0
    have hzero' : ∀ t, causalGammaGreen t * (f : ℝ → ℝ) t = 0 := by
      intro t
      by_cases ht0 : 0 ≤ t
      · have hat : a ≤ t := le_trans ha.le ht0
        simp [causalGammaGreen, ht0, hzero t hat]
      · simp [causalGammaGreen, ht0]
    rw [show (fun t : ℝ => causalGammaGreen t * (f : ℝ → ℝ) t) = 0 by
      funext t; exact hzero' t]
    simp

theorem causalGammaGreen_norm_le_one (t : ℝ) : ‖causalGammaGreen t‖ ≤ 1 := by
  by_cases ht : 0 ≤ t
  · rw [causalGammaGreen, if_pos ht, Real.norm_of_nonneg (mul_nonneg ht (Real.exp_nonneg _))]
    have hlin : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    calc
      t * Real.exp (-t) ≤ Real.exp t * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right hlin (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  · rw [causalGammaGreen, if_neg ht, norm_zero]
    norm_num

theorem p5CausalGreen_integral_bound (f : P5TestFunction) :
    ‖p5CausalGreen.apply f‖ ≤ ∫ t : ℝ, ‖(f : ℝ → ℝ) t‖ := by
  change ‖∫ t : ℝ, causalGammaGreen t * (f : ℝ → ℝ) t‖ ≤ _
  have hp : Integrable (fun t : ℝ => causalGammaGreen t * (f : ℝ → ℝ) t) := by
    apply (continuous_causalGammaGreen.mul f.property.1.continuous).integrable_of_hasCompactSupport
    exact HasCompactSupport.mul_left f.property.2
  have hf : Integrable (fun t : ℝ => ‖(f : ℝ → ℝ) t‖) := by
    apply f.property.1.continuous.norm.integrable_of_hasCompactSupport
    exact f.property.2.norm
  calc
    _ ≤ ∫ t : ℝ, ‖causalGammaGreen t * (f : ℝ → ℝ) t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ‖(f : ℝ → ℝ) t‖ := by
      apply integral_mono hp.norm hf
      intro t
      change ‖causalGammaGreen t * (f : ℝ → ℝ) t‖ ≤ ‖(f : ℝ → ℝ) t‖
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (causalGammaGreen_norm_le_one t)

@[ext]
structure P5RegularDistribution where
  functional : P5CausalDistribution
  l1_continuous : ∀ f : P5TestFunction,
    ‖functional.apply f‖ ≤ ∫ t : ℝ, ‖(f : ℝ → ℝ) t‖

def p5CausalGreenDistribution : P5RegularDistribution :=
  ⟨p5CausalGreen, p5CausalGreen_integral_bound⟩

def p5GreenFlux (f : P5TestFunction) : ℝ → ℝ := fun t =>
  t * Real.exp (-t) * deriv (f : ℝ → ℝ) t - (1+t) * Real.exp (-t) * (f : ℝ → ℝ) t

theorem p5GreenFlux_deriv (f : P5TestFunction) (t : ℝ) :
    deriv (p5GreenFlux f) t =
      t * Real.exp (-t) *
        (deriv (deriv (f : ℝ → ℝ)) t - 2 * deriv (f : ℝ → ℝ) t + (f : ℝ → ℝ) t) := by
  have hf : DifferentiableAt ℝ (f : ℝ → ℝ) t :=
    (contDiff_infty_iff_deriv.mp f.property.1).1.differentiableAt
  have hdf : DifferentiableAt ℝ (deriv (f : ℝ → ℝ)) t := by
    exact (((contDiff_infty_iff_deriv.mp f.property.1).2).differentiable (by simp)).differentiableAt
  have hneg : HasDerivAt (fun x : ℝ => -x) (-1) t := by
    simpa using (hasDerivAt_id t).neg
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-t)) t := by
    simpa using (Real.hasDerivAt_exp (-t)).comp t hneg
  have hsum : HasDerivAt (fun x : ℝ => 1+x) 1 t := by
    simpa using (hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)
  have h1 := ((hasDerivAt_id t).mul hexp).mul hdf.hasDerivAt
  have h2 := (hsum.mul hexp).mul hf.hasDerivAt
  change deriv ((fun x : ℝ => x * Real.exp (-x) * deriv (f : ℝ → ℝ) x) -
    (fun x : ℝ => (1+x) * Real.exp (-x) * (f : ℝ → ℝ) x)) t = _
  convert (h1.sub h2).deriv using 1
  simp only [id_eq]
  ring

theorem p5_causal_green_pairing_eq_dirac :
    ∀ f : P5TestFunction,
      p5CausalGreen.apply (p5TestAdjointOperator f) = p5DiracFunctional f := by
  intro f
  change (∫ t : ℝ, causalGammaGreen t * (p5TestAdjointOperator f : ℝ → ℝ) t) =
    (f : ℝ → ℝ) 0
  have hflux : ContDiff ℝ 1 (p5GreenFlux f) := by
    have hf := f.property.1
    have hdf : ContDiff ℝ ∞ (deriv (f : ℝ → ℝ)) :=
      (contDiff_infty_iff_deriv.mp hf).2
    have hexp : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (-t)) := by fun_prop
    have hterms : ContDiff ℝ ∞ (fun t : ℝ =>
        t * Real.exp (-t) * deriv (f : ℝ → ℝ) t -
          (1+t) * Real.exp (-t) * (f : ℝ → ℝ) t) := by
      exact ((contDiff_id.mul hexp).mul hdf).sub
        (((contDiff_const.add contDiff_id).mul hexp).mul hf)
    exact hterms.of_le (by simp)
  have hcompact : HasCompactSupport (p5GreenFlux f) := by
    have hdf := f.property.2.deriv
    have hleft : HasCompactSupport (fun t : ℝ => t * Real.exp (-t) * deriv (f : ℝ → ℝ) t) := by
      exact HasCompactSupport.mul_left hdf
    have hright : HasCompactSupport (fun t : ℝ =>
        (1+t) * Real.exp (-t) * (f : ℝ → ℝ) t) := by
      exact HasCompactSupport.mul_left f.property.2
    have hneg : HasCompactSupport (fun t : ℝ =>
        -((1+t) * Real.exp (-t) * (f : ℝ → ℝ) t)) := by
      rw [hasCompactSupport_iff_eventuallyEq] at hright ⊢
      filter_upwards [hright] with t ht
      simp [ht]
    have hsum : HasCompactSupport (fun t : ℝ =>
        t * Real.exp (-t) * deriv (f : ℝ → ℝ) t +
          -((1+t) * Real.exp (-t) * (f : ℝ → ℝ) t)) := hleft.add hneg
    simpa [p5GreenFlux, sub_eq_add_neg] using hsum
  have hpoint (t : ℝ) :
      causalGammaGreen t * (p5TestAdjointOperator f : ℝ → ℝ) t =
        Set.indicator (Set.Ioi 0) (deriv (p5GreenFlux f)) t := by
    by_cases ht : 0 < t
    · rw [causalGammaGreen, if_pos (le_of_lt ht)]
      rw [p5TestAdjointOperator_apply, ← p5GreenFlux_deriv]
      simp [Set.indicator, ht]
    · have ht' : t ≤ 0 := le_of_not_gt ht
      by_cases htz : t = 0
      · subst t
        simp [causalGammaGreen]
      · have htn : t < 0 := lt_of_le_of_ne ht' htz
        simp [causalGammaGreen, htn, Set.indicator, not_lt.mpr (le_of_lt htn)]
  have hfun : (fun t : ℝ => causalGammaGreen t * (p5TestAdjointOperator f : ℝ → ℝ) t) =
      Set.indicator (Set.Ioi 0) (deriv (p5GreenFlux f)) := by
    funext t
    exact hpoint t
  rw [hfun, integral_indicator measurableSet_Ioi]
  simpa [p5GreenFlux, p5TestAdjointOperator_apply] using
    (hcompact.integral_Ioi_deriv_eq hflux 0)

theorem p5_causal_green_distributional_equation :
    p5DistributionGreenOperator p5CausalGreen.apply = p5DiracFunctional := by
  ext f
  rw [p5DistributionGreenOperator_apply]
  exact p5_causal_green_pairing_eq_dirac f

theorem p5_test_zero_eventually_atTop (f : P5TestFunction) :
    ∃ b : ℝ, ∀ x, b ≤ x → (f : ℝ → ℝ) x = 0 := by
  have hs := f.property.2
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at hs
  have ht := hs.filter_mono atTop_le_cocompact
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.1 ht
  exact ⟨b, fun x hx => by simpa using hb x hx⟩

def p5Primitive (q : ℝ → ℝ) (b : ℝ) : ℝ → ℝ :=
  fun t => ∫ x : ℝ in b..t, q x

theorem p5Primitive_hasDerivAt (q : ℝ → ℝ) (hq : Continuous q) (b t : ℝ) :
    HasDerivAt (p5Primitive q b) (q t) t := by
  exact (hq.integral_hasStrictDerivAt b t).hasDerivAt

theorem p5Primitive_contDiff (q : ℝ → ℝ) (hq : ContDiff ℝ ∞ q) (b : ℝ) :
    ContDiff ℝ ∞ (p5Primitive q b) := by
  have hderiv : deriv (p5Primitive q b) = q := by
    funext t
    exact (p5Primitive_hasDerivAt q hq.continuous b t).deriv
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨?_, ?_⟩
  · intro t
    exact (p5Primitive_hasDerivAt q hq.continuous b t).differentiableAt
  · simpa only [hderiv] using hq

def p5GreenQ0 (f : P5TestFunction) : ℝ → ℝ :=
  fun t => Real.exp (-t) * (f : ℝ → ℝ) t

def p5GreenQ1 (f : P5TestFunction) : ℝ → ℝ :=
  fun t => t * Real.exp (-t) * (f : ℝ → ℝ) t

theorem p5GreenQ0_contDiff (f : P5TestFunction) : ContDiff ℝ ∞ (p5GreenQ0 f) := by
  have hf := f.property.1
  have he : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (-t)) := by fun_prop
  exact he.mul hf

theorem p5GreenQ1_contDiff (f : P5TestFunction) : ContDiff ℝ ∞ (p5GreenQ1 f) := by
  have hf := f.property.1
  have he : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (-t)) := by fun_prop
  exact (contDiff_id.mul he).mul hf

def p5GreenAdjointIntegral (f : P5TestFunction) (b : ℝ) : ℝ → ℝ := fun t =>
  -p5Primitive (p5GreenQ1 f) b t + t * p5Primitive (p5GreenQ0 f) b t

def p5GreenAdjointCore (f : P5TestFunction) (b : ℝ) : ℝ → ℝ := fun t =>
  Real.exp t * p5GreenAdjointIntegral f b t

theorem p5GreenAdjointIntegral_contDiff (f : P5TestFunction) (b : ℝ) :
    ContDiff ℝ ∞ (p5GreenAdjointIntegral f b) := by
  have h0 := p5Primitive_contDiff (p5GreenQ0 f) (p5GreenQ0_contDiff f) b
  have h1 := p5Primitive_contDiff (p5GreenQ1 f) (p5GreenQ1_contDiff f) b
  exact h1.neg.add (contDiff_id.mul h0)

theorem p5GreenAdjointCore_contDiff (f : P5TestFunction) (b : ℝ) :
    ContDiff ℝ ∞ (p5GreenAdjointCore f b) := by
  have hi := p5GreenAdjointIntegral_contDiff f b
  have he : ContDiff ℝ ∞ (fun t : ℝ => Real.exp t) := by fun_prop
  exact he.mul hi

theorem p5GreenAdjointCore_solves (f : P5TestFunction) (b t : ℝ) :
    deriv (deriv (p5GreenAdjointCore f b)) t -
      2 * deriv (p5GreenAdjointCore f b) t + p5GreenAdjointCore f b t =
        (f : ℝ → ℝ) t := by
  let p0 := p5Primitive (p5GreenQ0 f) b
  let p1 := p5Primitive (p5GreenQ1 f) b
  let I := fun x : ℝ => -p1 x + x * p0 x
  have hp0 := p5Primitive_hasDerivAt (p5GreenQ0 f) (p5GreenQ0_contDiff f).continuous b t
  have hp1 := p5Primitive_hasDerivAt (p5GreenQ1 f) (p5GreenQ1_contDiff f).continuous b t
  have hI : HasDerivAt I (p0 t) t := by
    convert (hp1.neg).add ((hasDerivAt_id t).mul hp0) using 1
    simp [I, p0, p1, p5GreenQ0, p5GreenQ1]
    ring
  have hI0 : HasDerivAt (fun x : ℝ => I x + p0 x)
      (p0 t + p5GreenQ0 f t) t := hI.add hp0
  have hexp : HasDerivAt (fun x : ℝ => Real.exp x) (Real.exp t) t :=
    Real.hasDerivAt_exp t
  have hcore1 : HasDerivAt (p5GreenAdjointCore f b)
      (Real.exp t * (I t + p0 t)) t := by
    convert hexp.mul hI using 1
    simp [p5GreenAdjointCore, p5GreenAdjointIntegral, I, p0, p1]
    ring
  have hcore2 : HasDerivAt (fun x : ℝ => Real.exp x * (I x + p0 x))
      (Real.exp t * (I t + p0 t) + Real.exp t * (p0 t + p5GreenQ0 f t)) t :=
    hexp.mul hI0
  have hfirst : deriv (p5GreenAdjointCore f b) t = Real.exp t * (I t + p0 t) :=
    hcore1.deriv
  have hfirstFun : deriv (p5GreenAdjointCore f b) =
      fun x : ℝ => Real.exp x * (I x + p0 x) := by
    funext x
    have hp0x := p5Primitive_hasDerivAt (p5GreenQ0 f)
      (p5GreenQ0_contDiff f).continuous b x
    have hp1x := p5Primitive_hasDerivAt (p5GreenQ1 f)
      (p5GreenQ1_contDiff f).continuous b x
    have hIx : HasDerivAt I (p0 x) x := by
      convert (hp1x.neg).add ((hasDerivAt_id x).mul hp0x) using 1
      simp [I, p0, p1, p5GreenQ0, p5GreenQ1]
      ring
    have hcx := (Real.hasDerivAt_exp x).mul hIx
    have hc : HasDerivAt (p5GreenAdjointCore f b)
        (Real.exp x * (I x + p0 x)) x := by
      convert hcx using 1
      simp [p5GreenAdjointCore, p5GreenAdjointIntegral, I, p0, p1]
      ring
    exact hc.deriv
  have hsecond : deriv (deriv (p5GreenAdjointCore f b)) t =
      Real.exp t * (I t + p0 t) + Real.exp t * (p0 t + p5GreenQ0 f t) := by
    rw [hfirstFun]
    exact hcore2.deriv
  rw [hfirst, hsecond]
  dsimp [p5GreenAdjointCore, p5GreenAdjointIntegral, p5GreenQ0, I, p0, p1]
  have hexp_cancel : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hcancel_f : Real.exp t * (Real.exp (-t) * (f : ℝ → ℝ) t) =
      (f : ℝ → ℝ) t := by
    rw [← mul_assoc, hexp_cancel, one_mul]
  simp only [mul_add]
  rw [hcancel_f]
  ring

def p5GreenAdjointCutoff (t : ℝ) : ℝ := Real.smoothTransition (t + 4)

def p5GreenAdjointTestFunction (f : P5TestFunction) (b : ℝ) : ℝ → ℝ :=
  fun t => p5GreenAdjointCutoff t * p5GreenAdjointCore f b t

theorem p5GreenAdjointTest_solves (f : P5TestFunction) (b t : ℝ) (ht : -2 ≤ t) :
    deriv (deriv (p5GreenAdjointTestFunction f b)) t -
      2 * deriv (p5GreenAdjointTestFunction f b) t +
        p5GreenAdjointTestFunction f b t = (f : ℝ → ℝ) t := by
  have hlocal : p5GreenAdjointTestFunction f b =ᶠ[𝓝 t] p5GreenAdjointCore f b := by
    filter_upwards [Ioo_mem_nhds (by linarith : t-1 < t) (by linarith : t < t+1)] with x hx
    have hcut : 1 ≤ x+4 := by linarith [hx.1]
    simp [p5GreenAdjointTestFunction, p5GreenAdjointCutoff,
      Real.smoothTransition.one_of_one_le hcut]
  have hlocal' := hlocal.deriv
  have hlocal'' := hlocal.deriv.deriv_eq
  have hlocal_d := hlocal.deriv_eq
  rw [hlocal'', hlocal_d, hlocal.eq_of_nhds]
  exact p5GreenAdjointCore_solves f b t

theorem p5Primitive_eq_zero_of_tailzero (q : ℝ → ℝ) (b t : ℝ)
    (hq : ∀ x, b ≤ x → q x = 0) (hbt : b ≤ t) :
    p5Primitive q b t = 0 := by
  rw [p5Primitive, intervalIntegral.integral_of_le hbt]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  exact hq x hx.1.le

theorem p5GreenAdjointCore_eq_zero_of_tailzero (f : P5TestFunction) (b t : ℝ)
    (hbt : b ≤ t) (hf : ∀ x, b ≤ x → (f : ℝ → ℝ) x = 0) :
    p5GreenAdjointCore f b t = 0 := by
  have hq0 : ∀ x, b ≤ x → p5GreenQ0 f x = 0 := by
    intro x hx
    simp [p5GreenQ0, hf x hx]
  have hq1 : ∀ x, b ≤ x → p5GreenQ1 f x = 0 := by
    intro x hx
    simp [p5GreenQ1, hf x hx]
  rw [p5GreenAdjointCore, p5GreenAdjointIntegral,
    p5Primitive_eq_zero_of_tailzero _ _ _ hq1 hbt,
    p5Primitive_eq_zero_of_tailzero _ _ _ hq0 hbt]
  simp

noncomputable def p5GreenAdjointTest (f : P5TestFunction) (b : ℝ)
    (hf : ∀ x, b ≤ x → (f : ℝ → ℝ) x = 0) : P5TestFunction := by
  let B := max b (-3)
  have hcut : ContDiff ℝ ∞ p5GreenAdjointCutoff := by
    have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
    exact hs.comp (contDiff_id.add contDiff_const)
  have hcore := p5GreenAdjointCore_contDiff f B
  have hfun : ContDiff ℝ ∞ (p5GreenAdjointTestFunction f B) := by
    exact hcut.mul hcore
  have hleft (x : ℝ) (hx : x < -4) : p5GreenAdjointTestFunction f B x = 0 := by
    have hx' : x+4 ≤ 0 := by linarith
    simp [p5GreenAdjointTestFunction, p5GreenAdjointCutoff,
      Real.smoothTransition.zero_of_nonpos hx']
  have hright (x : ℝ) (hx : B < x) : p5GreenAdjointTestFunction f B x = 0 := by
    have hBzero := p5GreenAdjointCore_eq_zero_of_tailzero f B x hx.le
      (fun y hy => hf y (le_trans (le_max_left b (-3)) hy))
    simp [p5GreenAdjointTestFunction, hBzero]
  have hcomp : HasCompactSupport (p5GreenAdjointTestFunction f B) := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro x hx
    simp only [Function.mem_support] at hx
    by_contra hxI
    have hn := not_and_or.mp hxI
    rcases hn with hleft' | hright'
    · have hx' : x < -4 := lt_of_not_ge hleft'
      exact hx (hleft x hx')
    · have hx' : B < x := lt_of_not_ge hright'
      exact hx (hright x hx')
  refine ⟨p5GreenAdjointTestFunction f B, hfun, hcomp⟩

theorem p5GreenAdjointTestFunction_eq_one_region (f : P5TestFunction) (b t : ℝ)
    (ht : -2 ≤ t) (hf : ∀ x, b ≤ x → (f : ℝ → ℝ) x = 0) :
    deriv (deriv (p5GreenAdjointTest f b hf : ℝ → ℝ)) t -
      2 * deriv (p5GreenAdjointTest f b hf : ℝ → ℝ) t +
        (p5GreenAdjointTest f b hf : ℝ → ℝ) t = (f : ℝ → ℝ) t := by
  let B := max b (-3)
  change deriv (deriv (p5GreenAdjointTestFunction f B)) t -
      2 * deriv (p5GreenAdjointTestFunction f B) t +
        p5GreenAdjointTestFunction f B t = (f : ℝ → ℝ) t
  have hlocal : p5GreenAdjointTestFunction f B =ᶠ[𝓝 t] p5GreenAdjointCore f B := by
    filter_upwards [Ioo_mem_nhds (by linarith : t-1 < t) (by linarith : t < t+1)] with x hx
    have hcut : 1 ≤ x+4 := by linarith [hx.1]
    simp [p5GreenAdjointTestFunction, p5GreenAdjointCutoff,
      Real.smoothTransition.one_of_one_le hcut]
  have hlocal' := hlocal.deriv
  have hlocal'' := hlocal.deriv.deriv_eq
  have hlocal_d := hlocal.deriv_eq
  rw [hlocal'', hlocal_d, hlocal.eq_of_nhds]
  exact p5GreenAdjointCore_solves f B t

theorem p5_causal_homogeneous_functional_zero
    (T : P5TestFunction →ₗ[ℝ] ℝ)
    (hcausal : ∀ f, p5NegativeTest f → T f = 0)
    (hode : ∀ f, T (p5TestAdjointOperator f) = 0) : T = 0 := by
  apply LinearMap.ext
  intro f
  obtain ⟨b, hb⟩ := p5_test_zero_eventually_atTop f
  let ψ := p5GreenAdjointTest f b hb
  let r : P5TestFunction := f - p5TestAdjointOperator ψ
  have hr : p5NegativeTest r := by
    refine ⟨-2, by norm_num, ?_⟩
    intro x hx
    change (f : ℝ → ℝ) x - (p5TestAdjointOperator ψ : ℝ → ℝ) x = 0
    rw [p5TestAdjointOperator_apply,
      p5GreenAdjointTestFunction_eq_one_region f b x hx hb]
    ring
  have hdecomp : f = p5TestAdjointOperator ψ + r := by
    apply Subtype.ext
    funext x
    change (f : ℝ → ℝ) x = (p5TestAdjointOperator ψ : ℝ → ℝ) x +
      ((f : ℝ → ℝ) x - (p5TestAdjointOperator ψ : ℝ → ℝ) x)
    ring
  rw [hdecomp, map_add, hode ψ, hcausal r hr]
  simp

theorem p5_causal_distribution_green_unique (T : P5CausalDistribution)
    (hpde : ∀ f : P5TestFunction,
      T.apply (p5TestAdjointOperator f) = p5DiracFunctional f) :
    T.apply = p5CausalGreen.apply := by
  let D : P5TestFunction →ₗ[ℝ] ℝ := T.apply - p5CausalGreen.apply
  have hcausal : ∀ f, p5NegativeTest f → D f = 0 := by
    intro f hf
    simp [D, T.causal f hf, p5CausalGreen.causal f hf]
  have hode : ∀ f, D (p5TestAdjointOperator f) = 0 := by
    intro f
    simp [D, hpde f, p5_causal_green_pairing_eq_dirac f]
  have hD := p5_causal_homogeneous_functional_zero D hcausal hode
  ext f
  have hf := congrArg (fun F : P5TestFunction →ₗ[ℝ] ℝ => F f) hD
  change T.apply f = p5CausalGreen.apply f
  exact sub_eq_zero.mp (by simpa [D] using hf)

theorem p5_causal_distribution_green_exists_unique :
    ∃! T : P5CausalDistribution, ∀ f : P5TestFunction,
      T.apply (p5TestAdjointOperator f) = p5DiracFunctional f := by
  refine ⟨p5CausalGreen, p5_causal_green_pairing_eq_dirac, ?_⟩
  intro T hT
  apply P5CausalDistribution.ext
  exact p5_causal_distribution_green_unique T hT

theorem causalGammaGreen_eq_indicator (t : ℝ) :
    causalGammaGreen t = Set.indicator (Set.Ici 0)
      (fun x : ℝ => x * Real.exp (-x)) t := by
  by_cases ht : 0 ≤ t
  · simp [causalGammaGreen, ht]
  · simp [causalGammaGreen, ht]

theorem p5_causal_regular_distribution_green_exists_unique :
    ∃! T : P5RegularDistribution,
      p5DistributionGreenOperator T.functional.apply = p5DiracFunctional := by
  refine ⟨p5CausalGreenDistribution, ?_, ?_⟩
  · ext f
    rw [p5DistributionGreenOperator_apply]
    exact p5_causal_green_pairing_eq_dirac f
  · intro T hT
    apply P5RegularDistribution.ext
    change T.functional = p5CausalGreen
    apply P5CausalDistribution.ext
    apply p5_causal_distribution_green_unique T.functional ?_
    intro f
    have h := congrArg (fun F : P5TestFunction →ₗ[ℝ] ℝ => F f) hT
    simpa only [p5DistributionGreenOperator_apply] using h

theorem p5_causal_regular_distribution_green_representation (f : P5TestFunction) :
    p5CausalGreenDistribution.functional.apply f =
      ∫ t : ℝ, Set.indicator (Set.Ici 0) (fun x : ℝ => x * Real.exp (-x)) t *
        (f : ℝ → ℝ) t := by
  simp [p5CausalGreenDistribution, p5CausalGreen, causalGammaGreen_eq_indicator]

end
end Sigma
