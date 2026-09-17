import SigmaProbGammaShift
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal

/-- The strict survival of an arbitrary lifetime law, with no input density. -/
def lifetimeSurvival (μ : Measure ℝ) (t : ℝ) : ℝ := (μ (Ioi t)).toReal

/-- The equilibrium measure with its marked positive mean. -/
def equilibriumMeasure (μ : Measure ℝ) (m : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun t => ENNReal.ofReal (lifetimeSurvival μ t / m))

theorem lifetime_survival_antitone (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Antitone (lifetimeSurvival μ) := by
  intro a b hab
  exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Ioi_subset_Ioi hab))

theorem lifetime_survival_measurable (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Measurable (lifetimeSurvival μ) := (lifetime_survival_antitone μ).measurable

theorem lifetime_survival_eq_one_sub_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (t : ℝ) : lifetimeSurvival μ t = 1 - cdf μ t := by
  rw [lifetimeSurvival, ← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top μ _),
    ENNReal.toReal_sub_of_le (measure_mono (subset_univ _)) (measure_ne_top μ _),
    measure_univ, cdf_eq_toReal]
  simp

theorem lifetime_survival_right_continuous (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (t : ℝ) : ContinuousWithinAt (lifetimeSurvival μ) (Ioi t) t := by
  have he : lifetimeSurvival μ = fun x => 1 - cdf μ x :=
    funext (lifetime_survival_eq_one_sub_cdf μ)
  rw [he]
  exact continuousWithinAt_const.sub (((cdf μ).right_continuous t).mono Ioi_subset_Ici_self)

theorem equilibrium_measure_Ioc (μ : Measure ℝ) [IsFiniteMeasure μ]
    (m x : ℝ) (hm : 0 < m) (hx : 0 ≤ x) :
    (equilibriumMeasure μ m (Ioc 0 x)).toReal =
      ∫ t : ℝ in (0 : ℝ)..x, lifetimeSurvival μ t / m := by
  have hi := (lifetime_survival_antitone μ).intervalIntegrable (μ := volume) (a := 0) (b := x)
  rw [equilibriumMeasure, withDensity_apply _ measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (show Ioc 0 x ⊆ Ioi 0 from fun _ h => h.1),
    ← ofReal_integral_eq_lintegral_ofReal
      ((hi.div_const m).1) (Eventually.of_forall fun t => by
        exact div_nonneg ENNReal.toReal_nonneg hm.le),
    ENNReal.toReal_ofReal, intervalIntegral.integral_of_le hx]
  exact integral_nonneg (fun t => div_nonneg ENNReal.toReal_nonneg hm.le)

/-- Equality of equilibrium measures recovers their canonical right-continuous
densities pointwise, including the right-hand value at zero. -/
theorem equilibrium_equal_survival_ratios (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (m n : ℝ) (hm : 0 < m) (hn : 0 < n)
    (he : equilibriumMeasure μ m = equilibriumMeasure ν n) (x : ℝ) (hx : 0 ≤ x) :
    lifetimeSurvival μ x / m = lifetimeSurvival ν x / n := by
  have hμ := intervalIntegral.integral_hasDerivWithinAt_right
    ((lifetime_survival_antitone μ).intervalIntegrable.div_const m)
    (a := 0) (s := Ici x) (t := Ioi x)
    ((lifetime_survival_measurable μ).div_const m).aestronglyMeasurable.stronglyMeasurableAtFilter
    ((lifetime_survival_right_continuous μ x).div_const m)
  have hν := intervalIntegral.integral_hasDerivWithinAt_right
    ((lifetime_survival_antitone ν).intervalIntegrable.div_const n)
    (a := 0) (s := Ici x) (t := Ioi x)
    ((lifetime_survival_measurable ν).div_const n).aestronglyMeasurable.stronglyMeasurableAtFilter
    ((lifetime_survival_right_continuous ν x).div_const n)
  have hp : ∀ y ∈ Ici x,
      (∫ t : ℝ in (0 : ℝ)..y, lifetimeSurvival μ t / m) =
      ∫ t : ℝ in (0 : ℝ)..y, lifetimeSurvival ν t / n := by
    intro y hy
    rw [← equilibrium_measure_Ioc μ m y hm (hx.trans hy),
      ← equilibrium_measure_Ioc ν n y hn (hx.trans hy), he]
  exact (hμ.derivWithin (uniqueDiffOn_Ici x x (by simp))).symm.trans
    ((hν.congr_of_mem hp (by simp)).derivWithin (uniqueDiffOn_Ici x x (by simp)))

/-- The positive-lifetime inverse in Proposition 3.16: the output law recovers
both the original law and its marked mean, with no candidate density. -/
theorem equilibrium_positive_inverse (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (m n : ℝ) (hm : 0 < m) (hn : 0 < n)
    (hμ : μ (Ioi 0) = 1) (hν : ν (Ioi 0) = 1)
    (he : equilibriumMeasure μ m = equilibriumMeasure ν n) : m = n ∧ μ = ν := by
  have hzero := equilibrium_equal_survival_ratios μ ν m n hm hn he 0 le_rfl
  simp only [lifetimeSurvival, hμ, hν] at hzero
  norm_num at hzero
  have hmn : m = n := hzero
  refine ⟨hmn, Measure.eq_of_cdf μ ν ?_⟩
  ext x
  have hs : lifetimeSurvival μ x = lifetimeSurvival ν x := by
    by_cases hx : 0 ≤ x
    · have hr := equilibrium_equal_survival_ratios μ ν m n hm hn he x hx
      rw [← hmn] at hr
      exact (div_left_inj' hm.ne').mp hr
    · have hx0 : x ≤ 0 := le_of_not_ge hx
      have hμx : μ (Ioi x) = 1 := le_antisymm (prob_le_one) (by
        rw [← hμ]; exact measure_mono (Ioi_subset_Ioi hx0))
      have hνx : ν (Ioi x) = 1 := le_antisymm (prob_le_one) (by
        rw [← hν]; exact measure_mono (Ioi_subset_Ioi hx0))
      simp [lifetimeSurvival, hμx, hνx]
  rw [lifetime_survival_eq_one_sub_cdf μ x, lifetime_survival_eq_one_sub_cdf ν x] at hs
  linarith

theorem lifetime_survival_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (fun t : ℝ => t) μ) (hnonneg : ∀ᵐ t ∂μ, 0 ≤ t) :
    (∫ t : ℝ in Ioi 0, lifetimeSurvival μ t) = ∫ t : ℝ, t ∂μ :=
  hi.integral_eq_integral_meas_lt hnonneg |>.symm

/-- Tail integration normalizes the equilibrium measure for an arbitrary
nonnegative lifetime of finite positive mean. -/
theorem equilibrium_measure_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℝ) (hm : 0 < m) (hnonneg : ∀ᵐ t ∂μ, 0 ≤ t)
    (hmean : (∫ t : ℝ, t ∂μ) = m) : IsProbabilityMeasure (equilibriumMeasure μ m) := by
  have hi : Integrable (fun t : ℝ => t) μ :=
    Integrable.of_integral_ne_zero (by rw [hmean]; exact hm.ne')
  have hs : (∫ t : ℝ in Ioi 0, lifetimeSurvival μ t) = m :=
    (lifetime_survival_integral μ hi hnonneg).trans hmean
  have hsi : IntegrableOn (lifetimeSurvival μ) (Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [hs]; exact hm.ne')
  constructor
  rw [equilibriumMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hsi.div_const m)
      (Eventually.of_forall fun t => div_nonneg ENNReal.toReal_nonneg hm.le),
    integral_div, hs, div_self hm.ne', ENNReal.ofReal_one]

/-- Adding an atom at zero rescales the survival and mean equally, so the
equilibrium output loses the atom mass. -/
theorem equilibrium_atom_zero_invariance (μ : Measure ℝ) [IsFiniteMeasure μ]
    (m r : ℝ) (hr1 : r < 1) :
    equilibriumMeasure
      (ENNReal.ofReal r • Measure.dirac 0 + ENNReal.ofReal (1-r) • μ) ((1-r)*m) =
      equilibriumMeasure μ m := by
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hs : lifetimeSurvival
      (ENNReal.ofReal r • Measure.dirac 0 + ENNReal.ofReal (1-r) • μ) t =
      (1-r) * lifetimeSurvival μ t := by
    simp [lifetimeSurvival, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply' _ measurableSet_Ioi, not_lt.mpr ht.le,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (show 0 ≤ 1-r by linarith)]
  rw [hs, mul_div_mul_left _ _ (show 1-r ≠ 0 by linarith)]

theorem lifetime_atom_zero_mixture_mean (μ : Measure ℝ)
    (hi : Integrable (fun t : ℝ => t) μ) (r : ℝ) (hr1 : r ≤ 1) :
    (∫ t : ℝ, t ∂(ENNReal.ofReal r • Measure.dirac 0 + ENNReal.ofReal (1-r) • μ)) =
      (1-r) * ∫ t : ℝ, t ∂μ := by
  rw [integral_add_measure
    (((integrable_const (0 : ℝ)).congr (ae_eq_dirac (fun t : ℝ => t)).symm).smul_measure
      ENNReal.ofReal_ne_top) (hi.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure]
  simp [ENNReal.toReal_ofReal (show 0 ≤ 1-r by linarith), smul_eq_mul]

/-- A normalized family of distinct nonnegative lifetimes with the same
equilibrium law and their actual, rescaled means. -/
theorem equilibrium_atom_zero_counterexample (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnonneg : ∀ᵐ t ∂μ, 0 ≤ t) (hzero : μ {0} = 0)
    (hm : 0 < ∫ t : ℝ, t ∂μ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    let ν := ENNReal.ofReal r • Measure.dirac 0 + ENNReal.ofReal (1-r) • μ
    IsProbabilityMeasure ν ∧ (∀ᵐ t ∂ν, 0 ≤ t) ∧ ν ≠ μ ∧
      (∫ t : ℝ, t ∂ν) = (1-r) * (∫ t : ℝ, t ∂μ) ∧
      IsProbabilityMeasure (equilibriumMeasure ν (∫ t : ℝ, t ∂ν)) ∧
      equilibriumMeasure ν (∫ t : ℝ, t ∂ν) =
        equilibriumMeasure μ (∫ t : ℝ, t ∂μ) := by
  let ν := ENNReal.ofReal r • Measure.dirac 0 + ENNReal.ofReal (1-r) • μ
  have hprob : IsProbabilityMeasure ν := by
    constructor
    have hs : ENNReal.ofReal r + ENNReal.ofReal (1-r) = 1 := by
      rw [← ENNReal.ofReal_add hr0.le (by linarith)]
      norm_num
    simpa [ν] using hs
  letI := hprob
  have hν : ∀ᵐ t ∂ν, 0 ≤ t := by
    rw [ae_iff] at hnonneg ⊢
    simp only [not_le] at hnonneg
    simp [ν, Measure.add_apply, Measure.smul_apply, hnonneg]
  have hneq : ν ≠ μ := by
    intro he
    have hatom : ν {0} = ENNReal.ofReal r := by simp [ν, hzero]
    rw [he, hzero] at hatom
    exact (ENNReal.ofReal_pos.mpr hr0).ne' hatom.symm
  have hmean := lifetime_atom_zero_mixture_mean μ
    (Integrable.of_integral_ne_zero hm.ne') r hr1.le
  have hpos : 0 < ∫ t : ℝ, t ∂ν := by
    rw [hmean]
    exact mul_pos (by linarith) hm
  refine ⟨hprob, hν, hneq, hmean, equilibrium_measure_probability ν _ hpos hν rfl, ?_⟩
  rw [hmean]
  exact equilibrium_atom_zero_invariance μ _ r hr1

/-- Fixed-point equality gives an integral equation before any regularity is
assumed or deduced for the candidate lifetime. -/
theorem equilibrium_fixed_integral_equation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℝ) (hm : 0 < m) (hpos : μ (Ioi 0) = 1)
    (hfix : μ = equilibriumMeasure μ m) (x : ℝ) (hx : 0 ≤ x) :
    lifetimeSurvival μ x = 1 - ∫ t : ℝ in (0 : ℝ)..x, lifetimeSurvival μ t / m := by
  have hsum : μ (Ioc 0 x) + μ (Ioi x) = 1 := by
    rw [← measure_union (by exact Set.disjoint_left.mpr (fun t ht ht' => not_lt_of_ge ht.2 ht'))
      measurableSet_Ioi, Ioc_union_Ioi_eq_Ioi hx, hpos]
  have hr := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hr
  norm_num at hr
  have he : (μ (Ioc 0 x)).toReal = ∫ t : ℝ in (0 : ℝ)..x, lifetimeSurvival μ t / m := by
    calc
      _ = (equilibriumMeasure μ m (Ioc 0 x)).toReal := congrArg (fun ν : Measure ℝ => (ν (Ioc 0 x)).toReal) hfix
      _ = _ := equilibrium_measure_Ioc μ m x hm hx
  dsimp [lifetimeSurvival] at he ⊢
  rw [he] at hr
  linarith

theorem equilibrium_fixed_survival_continuous (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℝ) (hm : 0 < m) (hpos : μ (Ioi 0) = 1)
    (hfix : μ = equilibriumMeasure μ m) :
    ContinuousOn (lifetimeSurvival μ) (Ici 0) := by
  have hc : Continuous (fun x : ℝ => 1 - ∫ t : ℝ in (0 : ℝ)..x, lifetimeSurvival μ t / m) :=
    continuous_const.sub (intervalIntegral.continuous_primitive
      (fun a b => (lifetime_survival_antitone μ).intervalIntegrable.div_const m) 0)
  exact hc.continuousOn.congr (fun x hx =>
    equilibrium_fixed_integral_equation μ m hm hpos hfix x hx)

theorem equilibrium_fixed_survival_derivative (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℝ) (hm : 0 < m) (hpos : μ (Ioi 0) = 1)
    (hfix : μ = equilibriumMeasure μ m) (x : ℝ) (hx : 0 ≤ x) :
    HasDerivWithinAt (lifetimeSurvival μ) (-(lifetimeSurvival μ x / m)) (Ici x) x := by
  have hc := equilibrium_fixed_survival_continuous μ m hm hpos hfix
  have hd := intervalIntegral.integral_hasDerivWithinAt_right
    ((lifetime_survival_antitone μ).intervalIntegrable.div_const m)
    (a := 0) (s := Ici x) (t := Ioi x)
    ((lifetime_survival_measurable μ).div_const m).aestronglyMeasurable.stronglyMeasurableAtFilter
    ((hc x hx).mono (fun _ ht => hx.trans ht.le) |>.div_const m)
  exact (hd.const_sub 1).congr_of_mem
    (fun y hy => equilibrium_fixed_integral_equation μ m hm hpos hfix y (hx.trans hy))
    (by simp)

/-- The exponential survival is forced by fixed-point equality itself. -/
theorem equilibrium_fixed_survival (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℝ) (hm : 0 < m) (hpos : μ (Ioi 0) = 1)
    (hfix : μ = equilibriumMeasure μ m) (x : ℝ) (hx : 0 ≤ x) :
    lifetimeSurvival μ x = Real.exp (-x / m) := by
  let G : ℝ → ℝ := fun t => Real.exp (t / m) * lifetimeSurvival μ t
  have hc : ContinuousOn G (Icc 0 x) :=
    (continuous_id.div_const m).rexp.continuousOn.mul
      ((equilibrium_fixed_survival_continuous μ m hm hpos hfix).mono Icc_subset_Ici_self)
  have hd : ∀ t ∈ Ico 0 x, HasDerivWithinAt G 0 (Ici t) t := by
    intro t ht
    convert (((hasDerivAt_id t).div_const m).exp.hasDerivWithinAt.mul
      (equilibrium_fixed_survival_derivative μ m hm hpos hfix t ht.1)) using 1
    ring
  have he := constant_of_has_deriv_right_zero hc hd x ⟨hx, le_rfl⟩
  have h0 : lifetimeSurvival μ 0 = 1 := by simp [lifetimeSurvival, hpos]
  have he' : Real.exp (x / m) * lifetimeSurvival μ x = 1 := by simpa [G, h0] using he
  rw [neg_div, Real.exp_neg]
  rw [← one_div]
  apply (eq_div_iff (Real.exp_ne_zero (x / m))).mpr
  simpa [mul_comm] using he'

theorem exponential_lifetime_survival (m : ℝ) (hm : 0 < m) (t : ℝ) (ht : 0 ≤ t) :
    lifetimeSurvival (gammaMeasure 1 m⁻¹) t = Real.exp (-t / m) := by
  simpa only [lifetimeSurvival, gammaShapeSurvival, div_eq_mul_inv, neg_mul, mul_neg, mul_comm]
    using gamma_shape_one_survival m⁻¹ t (inv_pos.mpr hm) ht

theorem exponential_lifetime_positive (m : ℝ) (hm : 0 < m) :
    gammaMeasure 1 m⁻¹ (Ioi 0) = 1 := by
  rw [← ENNReal.toReal_eq_one_iff]
  simpa [lifetimeSurvival] using exponential_lifetime_survival m hm 0 le_rfl

theorem equilibrium_measure_of_exponential_survival (μ : Measure ℝ)
    (m : ℝ) (hm : 0 < m)
    (hS : ∀ t ≥ 0, lifetimeSurvival μ t = Real.exp (-t / m)) :
    equilibriumMeasure μ m = gammaMeasure 1 m⁻¹ := by
  haveI : IsProbabilityMeasure (gammaMeasure 1 m⁻¹) :=
    isProbabilityMeasureGamma (by norm_num) (inv_pos.mpr hm)
  have ha : ∀ᵐ t ∂gammaMeasure 1 m⁻¹, t ∈ Ioi 0 := by
    rw [ae_iff]
    change gammaMeasure 1 m⁻¹ (Ioi 0)ᶜ = 0
    rw [measure_compl measurableSet_Ioi (measure_ne_top _ _), measure_univ,
      exponential_lifetime_positive m hm, tsub_self]
  calc
    equilibriumMeasure μ m = (volume.restrict (Ioi 0)).withDensity (gammaPDF 1 m⁻¹) := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change ENNReal.ofReal (lifetimeSurvival μ t / m) = ENNReal.ofReal (gammaPDFReal 1 m⁻¹ t)
      rw [hS t ht.le, gamma_shape_one_density _ _ ht.le]
      congr 1
      simp only [div_eq_mul_inv, mul_comm, neg_mul, mul_neg]
    _ = (gammaMeasure 1 m⁻¹).restrict (Ioi 0) :=
      (restrict_withDensity measurableSet_Ioi _).symm
    _ = gammaMeasure 1 m⁻¹ := Measure.restrict_eq_self_of_ae_mem ha

/-- The full measure-level fixed-point characterization. In particular, a
candidate density is not a hypothesis. The marked scale is forced as well. -/
theorem equilibrium_fixed_iff_exponential (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℝ) (hm : 0 < m) (hpos : μ (Ioi 0) = 1) :
    μ = equilibriumMeasure μ m ↔ μ = gammaMeasure 1 m⁻¹ := by
  constructor
  · intro hfix
    exact hfix.trans (equilibrium_measure_of_exponential_survival μ m hm
      (equilibrium_fixed_survival μ m hm hpos hfix))
  · intro he
    subst μ
    exact (equilibrium_measure_of_exponential_survival _ m hm
      (exponential_lifetime_survival m hm)).symm

/-- Corollary 3.17, with the scale given by the lifetime's actual mean. -/
theorem equilibrium_fixed_points (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : μ (Ioi 0) = 1) (hm : 0 < ∫ t : ℝ, t ∂μ) :
    μ = equilibriumMeasure μ (∫ t : ℝ, t ∂μ) ↔
      μ = gammaMeasure 1 (∫ t : ℝ, t ∂μ)⁻¹ :=
  equilibrium_fixed_iff_exponential μ _ hm hpos

theorem gamma_equilibrium_density :
    equilibriumMeasure (gammaMeasure 2 1) 2 =
      (volume.restrict (Ioi 0)).withDensity
        (fun t => ENNReal.ofReal ((1+t)*Real.exp (-t)/2)) := by
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hs : lifetimeSurvival (gammaMeasure 2 1) t = (1+t)*Real.exp (-t) := by
    simpa [lifetimeSurvival, gammaShapeSurvival, gammaSurvival] using
      gamma_shape_two_survival 1 t (by norm_num) ht.le
  rw [hs]

/-- The displayed equilibrium density identifies the original Gamma lifetime
and its mean even among candidates with atoms or no initial density. -/
theorem gamma_equilibrium_identifies (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℝ) (hm : 0 < m) (hpos : μ (Ioi 0) = 1)
    (he : equilibriumMeasure μ m =
      (volume.restrict (Ioi 0)).withDensity
        (fun t => ENNReal.ofReal ((1+t)*Real.exp (-t)/2))) :
    m = 2 ∧ μ = gammaMeasure 2 1 := by
  haveI : IsProbabilityMeasure (gammaMeasure 2 1) := isProbabilityMeasureGamma
    (by norm_num) (by norm_num)
  have hg : gammaMeasure 2 1 (Ioi 0) = 1 := by
    rw [← ENNReal.toReal_eq_one_iff]
    simpa [gammaShapeSurvival, gammaSurvival] using
      gamma_shape_two_survival 1 0 (by norm_num) le_rfl
  exact equilibrium_positive_inverse μ _ m 2 hm (by norm_num) hpos hg
    (he.trans gamma_equilibrium_density.symm)

end
end Sigma
