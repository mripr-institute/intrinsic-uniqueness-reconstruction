import SigmaComplexCharacteristicPoles
import SigmaRealCharacteristicAnalytic
import Mathlib.Analysis.Convex.Normed

namespace Sigma
noncomputable section
open Filter
open scoped Topology

/-- The actual convergent Taylor germ cannot extend its convergence disk across
a zero of an entire denominator where the entire numerator stays nonzero. -/
theorem quotient_taylor_radius_le {f d n : ℂ → ℂ}
    {P : FormalMultilinearSeries ℂ ℂ ℂ} (hP : HasFPowerSeriesAt f P 0)
    (hd : ∀ z, AnalyticAt ℂ d z) (hn : ∀ z, AnalyticAt ℂ n z)
    (he : (fun z => d z*f z) =ᶠ[𝓝 0] n) (p : ℂ) (hp : d p=0) (hpn : n p ≠ 0) :
    P.radius ≤ (‖p‖₊ : ENNReal) := by
  by_contra hbound
  have hlt : (‖p‖₊ : ENNReal)<P.radius := lt_of_not_ge hbound
  obtain ⟨r,hpr,hrP⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
  have hpr' : ‖p‖<(r : ℝ) := by exact_mod_cast hpr
  have hr0 : (0 : ℝ)<r := lt_of_le_of_lt (norm_nonneg p) hpr'
  have hsum := (P.hasFPowerSeriesOnBall hP.radius_pos).analyticOnNhd
  have ha : AnalyticOnNhd ℂ (fun z => d z*P.sum z) (Metric.ball 0 r) := by
    intro z hz
    apply (hd z).mul (hsum z ?_)
    have hz' : z ∈ EMetric.ball (0 : ℂ) (r : ENNReal) := by
      simpa only [Metric.emetric_ball_nnreal] using hz
    exact EMetric.ball_subset_ball (le_of_lt hrP) hz'
  have hloc : (fun z => d z*P.sum z) =ᶠ[𝓝 0] n := by
    obtain ⟨s,hs⟩ := hP
    filter_upwards [he,EMetric.ball_mem_nhds (0 : ℂ) hs.r_pos] with z hz hzs
    have hfz := hs.sum hzs
    simp only [zero_add] at hfz
    rwa [←hfz]
  have hglobal := ha.eqOn_of_preconnected_of_eventuallyEq
    (fun z _ => hn z) (convex_ball (0 : ℂ) (r : ℝ)).isPreconnected
    (by simpa using hr0 : (0 : ℂ) ∈ Metric.ball 0 (r : ℝ)) hloc
  have hpoint := hglobal (show p ∈ Metric.ball (0 : ℂ) r by simpa using hpr')
  exact hpn (by simpa [hp] using hpoint.symm)

/-- Analyticity throughout an open complex disk supplies the converse radius bound
for the very same Taylor germ, via uniqueness of native power-series coefficients. -/
theorem analytic_disk_le_taylor_radius {f : ℂ → ℂ}
    {P : FormalMultilinearSeries ℂ ℂ ℂ} (hP : HasFPowerSeriesAt f P 0)
    (R : NNReal) (ha : AnalyticOnNhd ℂ f (Metric.ball 0 R)) :
    (R : ENNReal) ≤ P.radius := by
  apply le_of_forall_lt
  intro r hr
  obtain ⟨s,hrs,hsR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
  by_cases hs0 : s=0
  · subst s
    exact False.elim (not_lt_of_ge (zero_le r) hrs)
  have hspos : (0 : ℝ)<s := by exact_mod_cast bot_lt_iff_ne_bot.mpr hs0
  have hsR' : (s : ℝ)<R := by exact_mod_cast hsR
  have hd : DifferentiableOn ℂ f (Metric.closedBall 0 s) := by
    intro z hz
    exact (ha z (Metric.closedBall_subset_ball hsR' hz)).differentiableAt.differentiableWithinAt
  have hseries := hd.hasFPowerSeriesOnBall hspos
  have hcoeff := hP.eq_formalMultilinearSeries hseries.hasFPowerSeriesAt
  rw [hcoeff]
  exact lt_of_lt_of_le hrs hseries.r_le

theorem complex_characteristic_on_reals (u : ℝ) :
    complexTodd (u : ℂ)=(realTodd u : ℂ) ∧
    complexAhat (u : ℂ)=(realAhat u : ℂ) ∧
    complexLgenus (u : ℂ)=(realLgenus u : ℂ) := by
  by_cases hu : u=0
  · subst u
    simp only [Complex.ofReal_zero,complex_todd_zero,complex_ahat_zero,complex_lgenus_zero,
      real_todd_zero,real_characteristic_zero.1,real_characteristic_zero.2.1,Complex.ofReal_one,
      and_self]
  · have huc : (u : ℂ) ≠ 0 := by exact_mod_cast hu
    rw [complex_todd_quotient huc,complex_ahat_quotient huc,complex_lgenus_quotient huc,
      real_todd_quotient u hu,real_ahat_quotient u hu,real_lgenus_quotient u hu,
      Real.tanh_eq_sinh_div_cosh,div_div_eq_mul_div]
    push_cast
    exact ⟨rfl,rfl,rfl⟩

theorem complex_todd_local_identity :
    (fun z => complexToddDenominator z*complexTodd z) =ᶠ[𝓝 0] (fun z : ℂ => z) := by
  have hc := (analytic_dslope_at_base (complex_todd_denominator_analytic 0)).continuousAt
  have h0 : dslope complexToddDenominator 0 0 ≠ 0 := by
    simp [dslope_same,(complex_todd_denominator_derivative 0).deriv]
  filter_upwards [hc.eventually_ne h0] with z hz
  have he := sub_smul_dslope complexToddDenominator 0 z
  simp only [smul_eq_mul,sub_zero,complexToddDenominator,neg_zero,Complex.exp_zero,
    sub_self,sub_zero] at he
  change (1-Complex.exp (-z))*(dslope complexToddDenominator 0 z)⁻¹=z
  rw [←he,mul_assoc,mul_inv_cancel₀ hz,mul_one]

theorem complex_ahat_local_identity :
    (fun z => Complex.sinh (z/2)*complexAhat z) =ᶠ[𝓝 0] (fun z : ℂ => z/2) := by
  have hi : AnalyticAt ℂ (fun z : ℂ => z/2) 0 :=
    analyticAt_id.div analyticAt_const (by norm_num)
  have hs : AnalyticAt ℂ (dslope Complex.sinh 0) ((0 : ℂ)/2) := by
    simpa using analytic_dslope_at_base (complex_sinh_analytic 0)
  have hc := (hs.comp (f:=fun z : ℂ => z/2) hi).continuousAt
  have h0 : dslope Complex.sinh 0 ((0 : ℂ)/2) ≠ 0 := by
    simp [dslope_same,Complex.deriv_sinh]
  filter_upwards [hc.eventually_ne h0] with z hz
  change dslope Complex.sinh 0 (z/2) ≠ 0 at hz
  have he := sub_smul_dslope Complex.sinh 0 (z/2)
  simp only [smul_eq_mul,sub_zero,Complex.sinh_zero] at he
  change Complex.sinh (z/2)*(dslope Complex.sinh 0 (z/2))⁻¹=z/2
  rw [←he,mul_assoc,mul_inv_cancel₀ hz,mul_one]

theorem complex_lgenus_local_identity :
    (fun z => Complex.sinh z*complexLgenus z) =ᶠ[𝓝 0]
      (fun z : ℂ => z*Complex.cosh z) := by
  have hc := (analytic_dslope_at_base (complex_sinh_analytic 0)).continuousAt
  have h0 : dslope Complex.sinh 0 0 ≠ 0 := by simp [dslope_same,Complex.deriv_sinh]
  filter_upwards [hc.eventually_ne h0] with z hz
  have he := sub_smul_dslope Complex.sinh 0 z
  simp only [smul_eq_mul,sub_zero,Complex.sinh_zero] at he
  change Complex.sinh z*(Complex.cosh z*(dslope Complex.sinh 0 z)⁻¹)=z*Complex.cosh z
  rw [←he]
  field_simp
  ring

theorem complex_todd_analytic_disk :
    AnalyticOnNhd ℂ complexTodd (Metric.ball 0 (2*Real.pi)) := by
  intro p hp
  have hnorm : ‖p‖<2*Real.pi := by simpa using hp
  by_cases hp0 : p=0
  · subst p
    exact complex_characteristic_analytic_zero.1
  · apply complex_todd_analytic_of_regular hp0
    intro hd
    have hmin := (complex_todd_ahat_nearest_poles p (Or.inl (complex_todd_simple_pole hp0 hd))).1
    linarith

theorem complex_ahat_analytic_disk :
    AnalyticOnNhd ℂ complexAhat (Metric.ball 0 (2*Real.pi)) := by
  intro p hp
  have hnorm : ‖p‖<2*Real.pi := by simpa using hp
  by_cases hp0 : p=0
  · subst p
    exact complex_characteristic_analytic_zero.2.1
  · apply complex_ahat_analytic_of_regular hp0
    intro hd
    have hmin := (complex_todd_ahat_nearest_poles p (Or.inr (complex_ahat_simple_pole hp0 hd))).1
    linarith

theorem complex_lgenus_analytic_disk :
    AnalyticOnNhd ℂ complexLgenus (Metric.ball 0 Real.pi) := by
  intro p hp
  have hnorm : ‖p‖<Real.pi := by simpa using hp
  by_cases hp0 : p=0
  · subst p
    exact complex_characteristic_analytic_zero.2.2
  · apply complex_lgenus_analytic_of_regular hp0
    intro hd
    have hmin := (complex_lgenus_nearest_poles p (complex_lgenus_simple_pole hp0 hd)).1
    linarith

theorem complex_todd_taylor_radius {P : FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : HasFPowerSeriesAt complexTodd P 0) : P.radius=ENNReal.ofReal (2*Real.pi) := by
  apply le_antisymm
  · have hb := quotient_taylor_radius_le hP complex_todd_denominator_analytic
      (fun _ => analyticAt_id) complex_todd_local_identity (2*Real.pi*Complex.I)
      ((complex_todd_denominator_zero_iff _).mpr ⟨1,by simp⟩)
      (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
    simpa [←ofReal_norm_eq_coe_nnnorm,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,ENNReal.ofReal_mul (show (0 : ℝ)≤2 by norm_num)] using hb
  · simpa only [ENNReal.coe_nnreal_eq,NNReal.coe_mk] using
      analytic_disk_le_taylor_radius hP ⟨2*Real.pi,by positivity⟩ complex_todd_analytic_disk

theorem complex_ahat_taylor_radius {P : FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : HasFPowerSeriesAt complexAhat P 0) : P.radius=ENNReal.ofReal (2*Real.pi) := by
  have hi (z : ℂ) : AnalyticAt ℂ (fun z : ℂ => z/2) z :=
    analyticAt_id.div analyticAt_const (by norm_num)
  apply le_antisymm
  · have hb := quotient_taylor_radius_le hP
      (fun z => (complex_sinh_analytic (z/2)).comp (f:=fun z : ℂ => z/2) (hi z))
      hi complex_ahat_local_identity (2*Real.pi*Complex.I)
      ((complex_sinh_half_zero_iff _).mpr ⟨1,by simp⟩)
      (div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero) (by norm_num))
    simpa [←ofReal_norm_eq_coe_nnnorm,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,ENNReal.ofReal_mul (show (0 : ℝ)≤2 by norm_num)] using hb
  · simpa only [ENNReal.coe_nnreal_eq,NNReal.coe_mk] using
      analytic_disk_le_taylor_radius hP ⟨2*Real.pi,by positivity⟩ complex_ahat_analytic_disk

theorem complex_lgenus_taylor_radius {P : FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : HasFPowerSeriesAt complexLgenus P 0) : P.radius=ENNReal.ofReal Real.pi := by
  have hz : Complex.sinh (Real.pi*Complex.I)=0 :=
    (complex_sinh_zero_iff _).mpr ⟨1,by simp⟩
  apply le_antisymm
  · have hb := quotient_taylor_radius_le hP complex_sinh_analytic
      (fun z => analyticAt_id.mul (complex_cosh_analytic z)) complex_lgenus_local_identity
      (Real.pi*Complex.I) hz
      (mul_ne_zero (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero)
        (complex_cosh_ne_zero_at_sinh_zero hz))
    simpa [←ofReal_norm_eq_coe_nnnorm,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos] using hb
  · simpa only [ENNReal.coe_nnreal_eq,NNReal.coe_mk] using
      analytic_disk_le_taylor_radius hP ⟨Real.pi,le_of_lt Real.pi_pos⟩ complex_lgenus_analytic_disk

theorem taylor_germ_sum_on_disk {f : ℂ → ℂ} {P : FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : HasFPowerSeriesAt f P 0) (R : NNReal) (hR : 0<R)
    (hr : (R : ENNReal) ≤ P.radius) (ha : AnalyticOnNhd ℂ f (Metric.ball 0 R)) :
    Set.EqOn P.sum f (Metric.ball 0 R) := by
  have hsum := (P.hasFPowerSeriesOnBall hP.radius_pos).analyticOnNhd
  have hs : AnalyticOnNhd ℂ P.sum (Metric.ball 0 R) := by
    intro z hz
    apply hsum z
    apply EMetric.ball_subset_ball hr
    simpa only [Metric.emetric_ball_nnreal] using hz
  apply hs.eqOn_of_preconnected_of_eventuallyEq ha (convex_ball (0 : ℂ) (R : ℝ)).isPreconnected
    (by simpa using hR : (0 : ℂ) ∈ Metric.ball 0 (R : ℝ))
  obtain ⟨s,hs⟩ := hP
  filter_upwards [EMetric.ball_mem_nhds (0 : ℂ) hs.r_pos] with z hz
  simpa only [zero_add] using (hs.sum hz).symm

theorem characteristic_taylor_series_exist :
    (∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt complexTodd P 0 ∧ P.radius=ENNReal.ofReal (2*Real.pi)) ∧
    (∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt complexAhat P 0 ∧ P.radius=ENNReal.ofReal (2*Real.pi)) ∧
    (∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt complexLgenus P 0 ∧ P.radius=ENNReal.ofReal Real.pi) := by
  obtain ⟨P,hP⟩ := complex_characteristic_analytic_zero.1
  obtain ⟨Q,hQ⟩ := complex_characteristic_analytic_zero.2.1
  obtain ⟨S,hS⟩ := complex_characteristic_analytic_zero.2.2
  exact ⟨⟨P,hP,complex_todd_taylor_radius hP⟩,⟨Q,hQ,complex_ahat_taylor_radius hQ⟩,
    ⟨S,hS,complex_lgenus_taylor_radius hS⟩⟩

theorem characteristic_taylor_on_reals {P : FormalMultilinearSeries ℂ ℂ ℂ}
    {f : ℂ → ℂ} {g : ℝ → ℝ} (hP : HasFPowerSeriesAt f P 0)
    (R : NNReal) (hR : 0<R) (ha : AnalyticOnNhd ℂ f (Metric.ball 0 R))
    (hg : ∀ u : ℝ, f (u : ℂ)=(g u : ℂ)) (u : ℝ) (hu : |u|<R) :
    HasSum (fun n => P n (fun _ => (u : ℂ))) (g u : ℂ) := by
  have hr := analytic_disk_le_taylor_radius hP R ha
  have hm : (u : ℂ) ∈ Metric.ball (0 : ℂ) R := by simpa using hu
  have hs := taylor_germ_sum_on_disk hP R hR hr ha hm
  have hb : (u : ℂ) ∈ EMetric.ball (0 : ℂ) P.radius := by
    apply EMetric.ball_subset_ball hr
    simpa only [Metric.emetric_ball_nnreal] using hm
  rw [hg u] at hs
  exact hs ▸ P.hasSum hb

theorem complex_todd_taylor_on_reals {P : FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : HasFPowerSeriesAt complexTodd P 0) (u : ℝ) (hu : |u|<2*Real.pi) :
    HasSum (fun n => P n (fun _ => (u : ℂ))) (realTodd u : ℂ) :=
  characteristic_taylor_on_reals hP ⟨2*Real.pi,by positivity⟩ (by change (0 : ℝ)<2*Real.pi; positivity)
    complex_todd_analytic_disk (fun u => (complex_characteristic_on_reals u).1) u hu

theorem complex_ahat_taylor_on_reals {P : FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : HasFPowerSeriesAt complexAhat P 0) (u : ℝ) (hu : |u|<2*Real.pi) :
    HasSum (fun n => P n (fun _ => (u : ℂ))) (realAhat u : ℂ) :=
  characteristic_taylor_on_reals hP ⟨2*Real.pi,by positivity⟩ (by change (0 : ℝ)<2*Real.pi; positivity)
    complex_ahat_analytic_disk (fun u => (complex_characteristic_on_reals u).2.1) u hu

theorem complex_lgenus_taylor_on_reals {P : FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : HasFPowerSeriesAt complexLgenus P 0) (u : ℝ) (hu : |u|<Real.pi) :
    HasSum (fun n => P n (fun _ => (u : ℂ))) (realLgenus u : ℂ) :=
  characteristic_taylor_on_reals hP ⟨Real.pi,le_of_lt Real.pi_pos⟩ Real.pi_pos
    complex_lgenus_analytic_disk (fun u => (complex_characteristic_on_reals u).2.2) u hu

theorem finite_taylor_disk_misses_real {P : FormalMultilinearSeries ℂ ℂ ℂ}
    (R : ℝ) (hR : 0≤R) (h : P.radius=ENNReal.ofReal R) :
    ((R+1 : ℝ) : ℂ) ∉ EMetric.ball (0 : ℂ) P.radius := by
  rw [h]
  have hrp : 0<R+1 := by linarith
  simp only [EMetric.mem_ball,edist_dist,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hrp]
  exact not_lt_of_ge (ENNReal.ofReal_le_ofReal (by linarith))

/-- Explicit real points outside each actual Taylor disk, despite all three
real characteristic functions being analytic on the full real line. -/
theorem characteristic_taylor_discs_do_not_cover_reals
    {P Q S : FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : HasFPowerSeriesAt complexTodd P 0)
    (hQ : HasFPowerSeriesAt complexAhat Q 0)
    (hS : HasFPowerSeriesAt complexLgenus S 0) :
    ((2*Real.pi+1 : ℝ) : ℂ) ∉ EMetric.ball 0 P.radius ∧
    ((2*Real.pi+1 : ℝ) : ℂ) ∉ EMetric.ball 0 Q.radius ∧
    ((Real.pi+1 : ℝ) : ℂ) ∉ EMetric.ball 0 S.radius :=
  ⟨finite_taylor_disk_misses_real _ (by positivity) (complex_todd_taylor_radius hP),
    finite_taylor_disk_misses_real _ (by positivity) (complex_ahat_taylor_radius hQ),
    finite_taylor_disk_misses_real _ (le_of_lt Real.pi_pos) (complex_lgenus_taylor_radius hS)⟩

end
end Sigma
