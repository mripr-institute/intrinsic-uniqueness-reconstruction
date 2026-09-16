import SigmaProbDeficitDerivative
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff

theorem potential_analyticAt (t : ℝ) (ht : 0 < t) :
    AnalyticAt ℝ SigmaBase.potential t := by
  have h : ContDiffAt ℝ ω SigmaBase.potential t :=
    (contDiffAt_id.sub contDiffAt_const).sub ((Real.contDiffAt_log).mpr ht.ne')
  exact h.analyticAt

def potentialQuadraticFactor : ℝ → ℝ := dslope (dslope SigmaBase.potential 1) 1

theorem potential_quadratic_factor_analytic : AnalyticAt ℝ potentialQuadraticFactor 1 := by
  rcases potential_analyticAt 1 (by norm_num) with ⟨p,hp⟩
  exact ⟨_,hp.has_fpower_series_dslope_fslope.has_fpower_series_dslope_fslope⟩

theorem potential_slope_analytic : AnalyticAt ℝ (dslope SigmaBase.potential 1) 1 := by
  rcases potential_analyticAt 1 (by norm_num) with ⟨p,hp⟩
  exact ⟨_,hp.has_fpower_series_dslope_fslope⟩

theorem potential_derivative_one : deriv SigmaBase.potential 1 = 0 := by
  simpa using (SigmaBase.potential_hasDerivAt (show (0:ℝ)<1 by norm_num)).deriv

theorem potential_quadratic_factorization (t : ℝ) :
    SigmaBase.potential t = (t-1)^2*potentialQuadraticFactor t := by
  have h₁ := sub_smul_dslope SigmaBase.potential (1:ℝ) t
  have h₂ := sub_smul_dslope (dslope SigmaBase.potential 1) (1:ℝ) t
  simp only [smul_eq_mul,dslope_same,potential_derivative_one] at h₁ h₂
  simp only [SigmaBase.potential,Real.log_one,sub_self] at h₁
  dsimp [potentialQuadraticFactor]
  rw [sub_zero] at h₂
  rw [← h₂] at h₁
  dsimp [SigmaBase.potential]
  nlinarith [h₁]

theorem potential_quadratic_factor_one : potentialQuadraticFactor 1 = 1/2 := by
  let s : ℝ → ℝ := dslope SigmaBase.potential 1
  have hs : AnalyticAt ℝ s 1 := potential_slope_analytic
  have hs₁ : s 1 = 0 := by simp [s,potential_derivative_one]
  have hsd : HasDerivAt s (potentialQuadraticFactor 1) 1 := by
    simpa [potentialQuadraticFactor,s] using hs.differentiableAt.hasDerivAt
  have hds : DifferentiableAt ℝ (deriv s) 1 :=
    (((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).analyticAt (fderiv ℝ s 1)).comp hs.fderiv).differentiableAt
  have he : (fun x : ℝ => 1-1/x) =ᶠ[𝓝 1]
      (fun x => s x+(x-1)*deriv s x) := by
    filter_upwards [Ioi_mem_nhds (show (0:ℝ)<1 by norm_num),
      hs.eventually_analyticAt] with x hx hsa
    have hd : HasDerivAt (fun x => (x-1)*s x) (s x+(x-1)*deriv s x) x := by
      convert ((hasDerivAt_id x).sub_const 1).mul hsa.differentiableAt.hasDerivAt using 1 <;> simp only [id_eq] <;> ring
    have heq : (fun x => (x-1)*s x) = SigmaBase.potential := by
      funext y
      simpa [s,SigmaBase.potential] using sub_smul_dslope SigmaBase.potential (1:ℝ) y
    rw [heq] at hd
    exact (SigmaBase.potential_hasDerivAt hx).unique hd
  have hh := hsd.add (((hasDerivAt_id (1:ℝ)).sub_const 1).mul hds.hasDerivAt)
  have hleft : HasDerivAt (fun x : ℝ => 1-1/x) 1 1 := by
    convert (hasDerivAt_const (1:ℝ) (1:ℝ)).sub
      ((hasDerivAt_const (1:ℝ) (1:ℝ)).div (hasDerivAt_id 1) (by norm_num)) using 1 <;> norm_num
  have hu := hleft.unique (hh.congr_of_eventuallyEq he)
  simp only [id_eq,sub_self,zero_mul,one_mul,add_zero,hsd.deriv] at hu
  linarith


theorem potential_quadratic_factor_pos (t : ℝ) (ht : 0 < t) :
    0 < potentialQuadraticFactor t := by
  by_cases h : t=1
  · simp [h,potential_quadratic_factor_one]
  have hI : 0 < SigmaBase.potential t := by
    rcases lt_or_gt_of_ne h with h | h
    · have hh := intrinsic_potential_two_branch.left_strict ⟨ht,h.le⟩
        (show (1:ℝ)∈Ioc 0 1 by norm_num) h
      simpa [SigmaBase.potential] using hh
    · have hh := intrinsic_potential_two_branch.right_strict
        (show (1:ℝ)∈Ici 1 by simp) h.le h
      simpa [SigmaBase.potential] using hh
  have he := potential_quadratic_factorization t
  have hs : 0 < (t-1)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr h)
  nlinarith

def deficitNormalCoordinate (t : ℝ) : ℝ := (t-1)*Real.sqrt (2*potentialQuadraticFactor t)

theorem deficit_normal_coordinate_one : deficitNormalCoordinate 1 = 0 := by
  simp [deficitNormalCoordinate]

theorem deficit_normal_coordinate_square (t : ℝ) (ht : 0 < t) :
    (deficitNormalCoordinate t)^2 = 2*SigmaBase.potential t := by
  rw [deficitNormalCoordinate,mul_pow,Real.sq_sqrt (by nlinarith [potential_quadratic_factor_pos t ht]),
    potential_quadratic_factorization]
  ring

theorem deficit_normal_coordinate_analytic : AnalyticAt ℝ deficitNormalCoordinate 1 := by
  apply ContDiffAt.analyticAt
  apply (contDiffAt_id.sub contDiffAt_const).mul
  apply (contDiffAt_const.mul potential_quadratic_factor_analytic.contDiffAt).sqrt
  norm_num [potential_quadratic_factor_one]

theorem deficit_normal_coordinate_derivative_one : HasDerivAt deficitNormalCoordinate 1 1 := by
  have hr := potential_quadratic_factor_analytic.differentiableAt.hasDerivAt
  have hh := ((hasDerivAt_id (1:ℝ)).sub_const 1).mul
    ((hr.const_mul 2).sqrt (by norm_num [potential_quadratic_factor_one]))
  convert hh using 1 <;> simp [deficitNormalCoordinate,potential_quadratic_factor_one]

theorem canonical_deficit_involution_continuousAt (t : ℝ) (ht : 0 < t) :
    ContinuousAt canonicalDeficitInvolution t := by
  have hm : StrictMonoOn (fun x => -canonicalDeficitInvolution x) (Ioi (0:ℝ)) := by
    intro x hx y hy hxy
    exact neg_lt_neg (canonical_deficit_involution_strictAnti hx hy hxy)
  have him : (fun x => -canonicalDeficitInvolution x) '' Ioi (0:ℝ) = Iio 0 := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact neg_neg_of_pos (canonical_deficit_involution_positive_level x hx).1
    · intro hy
      have hp : 0 < -y := neg_pos.mpr hy
      exact ⟨canonicalDeficitInvolution (-y),
        (canonical_deficit_involution_positive_level (-y) hp).1,by
          dsimp
          rw [canonical_deficit_involution_involutive (-y) hp,neg_neg]⟩
  have hh := hm.continuousAt_of_image_mem_nhds (Ioi_mem_nhds ht) (by
    rw [him]
    exact Iio_mem_nhds (neg_neg_of_pos (canonical_deficit_involution_positive_level t ht).1))
  simpa only [neg_neg] using hh.neg

theorem deficit_normal_coordinate_pair (t : ℝ) (ht : 0 < t) :
    deficitNormalCoordinate (canonicalDeficitInvolution t) = -deficitNormalCoordinate t := by
  have hj := canonical_deficit_involution_positive_level t ht
  have hsq : deficitNormalCoordinate (canonicalDeficitInvolution t)^2 =
      deficitNormalCoordinate t^2 := by
    rw [deficit_normal_coordinate_square _ hj.1,deficit_normal_coordinate_square _ ht,hj.2]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · rcases lt_trichotomy t 1 with ht1 | rfl | ht1
    · have hja : 1 < canonicalDeficitInvolution t :=
        (canonical_deficit_involution_lower t ht ht1).1
      have hq : deficitNormalCoordinate t < 0 := mul_neg_of_neg_of_pos
        (sub_neg.mpr ht1) (Real.sqrt_pos.2 (by nlinarith [potential_quadratic_factor_pos t ht]))
      have hqj : 0 < deficitNormalCoordinate (canonicalDeficitInvolution t) :=
        mul_pos (sub_pos.mpr hja) (Real.sqrt_pos.2 (by
          nlinarith [potential_quadratic_factor_pos _ hj.1]))
      linarith
    · simp [canonical_deficit_involution_anchor,deficit_normal_coordinate_one]
    · have hja : canonicalDeficitInvolution t < 1 := by
        have hh := canonical_deficit_involution_strictAnti (show (1:ℝ)∈Ioi 0 by norm_num) ht ht1
        simpa [canonical_deficit_involution_anchor] using hh
      have hq : 0 < deficitNormalCoordinate t := mul_pos
        (sub_pos.mpr ht1) (Real.sqrt_pos.2 (by nlinarith [potential_quadratic_factor_pos t ht]))
      have hqj : deficitNormalCoordinate (canonicalDeficitInvolution t) < 0 :=
        mul_neg_of_neg_of_pos (sub_neg.mpr hja) (Real.sqrt_pos.2 (by
          nlinarith [potential_quadratic_factor_pos _ hj.1]))
      linarith
  · exact h


theorem contDiffAt_of_local_implicit_equation {f g h : ℝ → ℝ} {a d : ℝ}
    (hf : ContDiffAt ℝ ω f (g a)) (hfd : HasDerivAt f d (g a)) (hd : d ≠ 0)
    (hg : ContinuousAt g a) (hh : ContDiffAt ℝ ω h a)
    (he : (fun x => f (g x)) =ᶠ[𝓝 a] h) : ContDiffAt ℝ ω g a := by
  have hs := hf.hasStrictDerivAt' hfd (by simp)
  let hf' := hs.hasStrictFDerivAt_equiv hd
  let e := hf'.toPartialHomeomorph f
  have hsource : g a ∈ e.source := hf'.mem_toPartialHomeomorph_source
  have htarget : f (g a) ∈ e.target := hf'.image_mem_toPartialHomeomorph_target
  have hleft : e.symm (f (g a)) = g a := e.left_inv hsource
  have hsi : ContDiffAt ℝ ω e.symm (f (g a)) := by
    apply e.contDiffAt_symm_deriv hd htarget
    · simpa only [hleft] using hfd
    · simpa only [hleft] using hf
  have ha : f (g a) = h a := he.self_of_nhds
  rw [ha] at hsi
  have hc := hsi.comp a hh
  apply hc.congr_of_eventuallyEq
  have hm : ∀ᶠ x in 𝓝 a, g x ∈ e.source :=
    hg (e.open_source.mem_nhds hsource)
  filter_upwards [hm,he] with x hx hex
  change g x = e.symm (h x)
  rw [← hex]
  exact (e.left_inv hx).symm

theorem canonical_deficit_involution_analytic_at_one :
    AnalyticAt ℝ canonicalDeficitInvolution 1 := by
  apply ContDiffAt.analyticAt
  apply contDiffAt_of_local_implicit_equation
    (f := deficitNormalCoordinate) (h := fun t => -deficitNormalCoordinate t)
    (d := 1)
  · simpa [canonical_deficit_involution_anchor] using
      (deficit_normal_coordinate_analytic.contDiffAt : ContDiffAt ℝ ω deficitNormalCoordinate 1)
  · simpa [canonical_deficit_involution_anchor] using deficit_normal_coordinate_derivative_one
  · norm_num
  · exact canonical_deficit_involution_continuousAt 1 (by norm_num)
  · exact deficit_normal_coordinate_analytic.contDiffAt.neg
  · filter_upwards [Ioi_mem_nhds (show (0:ℝ)<1 by norm_num)] with t ht
    exact deficit_normal_coordinate_pair t ht

theorem canonical_deficit_involution_derivative_one :
    HasDerivAt canonicalDeficitInvolution (-1) 1 := by
  have hj := canonical_deficit_involution_analytic_at_one.differentiableAt.hasDerivAt
  have hq : HasDerivAt deficitNormalCoordinate 1 (canonicalDeficitInvolution 1) := by
    simpa [canonical_deficit_involution_anchor] using deficit_normal_coordinate_derivative_one
  have he : (fun t => deficitNormalCoordinate (canonicalDeficitInvolution t)) =ᶠ[𝓝 1]
      (fun t => -deficitNormalCoordinate t) := by
    filter_upwards [Ioi_mem_nhds (show (0:ℝ)<1 by norm_num)] with t ht
    exact deficit_normal_coordinate_pair t ht
  have hu := (hq.comp 1 hj).unique
    (deficit_normal_coordinate_derivative_one.neg.congr_of_eventuallyEq he)
  simp only [one_mul] at hu
  rwa [hu] at hj

theorem canonical_deficit_involution_analytic (t : ℝ) (ht : 0 < t) :
    AnalyticAt ℝ canonicalDeficitInvolution t := by
  by_cases h : t=1
  · simpa [h] using canonical_deficit_involution_analytic_at_one
  have hj := canonical_deficit_involution_positive_level t ht
  have hjne : canonicalDeficitInvolution t ≠ 1 := by
    intro he
    have hh := canonical_deficit_involution_involutive t ht
    rw [he,canonical_deficit_involution_anchor] at hh
    exact h hh.symm
  apply ContDiffAt.analyticAt
  apply contDiffAt_of_local_implicit_equation
    (f := SigmaBase.potential) (h := SigmaBase.potential)
    (d := 1-1/canonicalDeficitInvolution t)
  · exact (potential_analyticAt _ hj.1).contDiffAt
  · exact SigmaBase.potential_hasDerivAt hj.1
  · intro he
    apply hjne
    have hh : 1/canonicalDeficitInvolution t = 1 := by linarith
    have hh' := (div_eq_iff hj.1.ne').mp hh
    simpa using hh'.symm
  · exact canonical_deficit_involution_continuousAt t ht
  · exact (potential_analyticAt _ ht).contDiffAt
  · filter_upwards [Ioi_mem_nhds ht] with x hx
    exact (canonical_deficit_involution_positive_level x hx).2

theorem canonical_deficit_involution_smooth :
    ContDiffOn ℝ ω canonicalDeficitInvolution (Ioi 0) := by
  intro t ht
  exact (canonical_deficit_involution_analytic t ht).contDiffAt.contDiffWithinAt

end
end Sigma
