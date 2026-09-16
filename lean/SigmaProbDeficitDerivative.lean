import SigmaProbLambert
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.Calculus.Deriv.Inverse

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

def deficitLowerRoot (v : ℝ) := (canonicalDeficitRoots v).1
def deficitUpperRoot (v : ℝ) := (canonicalDeficitRoots v).2

theorem deficit_roots_strict (v : ℝ) (hv : 0 < v) :
    0 < deficitLowerRoot v ∧ deficitLowerRoot v < 1 ∧ 1 < deficitUpperRoot v := by
  have hs := canonical_deficit_roots_spec v hv.le
  have hl : deficitLowerRoot v < 1 := by
    by_contra hn
    have he : (canonicalDeficitRoots v).1 = 1 :=
      le_antisymm hs.2.1 (le_of_not_gt hn)
    have hh := hs.2.2.2.1
    rw [he] at hh
    simp [SigmaBase.potential] at hh
    linarith
  have hr : 1 < deficitUpperRoot v := by
    by_contra hn
    have he : (canonicalDeficitRoots v).2 = 1 :=
      le_antisymm (le_of_not_gt hn) hs.2.2.1
    have hh := hs.2.2.2.2
    rw [he] at hh
    simp [SigmaBase.potential] at hh
    linarith
  exact ⟨hs.1,hl,hr⟩

theorem deficit_lower_strictAnti : StrictAntiOn deficitLowerRoot (Ioi (0 : ℝ)) := by
  intro u hu v hv huv
  have hs := canonical_deficit_roots_spec u hu.le
  have ht := canonical_deficit_roots_spec v hv.le
  by_contra hn
  have hh := intrinsic_potential_two_branch.left_strict.antitoneOn ⟨hs.1,hs.2.1⟩
    ⟨ht.1,ht.2.1⟩ (le_of_not_gt hn)
  rw [hs.2.2.2.1,ht.2.2.2.1] at hh
  linarith

theorem deficit_upper_strictMono : StrictMonoOn deficitUpperRoot (Ioi (0 : ℝ)) := by
  intro u hu v hv huv
  have hs := canonical_deficit_roots_spec u hu.le
  have ht := canonical_deficit_roots_spec v hv.le
  by_contra hn
  have hh := intrinsic_potential_two_branch.right_strict.monotoneOn ht.2.2.1 hs.2.2.1
    (le_of_not_gt hn)
  rw [hs.2.2.2.2,ht.2.2.2.2] at hh
  linarith

theorem deficit_lower_image : deficitLowerRoot '' Ioi (0 : ℝ) = Ioo 0 1 := by
  ext t
  constructor
  · rintro ⟨v,hv,rfl⟩
    have hs := deficit_roots_strict v hv
    exact ⟨hs.1,hs.2.1⟩
  · intro ht
    refine ⟨SigmaBase.potential t,?_,canonical_deficit_lower_inverse t ht.1 ht.2.le⟩
    have hh := intrinsic_potential_two_branch.left_strict ⟨ht.1,ht.2.le⟩
      (show (1 : ℝ) ∈ Ioc 0 1 by norm_num) ht.2
    simpa [SigmaBase.potential] using hh

theorem deficit_upper_image : deficitUpperRoot '' Ioi (0 : ℝ) = Ioi 1 := by
  ext t
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact (deficit_roots_strict v hv).2.2
  · intro ht
    refine ⟨SigmaBase.potential t,?_,canonical_deficit_upper_inverse t ht.le⟩
    have hh := intrinsic_potential_two_branch.right_strict (show (1 : ℝ) ∈ Ici 1 by simp)
      ht.le ht
    simpa [SigmaBase.potential] using hh

theorem deficit_upper_continuousAt (v : ℝ) (hv : 0 < v) : ContinuousAt deficitUpperRoot v := by
  apply deficit_upper_strictMono.continuousAt_of_image_mem_nhds (Ioi_mem_nhds hv)
  rw [deficit_upper_image]
  exact Ioi_mem_nhds (deficit_roots_strict v hv).2.2

theorem deficit_lower_continuousAt (v : ℝ) (hv : 0 < v) : ContinuousAt deficitLowerRoot v := by
  have hn : StrictMonoOn (fun x => -deficitLowerRoot x) (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    exact neg_lt_neg (deficit_lower_strictAnti hx hy hxy)
  have him : (fun x => -deficitLowerRoot x) '' Ioi (0 : ℝ) = Ioo (-1) 0 := by
    rw [← image_image Neg.neg deficitLowerRoot (Ioi (0 : ℝ)),deficit_lower_image]
    ext t
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨by linarith [hu.2],by linarith [hu.1]⟩
    · intro ht
      exact ⟨-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,neg_neg t⟩
  have hc := hn.continuousAt_of_image_mem_nhds (Ioi_mem_nhds hv) (by
    rw [him]
    have hs := deficit_roots_strict v hv
    exact Ioo_mem_nhds (by linarith [hs.2.1]) (by linarith [hs.1]))
  simpa only [neg_neg] using hc.neg

theorem deficit_lower_derivative (v : ℝ) (hv : 0 < v) :
    HasDerivAt deficitLowerRoot (deficitLowerRoot v/(deficitLowerRoot v-1)) v := by
  have hs := deficit_roots_strict v hv
  have hn : 1-1/deficitLowerRoot v ≠ 0 := by
    have hh : 1 < 1/deficitLowerRoot v := (one_lt_div hs.1).mpr hs.2.1
    linarith
  have hi : ∀ᶠ w in 𝓝 v, SigmaBase.potential (deficitLowerRoot w) = w := by
    filter_upwards [Ioi_mem_nhds hv] with w hw
    exact (canonical_deficit_roots_spec w hw.le).2.2.2.1
  have hh := (SigmaBase.potential_hasDerivAt hs.1).of_local_left_inverse
    (deficit_lower_continuousAt v hv) hn hi
  convert hh using 1
  have hden : deficitLowerRoot v-1 ≠ 0 := sub_ne_zero.mpr hs.2.1.ne
  field_simp [hs.1.ne',hden]

theorem deficit_upper_derivative (v : ℝ) (hv : 0 < v) :
    HasDerivAt deficitUpperRoot (deficitUpperRoot v/(deficitUpperRoot v-1)) v := by
  have hs := deficit_roots_strict v hv
  have hp : 0 < deficitUpperRoot v := by linarith [hs.2.2]
  have hn : 1-1/deficitUpperRoot v ≠ 0 := by
    have hh : 1/deficitUpperRoot v < 1 := (div_lt_one hp).mpr hs.2.2
    linarith
  have hi : ∀ᶠ w in 𝓝 v, SigmaBase.potential (deficitUpperRoot w) = w := by
    filter_upwards [Ioi_mem_nhds hv] with w hw
    exact (canonical_deficit_roots_spec w hw.le).2.2.2.2
  have hh := (SigmaBase.potential_hasDerivAt hp).of_local_left_inverse
    (deficit_upper_continuousAt v hv) hn hi
  convert hh using 1
  field_simp

def gammaDeficitCDF (v : ℝ) : ℝ := (gammaDeficitProbability (Iic v)).toReal

def gammaDeficitDensity (v : ℝ) : ℝ := Real.exp (-1-v)*
  (deficitLowerRoot v/(1-deficitLowerRoot v)+deficitUpperRoot v/(deficitUpperRoot v-1))

theorem gamma_deficit_cdf_real (v : ℝ) (hv : 0 ≤ v) :
    gammaDeficitCDF v = gammaSurvival (deficitLowerRoot v)-gammaSurvival (deficitUpperRoot v) := by
  have hs := canonical_deficit_roots_spec v hv
  rw [gammaDeficitCDF,canonical_deficit_cdf v hv]
  apply ENNReal.toReal_ofReal
  rw [← gamma_density_interval _ _ (hs.2.1.trans hs.2.2.1)]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (SigmaPresentations.density_pos (hs.1.trans_le ht.1)).le

theorem gamma_deficit_cdf_derivative (v : ℝ) (hv : 0 < v) :
    HasDerivAt gammaDeficitCDF (gammaDeficitDensity v) v := by
  have hs := canonical_deficit_roots_spec v hv.le
  have hp : 0 < deficitUpperRoot v := by linarith [(deficit_roots_strict v hv).2.2]
  have hpa : 0 < deficitLowerRoot v := hs.1
  have hIa : SigmaBase.potential (deficitLowerRoot v) = v := hs.2.2.2.1
  have hIb : SigmaBase.potential (deficitUpperRoot v) = v := hs.2.2.2.2
  have hl := (gamma_survival_derivative _).comp v (deficit_lower_derivative v hv)
  have hr := (gamma_survival_derivative _).comp v (deficit_upper_derivative v hv)
  have he : gammaDeficitCDF =ᶠ[𝓝 v]
      (fun w => gammaSurvival (deficitLowerRoot w)-gammaSurvival (deficitUpperRoot w)) := by
    filter_upwards [Ioi_mem_nhds hv] with w hw
    exact gamma_deficit_cdf_real w hw.le
  apply HasDerivAt.congr_of_eventuallyEq _ he
  convert hl.sub hr using 1
  rw [intrinsic_real_density_value _ hpa,intrinsic_real_density_value _ hp,hIa,hIb]
  unfold gammaDeficitDensity
  rw [show 1-deficitLowerRoot v = -(deficitLowerRoot v-1) by ring,div_neg]
  ring

end
end Sigma
