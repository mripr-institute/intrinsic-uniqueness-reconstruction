import SigmaAutomorphisms
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Sigma
noncomputable section
open Set
open Filter MeasureTheory
open scoped Topology Pointwise

/-- Logarithmic coordinates transport the actual group law to addition. -/
def conjugateStarHom (φ : ℝ → ℝ)
    (hD : ∀ x > -1, -1 < φ x)
    (hh : ∀ x > -1, ∀ y > -1, φ (star x y)=star (φ x) (φ y)) : ℝ →+ ℝ where
  toFun u := Real.log (1+φ (Real.exp u-1))
  map_zero' := by
    have hz := hh 0 (by norm_num) 0 (by norm_num)
    have hp := hD 0 (by norm_num)
    have he : φ 0=0 := by
      simp only [star, SigmaBase.star, add_zero, mul_zero, zero_add] at hz
      nlinarith
    simp [he]
  map_add' u v := by
    have hu : -1 < Real.exp u-1 := by linarith [Real.exp_pos u]
    have hv : -1 < Real.exp v-1 := by linarith [Real.exp_pos v]
    have he : Real.exp (u+v)-1=star (Real.exp u-1) (Real.exp v-1) := by
      rw [Real.exp_add]
      unfold star SigmaBase.star
      ring
    change Real.log (1+φ (Real.exp (u+v)-1)) =
      Real.log (1+φ (Real.exp u-1))+Real.log (1+φ (Real.exp v-1))
    rw [he, hh _ hu _ hv]
    exact SigmaBase.log_star (hD _ hu) (hD _ hv)

theorem group_endomorphism_conjugate_classification (φ : ℝ → ℝ)
    (hD : ∀ x > -1, -1 < φ x)
    (hh : ∀ x > -1, ∀ y > -1, φ (star x y)=star (φ x) (φ y))
    (hc : Continuous (conjugateStarHom φ hD hh)) :
    ∃ c : ℝ, ∀ x > -1, φ x=groupPower c x := by
  let A := conjugateStarHom φ hD hh
  refine ⟨A 1, ?_⟩
  intro x hx
  have he := map_real_smul A hc (Real.log (1+x)) (1 : ℝ)
  simp only [smul_eq_mul, mul_one] at he
  change Real.log (1+φ (Real.exp (Real.log (1+x))-1)) = _ at he
  rw [Real.exp_log (by linarith : 0 < 1+x)] at he
  have hhx : 1+x-1=x := by ring
  rw [hhx] at he
  have he' := congrArg Real.exp he
  rw [Real.exp_log (by linarith [hD x hx] : 0 < 1+φ x)] at he'
  unfold groupPower
  rw [mul_comm]
  linarith

theorem group_endomorphism_continuous_classification (φ : ℝ → ℝ)
    (hD : ∀ x > -1, -1 < φ x)
    (hh : ∀ x > -1, ∀ y > -1, φ (star x y)=star (φ x) (φ y))
    (hc : ContinuousOn φ (Ioi (-1))) :
    ∃ c : ℝ, ∀ x > -1, φ x=groupPower c x := by
  apply group_endomorphism_conjugate_classification φ hD hh
  have hmap : ∀ u : ℝ, Real.exp u-1 ∈ Ioi (-1 : ℝ) := by
    intro u
    change -1 < Real.exp u-1
    linarith [Real.exp_pos u]
  have hf : Continuous (fun u : ℝ => φ (Real.exp u-1)) :=
    hc.comp_continuous (Real.continuous_exp.sub continuous_const) hmap
  exact (continuous_const.add hf).log (fun u => by have := hD _ (hmap u); linarith)

theorem group_automorphism_continuous_classification (φ : ℝ → ℝ)
    (hD : ∀ x > -1, -1 < φ x)
    (hh : ∀ x > -1, ∀ y > -1, φ (star x y)=star (φ x) (φ y))
    (hc : ContinuousOn φ (Ioi (-1))) (hi : InjOn φ (Ioi (-1))) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ x > -1, φ x=groupPower c x := by
  obtain ⟨c,hc⟩ := group_endomorphism_continuous_classification φ hD hh hc
  refine ⟨c, ?_, hc⟩
  intro hz
  have he : φ 0=φ 1 := by rw [hc 0 (by norm_num), hc 1 (by norm_num), hz]; simp [groupPower]
  have := hi (by norm_num) (by norm_num) he
  norm_num at this

theorem conjugateStarHom_surjective (φ : ℝ → ℝ)
    (hD : ∀ x > -1, -1 < φ x)
    (hh : ∀ x > -1, ∀ y > -1, φ (star x y)=star (φ x) (φ y))
    (hs : SurjOn φ (Ioi (-1)) (Ioi (-1))) :
    Function.Surjective (conjugateStarHom φ hD hh) := by
  intro u
  obtain ⟨x,hx,he⟩ := hs (show Real.exp u-1 ∈ Ioi (-1 : ℝ) by
    change -1 < Real.exp u-1; linarith [Real.exp_pos u])
  refine ⟨Real.log (1+x), ?_⟩
  change Real.log (1+φ (Real.exp (Real.log (1+x))-1))=u
  rw [Real.exp_log (by linarith [mem_Ioi.mp hx] : 0 < 1+x)]
  simp only [add_sub_cancel_left, he]
  rw [show 1+(Real.exp u-1)=Real.exp u by ring, Real.log_exp]

theorem group_automorphism_monotone_classification (φ : ℝ → ℝ)
    (hD : ∀ x > -1, -1 < φ x)
    (hh : ∀ x > -1, ∀ y > -1, φ (star x y)=star (φ x) (φ y))
    (hs : SurjOn φ (Ioi (-1)) (Ioi (-1))) (hi : InjOn φ (Ioi (-1)))
    (hm : MonotoneOn φ (Ioi (-1)) ∨ AntitoneOn φ (Ioi (-1))) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ x > -1, φ x=groupPower c x := by
  have hmap (u : ℝ) : Real.exp u-1 ∈ Ioi (-1 : ℝ) := by
    change -1 < Real.exp u-1; linarith [Real.exp_pos u]
  have hA : Continuous (conjugateStarHom φ hD hh) := by
    rcases hm with hm | hm
    · apply Monotone.continuous_of_surjective _ (conjugateStarHom_surjective φ hD hh hs)
      intro u v huv
      change Real.log (1+φ (Real.exp u-1)) ≤ Real.log (1+φ (Real.exp v-1))
      exact Real.log_le_log (by linarith [hD _ (hmap u)])
        (add_le_add_left (hm (hmap u) (hmap v) (sub_le_sub_right (Real.exp_le_exp.mpr huv) 1)) 1)
    · have hm' : Monotone (fun u : ℝ => -conjugateStarHom φ hD hh u) := by
        intro u v huv
        apply neg_le_neg
        change Real.log (1+φ (Real.exp v-1)) ≤ Real.log (1+φ (Real.exp u-1))
        exact Real.log_le_log (by linarith [hD _ (hmap v)])
          (add_le_add_left (hm (hmap u) (hmap v) (sub_le_sub_right (Real.exp_le_exp.mpr huv) 1)) 1)
      have hs' : Function.Surjective (fun u : ℝ => -conjugateStarHom φ hD hh u) := by
        intro y
        obtain ⟨u,hu⟩ := conjugateStarHom_surjective φ hD hh hs (-y)
        exact ⟨u, by simp only [hu, neg_neg]⟩
      simpa only [neg_neg] using (hm'.continuous_of_surjective hs').neg
  obtain ⟨c,hc⟩ := group_endomorphism_conjugate_classification φ hD hh hA
  refine ⟨c, ?_, hc⟩
  intro hz
  have he : φ 0=φ 1 := by rw [hc 0 (by norm_num), hc 1 (by norm_num), hz]; simp [groupPower]
  have := hi (by norm_num) (by norm_num) he
  norm_num at this

theorem real_additive_measurable_continuous (A : ℝ →+ ℝ) (hm : Measurable A) :
    Continuous A := by
  let E : ℕ → Set ℝ := fun n => {x | |A x| ≤ n}
  have hE (n : ℕ) : MeasurableSet (E n) :=
    measurableSet_le (continuous_abs.measurable.comp hm) measurable_const
  have hcover : (⋃ n, E n)=univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    obtain ⟨n,hn⟩ := exists_nat_gt |A x|
    exact ⟨n, hn.le⟩
  obtain ⟨n,hn⟩ : ∃ n, 0 < volume (E n) := by
    by_contra h
    have hz : ∀ n, volume (E n)=0 := by
      intro n
      exact le_antisymm (le_of_not_gt (fun hn => h ⟨n,hn⟩)) (zero_le _)
    have hh := measure_iUnion_null hz
    rw [hcover] at hh
    simp at hh
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp
    (Measure.sub_mem_nhds_zero_of_addHaar_pos volume (E n) (hE n) hn)
  have hb (x : ℝ) (hx : |x| < δ) : |A x| ≤ 2*n := by
    have hx' : x ∈ E n-E n := hball (by simpa [Metric.mem_ball, Real.dist_eq] using hx)
    obtain ⟨u,hu,v,hv,rfl⟩ := mem_sub.mp hx'
    calc
      |A (u-v)| = |A u-A v| := by rw [map_sub]
      _ ≤ |A u|+|A v| := abs_sub _ _
      _ ≤ 2*n := by change |A u| ≤ (n:ℝ) at hu; change |A v| ≤ (n:ℝ) at hv; linarith
  apply continuous_of_continuousAt_zero A
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨k,hk⟩ := exists_nat_gt (2*(n:ℝ)/ε)
  have hk0 : 0 < (k:ℝ) := lt_of_le_of_lt (by positivity) hk
  refine ⟨δ/k, div_pos hδ hk0, ?_⟩
  intro x hx
  have hx' : |x| < δ/k := by simpa [Real.dist_eq] using hx
  have hxk : |(k:ℝ)*x| < δ := by
    rw [abs_mul, abs_of_pos hk0]
    nlinarith [(lt_div_iff₀ hk0).mp hx']
  have hh := hb ((k:ℝ)*x) hxk
  have he : A ((k:ℝ)*x)=(k:ℝ)*A x := by
    simpa only [nsmul_eq_mul] using map_nsmul A k x
  rw [he, abs_mul, abs_of_pos hk0] at hh
  have hkε := (div_lt_iff₀ hε).mp hk
  rw [map_zero, dist_zero_right, Real.norm_eq_abs]
  nlinarith

theorem group_automorphism_measurable_classification (φ : ℝ → ℝ)
    (hD : ∀ x > -1, -1 < φ x)
    (hh : ∀ x > -1, ∀ y > -1, φ (star x y)=star (φ x) (φ y))
    (hm : Measurable (fun x : Ioi (-1 : ℝ) => φ x))
    (hi : InjOn φ (Ioi (-1))) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ x > -1, φ x=groupPower c x := by
  have hmap (u : ℝ) : Real.exp u-1 ∈ Ioi (-1 : ℝ) := by
    change -1 < Real.exp u-1; linarith [Real.exp_pos u]
  have hf : Measurable (fun u : ℝ => φ (Real.exp u-1)) :=
    hm.comp (((Real.continuous_exp.sub continuous_const).subtype_mk hmap).measurable)
  have hA : Continuous (conjugateStarHom φ hD hh) :=
    real_additive_measurable_continuous _ (Real.measurable_log.comp (measurable_const.add hf))
  obtain ⟨c,hc⟩ := group_endomorphism_conjugate_classification φ hD hh hA
  refine ⟨c, ?_, hc⟩
  intro hz
  have he : φ 0=φ 1 := by rw [hc 0 (by norm_num), hc 1 (by norm_num), hz]; simp [groupPower]
  have := hi (by norm_num) (by norm_num) he
  norm_num at this

end
end Sigma
