import SigmaProbCantorNull
import Mathlib.Probability.CDF
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.ENNReal.Real

namespace Sigma
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

theorem atomless_probability_cdf_continuous (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NoAtoms μ] : Continuous (cdf μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [(monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim, (cdf μ).rightLim_eq]
  have he := (cdf μ).measure_singleton x
  rw [measure_cdf, measure_singleton] at he
  have hle : cdf μ x ≤ Function.leftLim (cdf μ) x :=
    sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp he.symm)
  exact le_antisymm ((monotone_cdf μ).leftLim_le le_rfl) hle

def singularShiftedCDF (μ : Measure ℝ) (t : ℝ) : ℝ := cdf μ (t-1)

theorem singular_shifted_cdf_continuous (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NoAtoms μ] : Continuous (singularShiftedCDF μ) :=
  (atomless_probability_cdf_continuous μ).comp (continuous_id.sub continuous_const)

theorem singular_shifted_cdf_monotone (μ : Measure ℝ) : Monotone (singularShiftedCDF μ) :=
  (monotone_cdf μ).comp (fun _ _ h => sub_le_sub_right h 1)

theorem singular_shifted_cdf_bounds (μ : Measure ℝ) (t : ℝ) :
    0 ≤ singularShiftedCDF μ t ∧ singularShiftedCDF μ t ≤ 1 :=
  ⟨cdf_nonneg μ _,cdf_le_one μ _⟩

theorem singular_shifted_cdf_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]
    (hμ : μ cantorSetᶜ = 0) {t : ℝ} (ht : t ≤ 1) : singularShiftedCDF μ t = 0 := by
  rw [singularShiftedCDF,cdf_eq_toReal]
  have hi : μ (Iic (t-1)) = 0 := by
    apply measure_mono_null (t := cantorSetᶜ ∪ {0}) _
      (measure_union_null hμ (measure_singleton 0))
    intro x hx
    by_cases hc : x ∈ cantorSet
    · right
      have hb := cantorSet_subset_unitInterval hc
      simp only [mem_singleton_iff]
      change x ≤ t-1 at hx
      linarith [hb.1]
    · exact Or.inl hc
  simp [hi]

theorem singular_shifted_cdf_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ cantorSetᶜ = 0) {t : ℝ} (ht : 2 ≤ t) : singularShiftedCDF μ t = 1 := by
  rw [singularShiftedCDF,cdf_eq_toReal]
  have hi : μ (Iic (t-1)) = 1 := by
    have hae : ∀ᵐ x ∂μ, x ∈ cantorSet := by simpa only [ae_iff] using hμ
    have hs : ∀ᵐ x ∂μ, x ∈ Iic (t-1) := by
      filter_upwards [hae] with x hx
      have hb := cantorSet_subset_unitInterval hx
      change x ≤ t-1
      linarith [hb.2]
    calc
      _ = μ univ := measure_congr (by
        filter_upwards [hs] with x hx
        exact propext ⟨fun _ => mem_univ x,fun _ => hx⟩)
      _ = 1 := measure_univ
  simp [hi]

theorem probability_cdf_locally_constant_off_closed_support (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (S : Set ℝ) (hS : IsClosed S)
    (hμ : μ Sᶜ = 0) {x : ℝ} (hx : x ∉ S) :
    ∀ᶠ y in 𝓝 x, cdf μ y = cdf μ x := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hS.isOpen_compl x hx
  filter_upwards [Metric.ball_mem_nhds x hε] with y hy
  simp only [cdf_eq_toReal]
  congr 1
  apply measure_congr
  have hae : ∀ᵐ t ∂μ, t ∈ S := by simpa only [ae_iff] using hμ
  filter_upwards [hae] with t ht
  have hy' : |y-x| < ε := by simpa [Metric.mem_ball,Real.dist_eq] using hy
  have hfar : ε ≤ |t-x| := by
    by_contra hh
    have hm : t ∈ Metric.ball x ε := by
      simpa [Metric.mem_ball,Real.dist_eq] using lt_of_not_ge hh
    exact hball hm ht
  have htcase : t ≤ x-ε ∨ x+ε ≤ t := by
    rcases le_or_gt t x with hh | hh
    · left
      rw [abs_of_nonpos (sub_nonpos.mpr hh)] at hfar
      linarith
    · right
      rw [abs_of_nonneg (sub_nonneg.mpr hh.le)] at hfar
      linarith
  change (t ≤ y) = (t ≤ x)
  apply propext
  rcases htcase with hh | hh
  · constructor <;> intro _ <;> linarith [(abs_lt.mp hy').1]
  · constructor <;> intro hh' <;> linarith [(abs_lt.mp hy').2]

theorem singular_shifted_cdf_hasDerivAt_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ cantorSetᶜ = 0) {t : ℝ} (ht : t-1 ∉ cantorSet) :
    HasDerivAt (singularShiftedCDF μ) 0 t := by
  have he := probability_cdf_locally_constant_off_closed_support μ cantorSet isClosed_cantorSet hμ ht
  have hc : HasDerivAt (cdf μ) 0 (t-1) :=
    (hasDerivAt_const (t-1) (cdf μ (t-1))).congr_of_eventuallyEq he
  simpa only [zero_mul,singularShiftedCDF] using hc.comp t ((hasDerivAt_id t).sub_const 1)

theorem singular_shifted_cdf_derivative_zero_ae (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ cantorSetᶜ = 0) :
    ∀ᵐ t : ℝ, HasDerivAt (singularShiftedCDF μ) 0 t := by
  have hn : volume ((fun t : ℝ => t-1) ⁻¹' cantorSet) = 0 := by
    simpa only [sub_eq_add_neg,measure_preimage_add_right] using volume_cantorSet_zero
  have hae : ∀ᵐ t : ℝ, t-1 ∉ cantorSet := by
    simpa only [ae_iff,not_not,mem_preimage,Set.setOf_mem_eq] using hn
  filter_upwards [hae] with t ht
  exact singular_shifted_cdf_hasDerivAt_zero μ hμ ht

end
end Sigma
