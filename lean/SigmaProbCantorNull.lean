import Mathlib.Topology.Instances.CantorSet
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Sigma
open MeasureTheory Set Filter
open scoped Topology ENNReal

theorem volume_cantor_left_image (s : Set ℝ) :
    volume ((fun x : ℝ => x/3) '' s) = ENNReal.ofReal (1/3 : ℝ) * volume s := by
  have he : (fun x : ℝ => x/3) '' s = (fun x : ℝ => 3*x) ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change 3*(y/3) ∈ s
      convert hy using 1
      ring
    · intro hx
      exact ⟨3*x,hx,by ring⟩
  rw [he,Real.volume_preimage_mul_left (by norm_num)]
  rw [abs_of_pos (by norm_num : (0:ℝ)<3⁻¹)]
  simp only [one_div]

theorem volume_cantor_right_image (s : Set ℝ) :
    volume ((fun x : ℝ => (2+x)/3) '' s) = ENNReal.ofReal (1/3 : ℝ) * volume s := by
  have he : (fun x : ℝ => (2+x)/3) '' s =
      (fun x : ℝ => x/3) '' ((fun x : ℝ => 2+x) '' s) := by
    rw [image_image]
  rw [he, volume_cantor_left_image]
  have ha : (fun x : ℝ => 2+x) '' s = (fun x : ℝ => -2+x) ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa using hy
    · intro hx
      exact ⟨-2+x,hx,by ring⟩
  rw [ha,measure_preimage_add]

theorem volume_preCantorSet_le (n : ℕ) :
    volume (preCantorSet n) ≤ ENNReal.ofReal ((2/3 : ℝ)^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [preCantorSet_succ]
    apply (measure_union_le _ _).trans
    rw [volume_cantor_left_image,volume_cantor_right_image]
    calc
      _ ≤ ENNReal.ofReal (1/3 : ℝ) * ENNReal.ofReal ((2/3 : ℝ)^n) +
          ENNReal.ofReal (1/3 : ℝ) * ENNReal.ofReal ((2/3 : ℝ)^n) :=
        add_le_add (mul_le_mul_left' ih _) (mul_le_mul_left' ih _)
      _ = ENNReal.ofReal ((2/3 : ℝ)^(n+1)) := by
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [pow_succ]
        ring

/-- The native middle-thirds Cantor set has zero Lebesgue measure. -/
theorem volume_cantorSet_zero : volume cantorSet = 0 := by
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal ((2/3 : ℝ)^n)) atTop (𝓝 0) := by
    simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2/3) (by norm_num))
  apply le_antisymm _ (zero_le _)
  exact ge_of_tendsto ht (Eventually.of_forall fun n =>
    (measure_mono (iInter_subset (fun n => preCantorSet n) n)).trans (volume_preCantorSet_le n))

end Sigma
