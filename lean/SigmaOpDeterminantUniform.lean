import SigmaOpDeterminantProductAnalytic
import Mathlib.Analysis.NormedSpace.FunctionSeries

namespace Sigma
noncomputable section
open Filter Set Metric
open scoped Topology BigOperators
variable {ι β : Type*}

/-- Uniform convergence is preserved by complex exponentiation on bounded ranges. -/
theorem determinant_uniform_exp {F : ι → β → ℂ} {f : β → ℂ}
    {l : Filter ι} {s : Set β} (h : TendstoUniformlyOn F f l s)
    (M : ℝ) (hM : ∀ i x, x ∈ s → ‖F i x‖ ≤ M) (hm : ∀ x ∈ s, ‖f x‖ ≤ M) :
    TendstoUniformlyOn (fun i x => Complex.exp (F i x)) (fun x => Complex.exp (f x)) l s := by
  have hu := (isCompact_closedBall (0 : ℂ) M).uniformContinuousOn_of_continuous
    Complex.continuous_exp.continuousOn
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h δ hδ] with i hi x hx
  exact hbound (f x) (by simpa using hm x hx) (F i x) (by simpa using hM i x hx) (hi x hx)

def determinantTailLogTerm (reg : Bool) (c : ι → ℂ) (S : Finset ι) (i : ι) (z : ℂ) : ℂ := by
  classical
  exact if i ∈ S then 0 else determinantLog reg (z*c i)

theorem determinant_tail_log_uniform_bound (reg : Bool) (c : ι → ℂ)
    (S : Finset ι) (R : ℝ) (hS : ∀ i ∉ S, R*‖c i‖ ≤ 1/2)
    (i : ι) (z : ℂ) (hz : z ∈ closedBall 0 R) :
    ‖determinantTailLogTerm reg c S i z‖ ≤
      2*R^(determinantSummabilityPower reg)*‖c i‖^(determinantSummabilityPower reg) := by
  classical
  have hz' : ‖z‖ ≤ R := by simpa using hz
  have hR : 0 ≤ R := (norm_nonneg z).trans hz'
  unfold determinantTailLogTerm
  split_ifs with hi
  · simp only [norm_zero]
    positivity
  · have hh : ‖z*c i‖ ≤ 1/2 := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right hz' (norm_nonneg _)).trans (hS i hi)
    calc
      _ ≤ 2*‖z*c i‖^(determinantSummabilityPower reg) := determinant_log_norm_bound reg _ hh
      _ ≤ 2*(R*‖c i‖)^(determinantSummabilityPower reg) := by rw [norm_mul]; gcongr
      _ = _ := by rw [mul_pow]; ring

/-- The logarithmic tails converge uniformly on every closed disk, with an
explicit summable majorant for both the ordinary and regularized conventions. -/
theorem determinant_tail_log_uniform (reg : Bool) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖^(determinantSummabilityPower reg)))
    (S : Finset ι) (R : ℝ) (hS : ∀ i ∉ S, R*‖c i‖ ≤ 1/2) :
    TendstoUniformlyOn
      (fun F : Finset ι => fun z => ∑ i ∈ F, determinantTailLogTerm reg c S i z)
      (fun z => ∑' i, determinantTailLogTerm reg c S i z) atTop (closedBall 0 R) := by
  exact tendstoUniformlyOn_tsum (hc.mul_left (2*R^(determinantSummabilityPower reg)))
    (determinant_tail_log_uniform_bound reg c S R hS)

/-- Exponentiating the uniformly bounded log sums preserves uniform convergence. -/
theorem determinant_tail_exp_uniform (reg : Bool) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖^(determinantSummabilityPower reg)))
    (S : Finset ι) (R : ℝ) (hR : 0 ≤ R) (hS : ∀ i ∉ S, R*‖c i‖ ≤ 1/2) :
    TendstoUniformlyOn
      (fun F : Finset ι => fun z => Complex.exp (∑ i ∈ F, determinantTailLogTerm reg c S i z))
      (fun z => Complex.exp (∑' i, determinantTailLogTerm reg c S i z)) atTop (closedBall 0 R) := by
  let u := fun i => 2*R^(determinantSummabilityPower reg)*‖c i‖^(determinantSummabilityPower reg)
  have hu : Summable u := hc.mul_left _
  have hu0 (i : ι) : 0 ≤ u i := by dsimp [u]; positivity
  have hb := determinant_tail_log_uniform_bound reg c S R hS
  apply determinant_uniform_exp (determinant_tail_log_uniform reg c hc S R hS) (∑' i, u i)
  · intro F z hz
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i hi => hb i z hz).trans
      (sum_le_tsum F (fun i hi => hu0 i) hu))
  · intro z hz
    have hs := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hb i z hz) hu
    exact (norm_tsum_le_tsum_norm hs).trans (tsum_le_tsum (fun i => hb i z hz) hs hu)


theorem determinant_uniform_mul_left {F : ι → β → ℂ} {f a : β → ℂ}
    {l : Filter ι} {s : Set β} (h : TendstoUniformlyOn F f l s)
    (C : ℝ) (hC : 0 < C) (ha : ∀ x ∈ s, ‖a x‖ ≤ C) :
    TendstoUniformlyOn (fun i x => a x * F i x) (fun x => a x * f x) l s := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h (ε/C) (div_pos hε hC)] with i hi x hx
  rw [dist_eq_norm, ← mul_sub, norm_mul]
  calc
    _ ≤ C*‖f x-F i x‖ := mul_le_mul_of_nonneg_right (ha x hx) (norm_nonneg _)
    _ < C*(ε/C) := mul_lt_mul_of_pos_left (by simpa only [dist_eq_norm] using hi x hx) hC
    _ = ε := by field_simp

theorem determinant_tail_log_tsum (reg : Bool) (c : ι → ℂ) (S : Finset ι) (z : ℂ) :
    (∑' i, determinantTailLogTerm reg c S i z) = spectralDeterminantTailLog reg c S z := by
  classical
  change (∑' i, determinantTailLogTerm reg c S i z) =
    ∑' i : ({i | i ∉ S} : Set ι), determinantLog reg (z*c i)
  rw [tsum_subtype {i | i ∉ S} (fun i => determinantLog reg (z*c i))]
  apply tsum_congr
  intro i
  by_cases hi : i ∈ S <;> simp [determinantTailLogTerm, Set.indicator, hi]

theorem determinant_finite_tail_exp (reg : Bool) (c : ι → ℂ) (S F : Finset ι)
    (hSF : S ⊆ F) (z : ℂ) (hS : ∀ i ∉ S, ‖z*c i‖ < 1) :
    (∏ i ∈ F, determinantFactor reg (z*c i)) =
      (∏ i ∈ S, determinantFactor reg (z*c i)) *
        Complex.exp (∑ i ∈ F, determinantTailLogTerm reg c S i z) := by
  classical
  have hsum : (∑ i ∈ F, determinantTailLogTerm reg c S i z) =
      ∑ i ∈ F \ S, determinantLog reg (z*c i) := by
    rw [← Finset.sum_sdiff hSF]
    have hz : (∑ i ∈ S, determinantTailLogTerm reg c S i z) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [determinantTailLogTerm, hi]
    rw [hz, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    simp [determinantTailLogTerm, (Finset.mem_sdiff.mp hi).2]
  rw [hsum, Complex.exp_sum]
  have he : (∏ i ∈ F \ S, Complex.exp (determinantLog reg (z*c i))) =
      ∏ i ∈ F \ S, determinantFactor reg (z*c i) := by
    apply Finset.prod_congr rfl
    intro i hi
    apply determinant_log_exp
    exact Complex.slitPlane_ne_zero
      (Complex.mem_slitPlane_of_norm_lt_one (hS i (Finset.mem_sdiff.mp hi).2))
  rw [he, mul_comm]
  exact (Finset.prod_sdiff hSF).symm

/-- The actual unordered finite spectral products converge uniformly on every
closed disk, including disks crossing zeros. -/
theorem spectral_determinant_uniform_closedBall (reg : Bool) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖^(determinantSummabilityPower reg))) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun F : Finset ι => fun z => ∏ i ∈ F, determinantFactor reg (z*c i))
      (spectralDeterminant reg c) atTop (closedBall 0 R) := by
  classical
  obtain ⟨S, hS⟩ := determinant_exists_finite_tail reg c hc R
  let a := fun z => ∏ i ∈ S, determinantFactor reg (z*c i)
  have ha : Continuous a := continuous_finset_prod _ fun i hi =>
    (determinant_factor_differentiable reg (c i)).continuous
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn ha.continuousOn
  have h := determinant_uniform_mul_left (a := a)
    (determinant_tail_exp_uniform reg c hc S R hR hS) (max C 1)
    (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    (fun z hz => (hC z hz).trans (le_max_left _ _))
  have hsmall (z : ℂ) (hz : z ∈ closedBall 0 R) (i : ι) (hi : i ∉ S) : ‖z*c i‖ < 1 := by
    have hz' : ‖z‖ ≤ R := by simpa using hz
    rw [norm_mul]
    exact lt_of_le_of_lt ((mul_le_mul_of_nonneg_right hz' (norm_nonneg _)).trans (hS i hi))
      (by norm_num)
  apply (h.congr_right ?_).congr
  · filter_upwards [eventually_ge_atTop S] with F hF z hz
    exact (determinant_finite_tail_exp reg c S F hF z (hsmall z hz)).symm
  · intro z hz
    change a z * Complex.exp (∑' i, determinantTailLogTerm reg c S i z) = _
    rw [determinant_tail_log_tsum]
    exact (spectral_determinant_finite_exp reg c hc S z (hsmall z hz)).symm

/-- Local uniform convergence of the finite-product net on the whole complex plane. -/
theorem spectral_determinant_locally_uniform (reg : Bool) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖^(determinantSummabilityPower reg))) :
    TendstoLocallyUniformly (fun F : Finset ι => fun z => ∏ i ∈ F, determinantFactor reg (z*c i))
      (spectralDeterminant reg c) atTop := by
  intro u hu z
  refine ⟨closedBall 0 (‖z‖+1), ?_,
    spectral_determinant_uniform_closedBall reg c hc (‖z‖+1) (by positivity) u hu⟩
  apply mem_of_superset (Metric.ball_mem_nhds z zero_lt_one)
  intro w hw
  have hh : ‖w‖ ≤ dist w z+‖z‖ := by simpa only [dist_eq_norm, add_comm] using norm_le_insert' w z
  rw [mem_closedBall, dist_zero_right]
  have hw' : dist w z < 1 := hw
  linarith

end
end Sigma
