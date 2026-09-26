import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Field

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology BigOperators

def determinantSummabilityPower (regularized : Bool) : ℕ := if regularized then 2 else 1

def determinantFactor (regularized : Bool) (w : ℂ) : ℂ :=
  if regularized then (1+w)*Complex.exp (-w) else 1+w

def determinantLog (regularized : Bool) (w : ℂ) : ℂ :=
  if regularized then Complex.log (1+w)-w else Complex.log (1+w)

theorem determinant_factor_eq_zero (regularized : Bool) (w : ℂ) :
    determinantFactor regularized w = 0 ↔ 1+w = 0 := by
  cases regularized <;> simp [determinantFactor, Complex.exp_ne_zero]

theorem determinant_log_exp (regularized : Bool) (w : ℂ) (hw : 1+w ≠ 0) :
    Complex.exp (determinantLog regularized w) = determinantFactor regularized w := by
  cases regularized <;> simp [determinantLog, determinantFactor, Complex.exp_sub,
    Complex.exp_log hw, Complex.exp_neg, div_eq_mul_inv]

theorem determinant_log_norm_bound (regularized : Bool) (w : ℂ) (hw : ‖w‖ ≤ 1/2) :
    ‖determinantLog regularized w‖ ≤ 2*‖w‖^(determinantSummabilityPower regularized) := by
  cases regularized
  · simp only [determinantLog, determinantSummabilityPower, Bool.false_eq_true,
      if_false, pow_one]
    exact (Complex.norm_log_one_add_half_le_self hw).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg w))
  · simp only [determinantLog, determinantSummabilityPower, if_true]
    have hh := Complex.norm_log_one_add_sub_self_le (lt_of_le_of_lt hw (by norm_num : (1/2 : ℝ)<1))
    have hi : (1-‖w‖)⁻¹ ≤ 2 := by
      apply (inv_le_comm₀ (by linarith) (by norm_num)).mpr
      simpa only [one_div] using (show (1/2 : ℝ) ≤ 1-‖w‖ by linarith)
    calc
      _ ≤ ‖w‖^2*(1-‖w‖)⁻¹/2 := hh
      _ ≤ ‖w‖^2*2/2 := by gcongr
      _ ≤ 2*‖w‖^2 := by nlinarith [sq_nonneg ‖w‖]

variable {ι : Type*}

theorem determinant_coefficients_tendsto_zero (regularized : Bool) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖^(determinantSummabilityPower regularized))) :
    Tendsto c cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  cases regularized
  · simpa [determinantSummabilityPower] using hc.tendsto_cofinite_zero
  · have h := Real.continuous_sqrt.tendsto (0 : ℝ) |>.comp hc.tendsto_cofinite_zero
    simpa only [determinantSummabilityPower, Function.comp_def, if_true, Real.sqrt_sq_eq_abs,
      abs_norm, Real.sqrt_zero] using h

theorem determinant_logs_summable (regularized : Bool) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖^(determinantSummabilityPower regularized))) (z : ℂ) :
    Summable (fun i => determinantLog regularized (z*c i)) := by
  have ht := (determinant_coefficients_tendsto_zero regularized c hc).const_mul z
  have hb : ∀ᶠ i in cofinite, ‖z*c i‖ ≤ (1/2 : ℝ) := by
    have hh : Tendsto (fun i => ‖z*c i‖) cofinite (𝓝 0) := by simpa using ht.norm
    exact (hh.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))).mono (fun _ h => h.le)
  apply Summable.of_norm_bounded_eventually
    (fun i => (2*‖z‖^(determinantSummabilityPower regularized))*
      ‖c i‖^(determinantSummabilityPower regularized)) (hc.mul_left _) 
  filter_upwards [hb] with i hi
  simpa only [norm_mul, mul_pow, mul_assoc] using determinant_log_norm_bound regularized (z*c i) hi

private theorem determinant_factors_hasProd_zero (regularized : Bool) (c : ι → ℂ)
    (z : ℂ) (i : ι) (hi : 1+z*c i = 0) :
    HasProd (fun j => determinantFactor regularized (z*c j)) 0 := by
  classical
  change Tendsto (fun s : Finset ι => ∏ j ∈ s, determinantFactor regularized (z*c j)) atTop (𝓝 0)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop ({i} : Finset ι)] with s hs
  symm
  apply Finset.prod_eq_zero (hs (Finset.mem_singleton_self i))
  exact (determinant_factor_eq_zero regularized _).mpr hi

theorem determinant_factors_hasProd_exp (regularized : Bool) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖^(determinantSummabilityPower regularized)))
    (z : ℂ) (hz : ∀ i, 1+z*c i ≠ 0) :
    HasProd (fun i => determinantFactor regularized (z*c i))
      (Complex.exp (∑' i, determinantLog regularized (z*c i))) := by
  have h := Complex.continuous_exp.tendsto _ |>.comp
    (determinant_logs_summable regularized c hc z).hasSum
  change Tendsto (fun s : Finset ι => Complex.exp (∑ i ∈ s, determinantLog regularized (z*c i)))
    atTop _ at h
  simpa only [Complex.exp_sum, determinant_log_exp regularized _ (hz _)] using h

/-- Absolute spectral summability gives an unordered product, including at its zeros. -/
theorem determinant_factors_multipliable (regularized : Bool) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖^(determinantSummabilityPower regularized))) (z : ℂ) :
    Multipliable (fun i => determinantFactor regularized (z*c i)) := by
  by_cases hz : ∀ i, 1+z*c i ≠ 0
  · exact (determinant_factors_hasProd_exp regularized c hc z hz).multipliable
  · push_neg at hz
    obtain ⟨i, hi⟩ := hz
    exact (determinant_factors_hasProd_zero regularized c z i hi).multipliable

def spectralDeterminant (regularized : Bool) (c : ι → ℂ) (z : ℂ) : ℂ :=
  ∏' i, determinantFactor regularized (z*c i)

theorem spectral_determinant_eq_zero_iff (regularized : Bool) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖^(determinantSummabilityPower regularized))) (z : ℂ) :
    spectralDeterminant regularized c z = 0 ↔ ∃ i, 1+z*c i = 0 := by
  constructor
  · intro hz
    by_contra h
    push_neg at h
    rw [spectralDeterminant, (determinant_factors_hasProd_exp regularized c hc z h).tprod_eq] at hz
    exact Complex.exp_ne_zero _ hz
  · rintro ⟨i, hi⟩
    exact (determinant_factors_hasProd_zero regularized c z i hi).tprod_eq

/-- Relabeling the complete spectrum does not change either determinant convention. -/
theorem spectral_determinant_reindex {κ : Type*} (regularized : Bool) (c : ι → ℂ)
    (e : κ ≃ ι) (z : ℂ) : spectralDeterminant regularized (c ∘ e) z =
      spectralDeterminant regularized c z := by
  exact e.tprod_eq (fun i => determinantFactor regularized (z*c i))

end
end Sigma
