import SigmaProbCompletionProcess

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

/-- The process obtained by reusing one Gamma variable at every time. -/
def gammaSingleVariableProcess (r : ℝ≥0) (T : ℝ) : ℝ := (r:ℝ)*T

theorem gamma_single_variable_measurable (r : ℝ≥0) :
    Measurable (gammaSingleVariableProcess r) := measurable_const.mul measurable_id

theorem gamma_single_variable_time_one :
    gammaProbability.map (gammaSingleVariableProcess 1) = gammaProbability := by
  have he : gammaSingleVariableProcess 1 = id := by funext T; simp [gammaSingleVariableProcess]
  rw [he, Measure.map_id]

theorem gamma_single_variable_zero (T : ℝ) : gammaSingleVariableProcess 0 T = 0 := by
  simp [gammaSingleVariableProcess]

theorem gamma_single_variable_nonnegative (r : ℝ≥0) :
    ∀ᵐ T ∂gammaProbability, 0 ≤ gammaSingleVariableProcess r T := by
  have hp : ∀ᵐ T ∂gammaProbability, 0 ≤ T := by
    rw [← gamma_completion_one]
    exact gamma_completion_nonnegative 1
  filter_upwards [hp] with T hT
  exact mul_nonneg r.coe_nonneg hT

theorem gamma_single_variable_stationary_increments (r s : ℝ≥0) :
    gammaProbability.map (fun T => gammaSingleVariableProcess (r+s) T-
      gammaSingleVariableProcess r T) =
      gammaProbability.map (gammaSingleVariableProcess s) := by
  congr 1
  funext T
  simp only [gammaSingleVariableProcess, NNReal.coe_add]
  ring

theorem gamma_coordinate_not_independent_of_itself :
    ¬IndepFun (fun T : ℝ => T) (fun T : ℝ => T) gammaProbability := by
  intro hi
  have hh := (indepFun_iff_map_prod_eq_prod_map_map
    measurable_id.aemeasurable measurable_id.aemeasurable).mp hi
  simp only [Measure.map_id] at hh
  have he := congrArg (fun ρ : Measure (ℝ×ℝ) => ∫ z, z.1*z.2 ∂ρ) hh
  dsimp only at he
  rw [integral_map (measurable_id.prod_mk measurable_id).aemeasurable
    (continuous_fst.mul continuous_snd).aestronglyMeasurable] at he
  rw [integral_prod_mul (fun x : ℝ => x) (fun x : ℝ => x), gamma_probability_mean] at he
  have hm : (∫ T : ℝ, T*T ∂gammaProbability) = 6 := by
    simpa only [← pow_two, Nat.factorial] using gamma_probability_moments 2
  change (∫ T : ℝ, T*T ∂gammaProbability) = 2*2 at he
  rw [hm] at he
  norm_num at he

/-- The unit increments are the same nonconstant Gamma variable, so the
time-one marginal and even stationarity do not supply independent increments. -/
theorem gamma_single_variable_dependent_unit_increments :
    ¬IndepFun (fun T => gammaSingleVariableProcess 1 T-gammaSingleVariableProcess 0 T)
      (fun T => gammaSingleVariableProcess 2 T-gammaSingleVariableProcess 1 T)
      gammaProbability := by
  have h0 : (fun T => gammaSingleVariableProcess 1 T-gammaSingleVariableProcess 0 T) =
      (fun T : ℝ => T) := by funext T; simp [gammaSingleVariableProcess]
  have h1 : (fun T => gammaSingleVariableProcess 2 T-gammaSingleVariableProcess 1 T) =
      (fun T : ℝ => T) := by funext T; norm_num [gammaSingleVariableProcess]; ring
  rw [h0,h1]
  exact gamma_coordinate_not_independent_of_itself

theorem gamma_single_variable_not_independent_increments :
    ¬HasIndependentNonnegativeTimeIncrements gammaProbability gammaSingleVariableProcess := by
  intro hi
  have hz : ∀ᵐ T ∂gammaProbability, gammaSingleVariableProcess 0 T = 0 :=
    ae_of_all _ gamma_single_variable_zero
  have hh := process_independent_present_future gammaProbability gammaSingleVariableProcess
    gamma_single_variable_measurable hz hi 1 1
  apply gamma_coordinate_not_independent_of_itself
  convert hh using 1
  · funext T
    simp [gammaSingleVariableProcess]
  · funext T
    norm_num [gammaSingleVariableProcess]
    ring

end
end Sigma
