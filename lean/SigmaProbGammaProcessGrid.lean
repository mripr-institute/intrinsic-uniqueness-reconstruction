import SigmaProbGammaProcessLevels
import SigmaProbGammaBeta

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

def gammaDyadicBeta (n : ℕ) : Measure ℝ := gammaProcessBetaProbability (gammaDyadicDuration n)
instance gamma_dyadic_beta_probability (n : ℕ) : IsProbabilityMeasure (gammaDyadicBeta n) :=
  gammaProcessBetaProbability_probability _

abbrev gammaDyadicRaw := gammaDyadicInputs gammaDyadicBeta

def gammaDyadicProcessGrid (p : ℕ × ℕ) : PoissonClockSpace → ℝ :=
  gammaDyadicGrid gammaDyadicRaw p.1 p.2

theorem gamma_dyadic_process_grid_measurable (p : ℕ × ℕ) : Measurable (gammaDyadicProcessGrid p) :=
  gamma_dyadic_grid_measurable _ (gamma_dyadic_inputs_measurable _) _ _

theorem gamma_dyadic_process_increments_independent (n : ℕ) :
    iIndepFun (fun _ => inferInstance) (gammaDyadicIncrement gammaDyadicRaw n) poissonClockProbability :=
  gamma_dyadic_level_independent gammaDyadicBeta (fun n => gamma_process_beta_split_law _) n

theorem gamma_dyadic_process_increment_law (n k : ℕ) :
    poissonClockProbability.map (gammaDyadicIncrement gammaDyadicRaw n k) =
      gammaCompletion (gammaDyadicDuration n) :=
  gamma_dyadic_increment_law gammaDyadicBeta (fun n => gamma_process_beta_split_law _) n k

theorem gamma_dyadic_process_grid_law (p : ℕ × ℕ) :
    poissonClockProbability.map (gammaDyadicProcessGrid p) = gammaCompletion (gammaDyadicTime p) := by
  have h := gamma_process_finset_sum_law poissonClockProbability
    (gammaDyadicIncrement gammaDyadicRaw p.1)
    (gamma_dyadic_increment_measurable _ (gamma_dyadic_inputs_measurable _) p.1)
    (gamma_dyadic_process_increments_independent p.1)
    (fun _ => gammaDyadicDuration p.1) (gamma_dyadic_process_increment_law p.1)
    (Finset.range p.2)
  simpa [gammaDyadicProcessGrid, gammaDyadicGrid, gammaDyadicDuration, gammaDyadicTime,
    nsmul_eq_mul, mul_div_assoc] using h

/-- Index of a dyadic time on a finer common level. -/
def gammaDyadicRescale (N : ℕ) (p : ℕ × ℕ) : ℕ := 2^(N-p.1)*p.2

theorem gamma_dyadic_rescale_grid (N : ℕ) (p : ℕ × ℕ) (hp : p.1 ≤ N) (ω : PoissonClockSpace) :
    gammaDyadicGrid gammaDyadicRaw N (gammaDyadicRescale N p) ω = gammaDyadicProcessGrid p ω := by
  simpa [gammaDyadicRescale, gammaDyadicProcessGrid, Nat.add_sub_of_le hp] using
    gamma_dyadic_grid_refine_iter gammaDyadicRaw p.1 (N-p.1) p.2 ω

theorem gamma_dyadic_rescale_time (N : ℕ) (p : ℕ × ℕ) (hp : p.1 ≤ N) :
    gammaDyadicTime (N,gammaDyadicRescale N p) = gammaDyadicTime p := by
  have hpow : (2 : ℝ≥0)^N = 2^(N-p.1)*2^p.1 := by
    rw [← pow_add, Nat.sub_add_cancel hp]
  simp only [gammaDyadicTime, gammaDyadicRescale, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [hpow, mul_div_mul_left _ _ (by positivity)]

theorem gamma_dyadic_rescale_mono (N : ℕ) (p q : ℕ × ℕ) (hp : p.1 ≤ N) (hq : q.1 ≤ N)
    (h : gammaDyadicTime p ≤ gammaDyadicTime q) : gammaDyadicRescale N p ≤ gammaDyadicRescale N q := by
  rw [← gamma_dyadic_rescale_time N p hp, ← gamma_dyadic_rescale_time N q hq] at h
  have hh := (div_le_div_iff_of_pos_right (show (0 : ℝ≥0)<2^N by positivity)).mp h
  exact_mod_cast hh

theorem gamma_dyadic_grid_sub (n a b : ℕ) (hab : a ≤ b) (ω : PoissonClockSpace) :
    gammaDyadicGrid gammaDyadicRaw n b ω-gammaDyadicGrid gammaDyadicRaw n a ω =
      ∑ k ∈ Finset.Ico a b, gammaDyadicIncrement gammaDyadicRaw n k ω := by
  exact (Finset.sum_Ico_eq_sub _ hab).symm

theorem gamma_dyadic_process_grid_increment_law (p q : ℕ × ℕ)
    (hpq : gammaDyadicTime p ≤ gammaDyadicTime q) :
    poissonClockProbability.map (fun ω => gammaDyadicProcessGrid q ω-gammaDyadicProcessGrid p ω) =
      gammaCompletion (gammaDyadicTime q-gammaDyadicTime p) := by
  let N := max p.1 q.1
  have hp : p.1 ≤ N := le_max_left _ _
  have hq : q.1 ≤ N := le_max_right _ _
  have hab := gamma_dyadic_rescale_mono N p q hp hq hpq
  have he : (fun ω => gammaDyadicProcessGrid q ω-gammaDyadicProcessGrid p ω) =
      (fun ω => ∑ k ∈ Finset.Ico (gammaDyadicRescale N p) (gammaDyadicRescale N q),
        gammaDyadicIncrement gammaDyadicRaw N k ω) := by
    funext ω
    rw [← gamma_dyadic_rescale_grid N p hp, ← gamma_dyadic_rescale_grid N q hq]
    exact gamma_dyadic_grid_sub _ _ _ hab ω
  rw [he, gamma_process_finset_sum_law poissonClockProbability
    (gammaDyadicIncrement gammaDyadicRaw N)
    (gamma_dyadic_increment_measurable _ (gamma_dyadic_inputs_measurable _) N)
    (gamma_dyadic_process_increments_independent N) (fun _ => gammaDyadicDuration N)
    (gamma_dyadic_process_increment_law N)]
  congr 1
  rw [← gamma_dyadic_rescale_time N p hp, ← gamma_dyadic_rescale_time N q hq]
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, gammaDyadicDuration, gammaDyadicTime]
  rw [Nat.cast_tsub, mul_one_div, tsub_div]

end
end Sigma
