import SigmaProbGammaProcessArray
import Mathlib.Logic.Encodable.Basic

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators

/-- Duration of one interval at dyadic level `n`. -/
def gammaDyadicDuration (n : ℕ) : ℝ≥0 := 1 / 2^n

theorem gamma_dyadic_duration_pos (n : ℕ) : 0 < gammaDyadicDuration n := by
  unfold gammaDyadicDuration
  positivity

theorem gamma_dyadic_duration_succ (n : ℕ) :
    gammaDyadicDuration (n+1) = gammaDyadicDuration n/2 := by
  simp [gammaDyadicDuration, pow_succ, div_mul_eq_div_div]

/-- Row zero contains independent unit totals; row `n+1` contains the splitting
variables used to refine level `n`. -/
def gammaDyadicInputLaw (beta : ℕ → Measure ℝ) (i : ℕ × ℕ) : Measure ℝ :=
  match i.1 with
  | 0 => gammaCompletion 1
  | n+1 => beta n

instance gamma_dyadic_input_probability (beta : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (beta n)] (i : ℕ × ℕ) :
    IsProbabilityMeasure (gammaDyadicInputLaw beta i) := by
  cases i with | mk n k => cases n <;> dsimp only [gammaDyadicInputLaw] <;> infer_instance

def gammaDyadicInputs (beta : ℕ → Measure ℝ) : (ℕ × ℕ) → PoissonClockSpace → ℝ :=
  gammaProcessEmbeddedSamples (gammaDyadicInputLaw beta) ⟨Encodable.encode, Encodable.encode_injective⟩

theorem gamma_dyadic_inputs_measurable (beta : ℕ → Measure ℝ) (i : ℕ × ℕ) :
    Measurable (gammaDyadicInputs beta i) := gamma_process_embedded_samples_measurable _ _ _

theorem gamma_dyadic_inputs_independent (beta : ℕ → Measure ℝ) :
    iIndepFun (fun _ => inferInstance) (gammaDyadicInputs beta) poissonClockProbability :=
  gamma_process_embedded_samples_independent _ _

theorem gamma_dyadic_inputs_law (beta : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (beta n)]
    (i : ℕ × ℕ) : poissonClockProbability.map (gammaDyadicInputs beta i) = gammaDyadicInputLaw beta i :=
  gamma_process_embedded_samples_law _ _ _

/-- Actual dyadic increments, obtained by repeated multiplicative splitting. -/
def gammaDyadicIncrement {Ω : Type*} (raw : (ℕ × ℕ) → Ω → ℝ) : ℕ → ℕ → Ω → ℝ
  | 0, k, ω => raw (0,k) ω
  | n+1, k, ω => gammaDyadicIncrement raw n (k/2) ω *
      if k%2=0 then raw (n+1,k/2) ω else 1-raw (n+1,k/2) ω

def gammaDyadicGrid {Ω : Type*} (raw : (ℕ × ℕ) → Ω → ℝ) (n k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range k, gammaDyadicIncrement raw n i ω

theorem gamma_dyadic_increment_measurable {Ω : Type*} [MeasurableSpace Ω]
    (raw : (ℕ × ℕ) → Ω → ℝ) (hraw : ∀ i, Measurable (raw i)) (n k : ℕ) :
    Measurable (gammaDyadicIncrement raw n k) := by
  induction n generalizing k with
  | zero => exact hraw (0,k)
  | succ n ih =>
    change Measurable (fun ω => gammaDyadicIncrement raw n (k/2) ω *
      if k%2=0 then raw (n+1,k/2) ω else 1-raw (n+1,k/2) ω)
    split_ifs
    · exact (ih _).mul (hraw _)
    · exact (ih _).mul (measurable_const.sub (hraw _))

theorem gamma_dyadic_grid_measurable {Ω : Type*} [MeasurableSpace Ω]
    (raw : (ℕ × ℕ) → Ω → ℝ) (hraw : ∀ i, Measurable (raw i)) (n k : ℕ) :
    Measurable (gammaDyadicGrid raw n k) :=
  Finset.measurable_sum _ fun i hi => gamma_dyadic_increment_measurable raw hraw n i

theorem gamma_dyadic_increment_even {Ω : Type*} (raw : (ℕ × ℕ) → Ω → ℝ) (n k : ℕ) (ω : Ω) :
    gammaDyadicIncrement raw (n+1) (2*k) ω =
      gammaDyadicIncrement raw n k ω * raw (n+1,k) ω := by
  simp [gammaDyadicIncrement, Nat.mul_div_right]

theorem gamma_dyadic_increment_odd {Ω : Type*} (raw : (ℕ × ℕ) → Ω → ℝ) (n k : ℕ) (ω : Ω) :
    gammaDyadicIncrement raw (n+1) (2*k+1) ω =
      gammaDyadicIncrement raw n k ω * (1-raw (n+1,k) ω) := by
  simp [gammaDyadicIncrement, Nat.add_div, Nat.mul_div_right,
    show (2*k+1)%2 ≠ 0 by omega]

theorem gamma_dyadic_increment_children_sum {Ω : Type*} (raw : (ℕ × ℕ) → Ω → ℝ)
    (n k : ℕ) (ω : Ω) :
    gammaDyadicIncrement raw (n+1) (2*k) ω + gammaDyadicIncrement raw (n+1) (2*k+1) ω =
      gammaDyadicIncrement raw n k ω := by
  rw [gamma_dyadic_increment_even, gamma_dyadic_increment_odd]
  ring

/-- Refinement preserves every old grid value pointwise, without exceptions. -/
theorem gamma_dyadic_grid_refine {Ω : Type*} (raw : (ℕ × ℕ) → Ω → ℝ) (n k : ℕ) (ω : Ω) :
    gammaDyadicGrid raw (n+1) (2*k) ω = gammaDyadicGrid raw n k ω := by
  induction k with
  | zero => simp [gammaDyadicGrid]
  | succ k ih =>
    rw [show 2*(k+1)=2*k+1+1 by omega]
    simp only [gammaDyadicGrid, Finset.sum_range_succ] at ih ⊢
    rw [ih, add_assoc, gamma_dyadic_increment_children_sum]

theorem gamma_dyadic_increment_nonnegative {Ω : Type*} (raw : (ℕ × ℕ) → Ω → ℝ) (ω : Ω)
    (hzero : ∀ k, 0 ≤ raw (0,k) ω)
    (hsplit : ∀ n k, raw (n+1,k) ω ∈ Icc (0 : ℝ) 1) (n k : ℕ) :
    0 ≤ gammaDyadicIncrement raw n k ω := by
  induction n generalizing k with
  | zero => exact hzero k
  | succ n ih =>
    simp only [gammaDyadicIncrement]
    apply mul_nonneg (ih _)
    split_ifs
    · exact (hsplit _ _).1
    · exact sub_nonneg.mpr (hsplit _ _).2

theorem gamma_dyadic_grid_monotone {Ω : Type*} (raw : (ℕ × ℕ) → Ω → ℝ) (ω : Ω)
    (hzero : ∀ k, 0 ≤ raw (0,k) ω)
    (hsplit : ∀ n k, raw (n+1,k) ω ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    Monotone (fun k => gammaDyadicGrid raw n k ω) := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [gammaDyadicGrid, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (gamma_dyadic_increment_nonnegative raw ω hzero hsplit n k)


/-- Repeated refinement embeds an old grid into any finer level. -/
theorem gamma_dyadic_grid_refine_iter {Ω : Type*} (raw : (ℕ × ℕ) → Ω → ℝ)
    (n m k : ℕ) (ω : Ω) : gammaDyadicGrid raw (n+m) (2^m*k) ω = gammaDyadicGrid raw n k ω := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_succ, pow_succ, show 2^m*2*k=2*(2^m*k) by ring,
      gamma_dyadic_grid_refine, ih]

def gammaDyadicTime (p : ℕ × ℕ) : ℝ≥0 := p.2 / 2^p.1

/-- Consistency and nonnegative increments give monotonicity across every pair
of dyadic grids, not only within a fixed discretization. -/
theorem gamma_dyadic_grid_time_monotone {Ω : Type*} (raw : (ℕ × ℕ) → Ω → ℝ) (ω : Ω)
    (hzero : ∀ k, 0 ≤ raw (0,k) ω)
    (hsplit : ∀ n k, raw (n+1,k) ω ∈ Icc (0 : ℝ) 1)
    (p q : ℕ × ℕ) (hpq : gammaDyadicTime p ≤ gammaDyadicTime q) :
    gammaDyadicGrid raw p.1 p.2 ω ≤ gammaDyadicGrid raw q.1 q.2 ω := by
  have hh : (p.2 : ℝ≥0)*2^q.1 ≤ (q.2 : ℝ≥0)*2^p.1 :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mp hpq
  have hn : 2^q.1*p.2 ≤ 2^p.1*q.2 := by
    exact_mod_cast (show (2:ℝ≥0)^q.1*p.2 ≤ 2^p.1*q.2 by simpa only [mul_comm] using hh)
  rw [← gamma_dyadic_grid_refine_iter raw p.1 q.1 p.2 ω,
    ← gamma_dyadic_grid_refine_iter raw q.1 p.1 q.2 ω, Nat.add_comm q.1 p.1]
  exact gamma_dyadic_grid_monotone raw ω hzero hsplit _ hn

end
end Sigma
