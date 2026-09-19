import SigmaMatrixMetricBounds
import SigmaMatrixPiecewiseRankOne

namespace Sigma
noncomputable section
open scoped Matrix Topology ComplexOrder BigOperators
open MeasureTheory

variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

def matrixTangentSpeed (X U : Matrix n n ℝ) : ℝ :=
  Real.sqrt (precisionMetric X⁻¹ U U)

theorem matrix_tangent_speed_continuousOn
    (γ v : ℝ → Matrix n n ℝ) (a b : ℝ)
    (hc : ContinuousOn γ (Set.Icc a b)) (hv : ContinuousOn v (Set.Icc a b))
    (hp : ∀ s ∈ Set.Icc a b, (γ s).PosDef) :
    ContinuousOn (fun s => matrixTangentSpeed (γ s) (v s)) (Set.Icc a b) := by
  have hi : ContinuousOn (fun s => (γ s)⁻¹) (Set.Icc a b) := by
    intro s hs
    exact (matrix_inverse_hasFDerivAt (γ s)
      (isUnit_iff_ne_zero.mpr (ne_of_gt (hp s hs).det_pos))).continuousAt.comp_continuousWithinAt (hc s hs)
  exact (matrixTraceCLM.continuous.comp_continuousOn (((hi.mul hv).mul hi).mul hv)).sqrt

theorem matrix_segment_speed_integrable (γ v : ℝ → Matrix n n ℝ) (a b : ℝ)
    (hab : a ≤ b) (hc : ContinuousOn γ (Set.Icc a b))
    (hv : ContinuousOn v (Set.Icc a b)) (hp : ∀ s ∈ Set.Icc a b, (γ s).PosDef)
    (hd : ∀ s ∈ Set.Ioo a b, HasDerivAt γ (v s) s) :
    IntervalIntegrable (matrixHessianSpeed γ) volume a b := by
  have hi : IntervalIntegrable (fun s => matrixTangentSpeed (γ s) (v s)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact matrix_tangent_speed_continuousOn γ v a b hc hv hp
  apply hi.congr
  apply (ae_restrict_iff' measurableSet_uIoc).mpr
  have hn : ∀ᵐ s : ℝ ∂volume, s ≠ b := by simp [ae_iff]
  filter_upwards [hn] with s hne hs
  rw [Set.uIoc_of_le hab] at hs
  rw [matrixHessianSpeed, (hd s ⟨hs.1, lt_of_le_of_ne hs.2 hne⟩).deriv]
  rfl

theorem scalar_segment_length_bound (f w speed : ℝ → ℝ) (a b C : ℝ)
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (hw : IntervalIntegrable w volume a b)
    (hd : ∀ s ∈ Set.Ioo a b, HasDerivAt f (w s) s)
    (hi : IntervalIntegrable speed volume a b)
    (hb : ∀ s ∈ Set.Ioo a b, |w s| ≤ C * speed s) :
    |f b-f a| ≤ C * ∫ s : ℝ in a..b, speed s := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hf hd hw
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (f := w) (μ := volume) hab
  rw [hftc, Real.norm_eq_abs] at hnorm
  calc
    _ ≤ ∫ s : ℝ in a..b, |w s| := by simpa only [Real.norm_eq_abs] using hnorm
    _ ≤ ∫ s : ℝ in a..b, C * speed s := by
      apply intervalIntegral.integral_mono_ae_restrict hab (by simpa only [Real.norm_eq_abs] using hw.norm)
        (hi.const_mul C)
      apply (ae_restrict_iff' measurableSet_Icc).mpr
      have hn' : ∀ᵐ s : ℝ ∂volume, s ≠ a := by simp [ae_iff]
      have hn : ∀ᵐ s : ℝ ∂volume, s ≠ b := by simp [ae_iff]
      filter_upwards [hn', hn] with s hne' hne hs
      exact hb s ⟨lt_of_le_of_ne hs.1 hne'.symm, lt_of_le_of_ne hs.2 hne⟩
    _ = _ := intervalIntegral.integral_const_mul _ _

theorem matrix_segment_diagonal_log_bound (γ v : ℝ → Matrix n n ℝ) (a b : ℝ)
    (hab : a ≤ b) (hc : ContinuousOn γ (Set.Icc a b))
    (hv : ContinuousOn v (Set.Icc a b)) (hp : ∀ s ∈ Set.Icc a b, (γ s).PosDef)
    (hd : ∀ s ∈ Set.Ioo a b, HasDerivAt γ (v s) s) (i : n) :
    |Real.log (γ b i i)-Real.log (γ a i i)| ≤
      ∫ s : ℝ in a..b, matrixHessianSpeed γ s := by
  have hf := (matrixEntryCLM i i).continuous.comp_continuousOn hc
  have hwc : ContinuousOn (fun s => v s i i / γ s i i) (Set.Icc a b) :=
    ((matrixEntryCLM i i).continuous.comp_continuousOn hv).div hf
      (fun s hs => ne_of_gt (matrix_posDef_diagonal_entry (γ s) (hp s hs) i))
  have hw : IntervalIntegrable (fun s => v s i i / γ s i i) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  have hh := scalar_segment_length_bound (fun s => Real.log (γ s i i))
    (fun s => v s i i / γ s i i) (matrixHessianSpeed γ) a b 1 hab
    (hf.log fun s hs => ne_of_gt (matrix_posDef_diagonal_entry (γ s) (hp s hs) i)) hw
    (fun s hs => matrix_diagonal_log_path_hasDerivAt (hp s ⟨hs.1.le, hs.2.le⟩) (hd s hs) i)
    (matrix_segment_speed_integrable γ v a b hab hc hv hp hd) (by
      intro s hs
      rw [one_mul, matrixHessianSpeed, (hd s hs).deriv]
      exact matrix_diagonal_log_velocity_bound (γ s) (v s) (hp s ⟨hs.1.le, hs.2.le⟩)
        (matrix_spd_path_velocity_symmetric hp hs (hd s hs)) i)
  simpa only [one_mul] using hh

theorem matrix_segment_logdet_bound (γ v : ℝ → Matrix n n ℝ) (a b : ℝ)
    (hab : a ≤ b) (hc : ContinuousOn γ (Set.Icc a b))
    (hv : ContinuousOn v (Set.Icc a b)) (hp : ∀ s ∈ Set.Icc a b, (γ s).PosDef)
    (hd : ∀ s ∈ Set.Ioo a b, HasDerivAt γ (v s) s) :
    |Real.log (γ b).det-Real.log (γ a).det| ≤
      Real.sqrt (Fintype.card n : ℝ) * ∫ s : ℝ in a..b, matrixHessianSpeed γ s := by
  have hdet := matrix_det_differentiable.continuous.comp_continuousOn hc
  have hi : ContinuousOn (fun s => (γ s)⁻¹) (Set.Icc a b) := by
    intro s hs
    exact (matrix_inverse_hasFDerivAt (γ s)
      (isUnit_iff_ne_zero.mpr (ne_of_gt (hp s hs).det_pos))).continuousAt.comp_continuousWithinAt (hc s hs)
  have hw : IntervalIntegrable (fun s => Matrix.trace ((γ s)⁻¹*v s)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact matrixTraceCLM.continuous.comp_continuousOn (hi.mul hv)
  apply scalar_segment_length_bound (fun s => Real.log (γ s).det)
    (fun s => Matrix.trace ((γ s)⁻¹*v s)) (matrixHessianSpeed γ) a b _ hab
    (hdet.log fun s hs => ne_of_gt (hp s hs).det_pos) hw
    (fun s hs => matrix_logdet_path_hasDerivAt (hp s ⟨hs.1.le, hs.2.le⟩) (hd s hs))
    (matrix_segment_speed_integrable γ v a b hab hc hv hp hd)
  intro s hs
  rw [matrixHessianSpeed, (hd s hs).deriv]
  exact matrix_logdet_velocity_bound (γ s) (v s) (hp s ⟨hs.1.le, hs.2.le⟩)
    (matrix_spd_path_velocity_symmetric hp hs (hd s hs))

def MatrixPiecewiseAdmissiblePath (X Y : Matrix n n ℝ) (γ : ℝ → Matrix n n ℝ) : Prop :=
  γ 0 = X ∧ γ 1 = Y ∧ ContinuousOn γ (Set.Icc (0:ℝ) 1) ∧
    (∀ s ∈ Set.Icc (0:ℝ) 1, (γ s).PosDef) ∧
    ∃ (N : ℕ) (a : ℕ → ℝ) (v : ℕ → ℝ → Matrix n n ℝ),
      0 < N ∧ a 0 = 0 ∧ a N = 1 ∧
      (∀ j ≤ N, a j ∈ Set.Icc (0:ℝ) 1) ∧
      (∀ j < N, a j < a (j+1)) ∧
      ∀ j < N, ContinuousOn (v j) (Set.Icc (a j) (a (j+1))) ∧
        ∀ s ∈ Set.Ioo (a j) (a (j+1)), HasDerivAt γ (v j s) s

theorem matrix_piecewise_rank_one_iff (X Y : Matrix (Fin 1) (Fin 1) ℝ)
    (γ : ℝ → Matrix (Fin 1) (Fin 1) ℝ) :
    MatrixPiecewiseAdmissiblePath X Y γ ↔ RankOnePiecewiseAdmissiblePath X Y γ := Iff.rfl

theorem partition_endpoint_integral_bound (f speed : ℝ → ℝ) (C : ℝ)
    (N : ℕ) (a : ℕ → ℝ) (ha0 : a 0 = 0) (haN : a N = 1)
    (hi : ∀ j < N, IntervalIntegrable speed volume (a j) (a (j+1)))
    (hb : ∀ j < N, |f (a (j+1))-f (a j)| ≤ C * ∫ s : ℝ in a j..a (j+1), speed s) :
    |f 1-f 0| ≤ C * ∫ s : ℝ in (0:ℝ)..1, speed s := by
  have htel : (∑ j ∈ Finset.range N, (f (a (j+1))-f (a j))) = f 1-f 0 := by
    simpa only [haN, ha0] using Finset.sum_range_sub (fun j => f (a j)) N
  rw [← htel]
  calc
    _ ≤ ∑ j ∈ Finset.range N, |f (a (j+1))-f (a j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, C * ∫ s : ℝ in a j..a (j+1), speed s := by
      exact Finset.sum_le_sum fun j hj => hb j (Finset.mem_range.mp hj)
    _ = _ := by
      rw [← Finset.mul_sum, intervalIntegral.sum_integral_adjacent_intervals hi, ha0, haN]

theorem matrix_piecewise_diagonal_log_length_bound (X Y : Matrix n n ℝ)
    (γ : ℝ → Matrix n n ℝ) (hγ : MatrixPiecewiseAdmissiblePath X Y γ) (i : n) :
    |Real.log (Y i i)-Real.log (X i i)| ≤ matrixHessianPathLength γ := by
  rcases hγ with ⟨h0, h1, hc, hp, N, a, v, _, ha0, haN, ha, hstep, hv⟩
  have hsub j (hj : j < N) : Set.Icc (a j) (a (j+1)) ⊆ Set.Icc (0:ℝ) 1 :=
    Set.Icc_subset_Icc (ha j hj.le).1 (ha (j+1) (Nat.succ_le_of_lt hj)).2
  have hi j (hj : j < N) := matrix_segment_speed_integrable γ (v j) (a j) (a (j+1))
    (hstep j hj).le (hc.mono (hsub j hj)) (hv j hj).1
    (fun s hs => hp s (hsub j hj hs)) (hv j hj).2
  have hb j (hj : j < N) := matrix_segment_diagonal_log_bound γ (v j) (a j) (a (j+1))
    (hstep j hj).le (hc.mono (hsub j hj)) (hv j hj).1
    (fun s hs => hp s (hsub j hj hs)) (hv j hj).2 i
  have hh := partition_endpoint_integral_bound (fun s => Real.log (γ s i i))
    (matrixHessianSpeed γ) 1 N a ha0 haN hi (by simpa only [one_mul] using hb)
  simpa only [h0, h1, one_mul, matrixHessianPathLength] using hh

theorem matrix_piecewise_logdet_length_bound (X Y : Matrix n n ℝ)
    (γ : ℝ → Matrix n n ℝ) (hγ : MatrixPiecewiseAdmissiblePath X Y γ) :
    |Real.log Y.det-Real.log X.det| ≤
      Real.sqrt (Fintype.card n : ℝ) * matrixHessianPathLength γ := by
  rcases hγ with ⟨h0, h1, hc, hp, N, a, v, _, ha0, haN, ha, hstep, hv⟩
  have hsub j (hj : j < N) : Set.Icc (a j) (a (j+1)) ⊆ Set.Icc (0:ℝ) 1 :=
    Set.Icc_subset_Icc (ha j hj.le).1 (ha (j+1) (Nat.succ_le_of_lt hj)).2
  have hi j (hj : j < N) := matrix_segment_speed_integrable γ (v j) (a j) (a (j+1))
    (hstep j hj).le (hc.mono (hsub j hj)) (hv j hj).1
    (fun s hs => hp s (hsub j hj hs)) (hv j hj).2
  have hb j (hj : j < N) := matrix_segment_logdet_bound γ (v j) (a j) (a (j+1))
    (hstep j hj).le (hc.mono (hsub j hj)) (hv j hj).1
    (fun s hs => hp s (hsub j hj hs)) (hv j hj).2
  have hh := partition_endpoint_integral_bound (fun s => Real.log (γ s).det)
    (matrixHessianSpeed γ) (Real.sqrt (Fintype.card n : ℝ)) N a ha0 haN hi hb
  simpa only [h0, h1, matrixHessianPathLength] using hh

/-- The all-rank distance uses the same native length integral and full
finite-piece path class as the independently verified rank-one distance. -/
def matrixPiecewiseHessianDistance (X Y : Matrix n n ℝ) : ℝ :=
  sInf {r : ℝ | ∃ γ : ℝ → Matrix n n ℝ,
    MatrixPiecewiseAdmissiblePath X Y γ ∧ matrixHessianPathLength γ = r}

theorem matrix_piecewise_distance_rank_one (X Y : Matrix (Fin 1) (Fin 1) ℝ) :
    matrixPiecewiseHessianDistance X Y = rankOnePiecewiseHessianDistance X Y := rfl

theorem matrixHessianPathLength_nonnegative (γ : ℝ → Matrix n n ℝ) :
    0 ≤ matrixHessianPathLength γ := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
  intro s _
  exact Real.sqrt_nonneg _

end
end Sigma
