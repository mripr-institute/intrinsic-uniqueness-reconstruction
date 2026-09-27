import SigmaMatrixGlobalMinimality

namespace Sigma
noncomputable section
open scoped Matrix Topology ComplexOrder
open MeasureTheory

variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

def matrixPathClampTime (s : ℝ) : ℝ := max 0 (min s 1)

theorem matrix_path_clamp_time_mem (s : ℝ) :
    matrixPathClampTime s ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_right _ _)

theorem matrix_path_clamp_time_eq (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    matrixPathClampTime s = s := by
  simp [matrixPathClampTime, min_eq_left hs.2, max_eq_right hs.1]

theorem matrix_path_clamp_time_eventually_eq (s : ℝ)
    (hs : s ∈ Set.Ioo (0:ℝ) 1) :
    (fun t => matrixPathClampTime t) =ᶠ[nhds s] id := by
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
  exact matrix_path_clamp_time_eq t ⟨ht.1.le, ht.2.le⟩

def matrixClampedPath (γ : ℝ → Matrix n n ℝ) (s : ℝ) : Matrix n n ℝ :=
  γ (matrixPathClampTime s)

omit [DecidableEq n] in
theorem matrix_clamped_path_posDef (γ : ℝ → Matrix n n ℝ)
    (hp : ∀ s ∈ Set.Icc (0:ℝ) 1, (γ s).PosDef) (s : ℝ) :
    (matrixClampedPath γ s).PosDef :=
  hp _ (matrix_path_clamp_time_mem s)

omit [Fintype n] [DecidableEq n] in
theorem matrix_clamped_path_eq (γ : ℝ → Matrix n n ℝ) (s : ℝ)
    (hs : s ∈ Set.Icc (0:ℝ) 1) : matrixClampedPath γ s = γ s := by
  simp [matrixClampedPath, matrix_path_clamp_time_eq s hs]

theorem matrix_clamped_path_hasDerivAt (γ : ℝ → Matrix n n ℝ)
    (s : ℝ) (hs : s ∈ Set.Ioo (0:ℝ) 1) (U : Matrix n n ℝ)
    (hd : HasDerivAt γ U s) : HasDerivAt (matrixClampedPath γ) U s := by
  apply hd.congr_of_eventuallyEq
  filter_upwards [matrix_path_clamp_time_eventually_eq s hs] with t ht
  simp [matrixClampedPath, ht]

theorem matrix_clamped_path_speed_eq (γ : ℝ → Matrix n n ℝ)
    (s : ℝ) (hs : s ∈ Set.Ioo (0:ℝ) 1) :
    matrixHessianSpeed (matrixClampedPath γ) s = matrixHessianSpeed γ s := by
  have he : matrixClampedPath γ =ᶠ[nhds s] γ := by
    filter_upwards [matrix_path_clamp_time_eventually_eq s hs] with t ht
    simp [matrixClampedPath, ht]
  rw [matrixHessianSpeed, matrixHessianSpeed, matrix_clamped_path_eq γ s ⟨hs.1.le, hs.2.le⟩]
  exact congrArg (fun U => Real.sqrt (precisionMetric (γ s)⁻¹ U U))
    (Filter.EventuallyEq.deriv_eq he)

theorem matrix_clamped_path_length_eq (γ : ℝ → Matrix n n ℝ) :
    matrixHessianPathLength (matrixClampedPath γ) = matrixHessianPathLength γ := by
  unfold matrixHessianPathLength
  apply intervalIntegral.integral_congr_ae
  have hn1 : ∀ᵐ s : ℝ ∂volume, s ≠ 1 := by simp [ae_iff]
  filter_upwards [hn1] with s hne hs
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
  exact matrix_clamped_path_speed_eq γ s ⟨hs.1, lt_of_le_of_ne hs.2 hne⟩

theorem matrix_clamped_path_admissible (X Y : Matrix n n ℝ)
    (γ : ℝ → Matrix n n ℝ) (hγ : MatrixPiecewiseAdmissiblePath X Y γ) :
    MatrixPiecewiseAdmissiblePath X Y (matrixClampedPath γ) := by
  rcases hγ with ⟨h0, h1, hc, hp, N, a, v, hN, ha0, haN, ha, hstep, hv⟩
  refine ⟨?_, ?_, ?_, (fun s _ => matrix_clamped_path_posDef γ hp s),
    N, a, v, hN, ha0, haN, ha, hstep, ?_⟩
  · simpa [matrix_clamped_path_eq γ 0 (by norm_num)] using h0
  · simpa [matrix_clamped_path_eq γ 1 (by norm_num)] using h1
  · apply hc.congr
    intro s hs
    exact matrix_clamped_path_eq γ s hs
  · intro j hj
    refine ⟨(hv j hj).1, ?_⟩
    intro s hs
    have hs01 : s ∈ Set.Ioo (0:ℝ) 1 :=
      ⟨lt_of_le_of_lt (ha j hj.le).1 hs.1,
        lt_of_lt_of_le hs.2 (ha (j+1) (Nat.succ_le_of_lt hj)).2⟩
    exact matrix_clamped_path_hasDerivAt γ s hs01 _ ((hv j hj).2 s hs)

end
end Sigma
