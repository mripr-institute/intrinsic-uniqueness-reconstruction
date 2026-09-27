import SigmaMatrixExpSpectral
import SigmaMatrixLogCalculus
import SigmaMatrixPiecewiseContraction

namespace Sigma
noncomputable section
open MeasureTheory
open scoped Matrix Topology
variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

/-- The actual spectral logarithm obeys the divided-difference chain rule
on every differentiable SPD path, with no log-regularity assumptions. -/
theorem matrix_spd_log_path_spectral_hasDerivAt
    (γ : ℝ → Matrix n n ℝ) (hpos : ∀ s, (γ s).PosDef)
    (s : ℝ) (U : Matrix n n ℝ) (hd : HasDerivAt γ U s) :
    HasDerivAt (matrixSPDLogPath γ hpos)
      (matrixSPDLogSpectralDifferential (γ s) U (hpos s)) s := by
  simpa only [matrix_exp_spd_log_equiv_symm_apply, matrixSPDLogPath] using
    matrix_spd_log_path_hasDerivAt γ hpos s U hd
      (matrixExpSPDLogEquiv (γ s) (hpos s))
      (matrix_exp_spd_log_equiv_coe (γ s) (hpos s))

theorem matrix_spd_log_path_spectral_continuousOn
    (γ : ℝ → Matrix n n ℝ) (hpos : ∀ s, (γ s).PosDef)
    (S : Set ℝ) (hc : ContinuousOn γ S) :
    ContinuousOn (matrixSPDLogPath γ hpos) S :=
  matrix_spd_log_path_continuousOn γ hpos S hc
    (fun s => matrixExpSPDLogEquiv (γ s) (hpos s))
    (fun s _ => matrix_exp_spd_log_equiv_coe (γ s) (hpos s))

theorem matrix_spd_log_path_velocity_continuousOn
    (γ v : ℝ → Matrix n n ℝ) (hpos : ∀ s, (γ s).PosDef)
    (S : Set ℝ) (hc : ContinuousOn γ S) (hv : ContinuousOn v S) :
    ContinuousOn (matrixSPDLogPathVelocity γ v hpos) S := by
  have hZ := matrix_spd_log_path_spectral_continuousOn γ hpos S hc
  have he := matrix_exp_inverse_differential_continuousOn
    (matrixSPDLogPath γ hpos) (fun s => matrixExpSPDLogEquiv (γ s) (hpos s)) S hZ
    (fun s _ => matrix_exp_spd_log_equiv_coe (γ s) (hpos s))
  simpa only [ContinuousLinearEquiv.coe_coe, matrix_exp_spd_log_equiv_symm_apply,
    matrixSPDLogPathVelocity] using he.clm_apply hv

/-- The paper's logarithmic length contraction, now with all logarithmic
regularity derived from the original C1 SPD path hypotheses. -/
theorem matrix_spd_log_path_contraction
    (γ v : ℝ → Matrix n n ℝ) (hpos : ∀ s, (γ s).PosDef)
    (a b : ℝ) (hab : a ≤ b)
    (hc : ContinuousOn γ (Set.Icc a b))
    (hv : ContinuousOn v (Set.Icc a b))
    (hd : ∀ s ∈ Set.Ioo a b, HasDerivAt γ (v s) s) :
    ‖matrixSPDLog (γ b) (hpos b) - matrixSPDLog (γ a) (hpos a)‖ ≤
      ∫ s : ℝ in a..b, matrixHessianSpeed γ s :=
  matrix_spd_log_path_subinterval_contraction γ v hpos a b hab hc hv hd
    (matrix_spd_log_path_spectral_continuousOn γ hpos _ hc)
    (matrix_spd_log_path_velocity_continuousOn γ v hpos _ hc hv)
    (fun s hs => matrix_spd_log_path_spectral_hasDerivAt γ hpos s _ (hd s hs))

theorem matrix_spd_log_piecewise_contraction
    (X Y : Matrix n n ℝ) (γ : ℝ → Matrix n n ℝ)
    (hγ : MatrixPiecewiseAdmissiblePath X Y γ)
    (hpos : ∀ s, (γ s).PosDef) :
    ‖matrixSPDLog (γ 1) (hpos 1) - matrixSPDLog (γ 0) (hpos 0)‖ ≤
      matrixHessianPathLength γ := by
  apply matrix_spd_log_piecewise_length_lower_bound X Y γ hγ hpos
    (matrix_spd_log_path_spectral_continuousOn γ hpos _ hγ.2.2.1)
  · intro N a v hN ha0 haN ha hstep hv j hj s hs
    exact matrix_spd_log_path_spectral_hasDerivAt γ hpos s _ ((hv j hj).2 s hs)
  · intro N a v hN ha0 haN ha hstep hv j hj
    have hsub : Set.Icc (a j) (a (j+1)) ⊆ Set.Icc (0:ℝ) 1 :=
      Set.Icc_subset_Icc (ha j hj.le).1 (ha (j+1) (Nat.succ_le_of_lt hj)).2
    exact matrix_spd_log_path_velocity_continuousOn γ (v j) hpos _
      (hγ.2.2.1.mono hsub) (hv j hj).1

theorem matrix_spd_log_piecewise_subinterval_contraction
    (X Y : Matrix n n ℝ) (γ : ℝ → Matrix n n ℝ)
    (hγ : MatrixPiecewiseAdmissiblePath X Y γ)
    (hpos : ∀ s, (γ s).PosDef)
    (s t : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hst : s ≤ t) :
    ‖matrixSPDLog (γ t) (hpos t) - matrixSPDLog (γ s) (hpos s)‖ ≤
      ∫ u : ℝ in s..t, matrixHessianSpeed γ u := by
  rcases hγ with ⟨h0, h1, hc, hp, N, a, v, hN, ha0, haN, ha, hstep, hv⟩
  let Z := matrixSPDLogPath γ hpos
  let W j := matrixSPDLogPathVelocity γ (v j) hpos
  have hsub j (hj : j < N) : Set.Icc (a j) (a (j+1)) ⊆ Set.Icc (0:ℝ) 1 :=
    Set.Icc_subset_Icc (ha j hj.le).1 (ha (j+1) (Nat.succ_le_of_lt hj)).2
  apply piecewise_curve_subinterval_contraction Z W (matrixHessianSpeed γ)
    N a ha0 haN ha hstep
    (matrix_spd_log_path_spectral_continuousOn γ hpos _ hc)
    (fun j hj => matrix_spd_log_path_velocity_continuousOn γ (v j) hpos _
      (hc.mono (hsub j hj)) (hv j hj).1)
    (fun j hj u hu => matrix_spd_log_path_spectral_hasDerivAt γ hpos u _ ((hv j hj).2 u hu))
    (fun j hj => matrix_segment_speed_integrable γ (v j) (a j) (a (j+1))
      (hstep j hj).le (hc.mono (hsub j hj)) (hv j hj).1
      (fun u _ => hpos u) (hv j hj).2) _ s t hs ht hst
  intro j hj u hu
  rw [matrixHessianSpeed, ((hv j hj).2 u hu).deriv]
  exact matrix_spd_log_spectral_differential_norm_bound _ _ (hpos u)
    (matrix_spd_path_velocity_symmetric (fun u _ => hpos u) hu ((hv j hj).2 u hu))

end
end Sigma
