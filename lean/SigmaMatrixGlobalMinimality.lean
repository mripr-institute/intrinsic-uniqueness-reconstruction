import SigmaMatrixPathCongruence

/-!
This file isolates the differential step in the higher-rank SPD length
argument.  The spectral divided-difference map is proved contractive in the
native Hessian metric.  The remaining chain rule for the spectral definition
of `matrixSPDLog` is represented by an explicit hypothesis in the path lemma;
Mathlib does not currently provide this matrix-log derivative theorem.
-/

namespace Sigma
noncomputable section
open scoped Matrix Topology ComplexOrder BigOperators
open MeasureTheory

variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

/-- The spectral divided-difference formula for the differential of the
matrix logarithm at an SPD matrix.  This definition records the candidate
Frechet derivative; the chain-rule theorem for `matrixSPDLog` is separate. -/
def matrixSPDLogSpectralDifferential (A U : Matrix n n ℝ) (hA : A.PosDef) :
    Matrix n n ℝ := by
  let V := (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)
  let a := hA.isHermitian.eigenvalues
  let W := Vᵀ * U * V
  exact V * (Matrix.of fun i j => realLogDividedDifference (a i) (a j) * W i j) * Vᵀ

private theorem realLogDividedDifference_comm (x y : ℝ) :
    realLogDividedDifference x y = realLogDividedDifference y x := by
  by_cases h : x = y
  · subst y
    simp [realLogDividedDifference]
  · have h' : y ≠ x := Ne.symm h
    simp only [realLogDividedDifference, if_neg h, if_neg h']
    rw [div_eq_div_iff (sub_ne_zero.mpr h') (sub_ne_zero.mpr h)]
    ring

/-- The spectral matrix-log differential has Frobenius norm at most the
actual Hessian speed.  This is a native consequence of the divided-difference
estimate; it does not assume a derivative of `matrixSPDLog`. -/
theorem matrix_spd_log_spectral_differential_norm_bound
    (A U : Matrix n n ℝ) (hA : A.PosDef) (hU : U.IsSymm) :
    ‖matrixSPDLogSpectralDifferential A U hA‖ ≤
      matrixTangentSpeed A U := by
  let V := (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)
  let a := hA.isHermitian.eigenvalues
  let W := Vᵀ * U * V
  let L : Matrix n n ℝ := Matrix.of fun i j =>
    realLogDividedDifference (a i) (a j) * W i j
  have hV : Vᵀ * V = 1 := unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary
  have hW : W.IsSymm := by
    change Wᵀ = W
    dsimp [W]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hU]
    simp [Matrix.mul_assoc]
  have hL : L.IsSymm := by
    change Lᵀ = L
    ext i j
    simp only [Matrix.transpose_apply, L, Matrix.of_apply]
    rw [realLogDividedDifference_comm]
    have hWij : W j i = W i j := by
      have hh := congrArg (fun M : Matrix n n ℝ => M i j) hW
      simpa only [Matrix.transpose_apply] using hh
    rw [hWij]
  have hD : (V * L * Vᵀ).IsSymm := by
    change (V * L * Vᵀ)ᵀ = V * L * Vᵀ
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    change Lᵀ = L at hL
    rw [hL]
    simp [Matrix.mul_assoc]
  have hformula : ‖V * L * Vᵀ‖^2 =
      ∑ i, ∑ j, (realLogDividedDifference (a i) (a j) * W i j)^2 := by
    rw [matrix_symmetric_frobenius_norm_square _ hD]
    have htrace : Matrix.trace ((V * L * Vᵀ) * (V * L * Vᵀ)) =
        Matrix.trace (L * L) := by
      calc
        _ = Matrix.trace (V * (L * L) * Vᵀ) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Vᵀ V, hV]
          simp only [Matrix.one_mul]
        _ = Matrix.trace (Vᵀ * (V * (L * L))) := by
          rw [Matrix.trace_mul_comm]
        _ = Matrix.trace (L * L) := by
          rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
    rw [htrace, symmetric_trace_square L hL]
    simp [L, Matrix.of_apply]
  have hbound := matrix_spd_log_spectral_directional_bound A U hA hU
  have hEq : matrixSPDLogSpectralDifferential A U hA = V * L * Vᵀ := by
    simp [matrixSPDLogSpectralDifferential, V, a, W, L]
  rw [hEq, matrixTangentSpeed]
  have hSq : ‖V * L * Vᵀ‖^2 ≤
      precisionMetric A⁻¹ U U := by
    rw [hformula]
    exact hbound
  have hnonneg : 0 ≤ precisionMetric A⁻¹ U U :=
    precisionMetric_nonnegative A⁻¹ U hA.inv hU
  have hsqrt : (Real.sqrt (precisionMetric A⁻¹ U U))^2 =
      precisionMetric A⁻¹ U U := Real.sq_sqrt hnonneg
  nlinarith [norm_nonneg (V * L * Vᵀ), Real.sqrt_nonneg (precisionMetric A⁻¹ U U)]

/-- A subinterval length estimate for any continuously differentiable matrix
curve whose logarithmic coordinate has the displayed derivative bound.  The
explicit `hlog` is the matrix-log chain-rule obligation that remains to be
proved for arbitrary SPD paths. -/
theorem matrix_log_curve_subinterval_contraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Z W : ℝ → E) (speed : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b)
    (hZ : ContinuousOn Z (Set.Icc a b))
    (hW : ContinuousOn W (Set.Icc a b))
    (hderiv : ∀ s ∈ Set.Ioo a b, HasDerivAt Z (W s) s)
    (hint : IntervalIntegrable speed volume a b)
    (hbound : ∀ s ∈ Set.Ioo a b, ‖W s‖ ≤ speed s) :
    ‖Z b - Z a‖ ≤ ∫ s : ℝ in a..b, speed s := by
  have hw : IntervalIntegrable W volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hZ hderiv hw
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (f := W) (μ := volume) hab
  have hmono : ∫ s : ℝ in a..b, ‖W s‖ ≤ ∫ s : ℝ in a..b, speed s := by
    apply intervalIntegral.integral_mono_ae_restrict hab hw.norm hint
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    have hna : ∀ᵐ s : ℝ ∂volume, s ≠ a := by simp [ae_iff]
    have hnb : ∀ᵐ s : ℝ ∂volume, s ≠ b := by simp [ae_iff]
    filter_upwards [hna, hnb] with s hsa hsb hs
    exact hbound s ⟨lt_of_le_of_ne hs.1 hsa.symm, lt_of_le_of_ne hs.2 hsb⟩
  calc
    _ = ‖∫ s : ℝ in a..b, W s‖ := by rw [hftc]
    _ ≤ ∫ s : ℝ in a..b, ‖W s‖ := by simpa only [Real.norm_eq_abs] using hnorm
    _ ≤ ∫ s : ℝ in a..b, speed s := hmono

/-- The spectral logarithm along a globally SPD curve, with its positivity
proof made explicit. -/
def matrixSPDLogPath (γ : ℝ → Matrix n n ℝ) (hpos : ∀ s, (γ s).PosDef) :
    ℝ → Matrix n n ℝ := fun s => matrixSPDLog (γ s) (hpos s)

/-- The divided-difference candidate velocity of the spectral logarithm along
a matrix curve. -/
def matrixSPDLogPathVelocity (γ v : ℝ → Matrix n n ℝ)
    (hpos : ∀ s, (γ s).PosDef) (s : ℝ) : Matrix n n ℝ :=
  matrixSPDLogSpectralDifferential (γ s) (v s) (hpos s)

/-- Subinterval contraction for a C1 SPD path, conditional only on the
explicit matrix-log chain rule and continuity of its displayed derivative.
This is the exact calculus bridge required to turn the algebraic spectral
bound above into a path-length theorem. -/
theorem matrix_spd_log_path_subinterval_contraction
    (γ v : ℝ → Matrix n n ℝ) (hpos : ∀ s, (γ s).PosDef)
    (a b : ℝ) (hab : a ≤ b)
    (hγ : ContinuousOn γ (Set.Icc a b))
    (hv : ContinuousOn v (Set.Icc a b))
    (hd : ∀ s ∈ Set.Ioo a b, HasDerivAt γ (v s) s)
    (hZ : ContinuousOn (matrixSPDLogPath γ hpos) (Set.Icc a b))
    (hW : ContinuousOn (matrixSPDLogPathVelocity γ v hpos) (Set.Icc a b))
    (hlog : ∀ s ∈ Set.Ioo a b,
      HasDerivAt (matrixSPDLogPath γ hpos) (matrixSPDLogPathVelocity γ v hpos s) s) :
    ‖matrixSPDLog (γ b) (hpos b) - matrixSPDLog (γ a) (hpos a)‖ ≤
      ∫ s : ℝ in a..b, matrixHessianSpeed γ s := by
  have hp (s : ℝ) (hs : s ∈ Set.Icc a b) : (γ s).PosDef := hpos s
  have hint : IntervalIntegrable (matrixHessianSpeed γ) volume a b :=
    matrix_segment_speed_integrable γ v a b hab hγ hv hp hd
  apply matrix_log_curve_subinterval_contraction
    (matrixSPDLogPath γ hpos) (matrixSPDLogPathVelocity γ v hpos)
    (matrixHessianSpeed γ) a b hab hZ hW hlog hint
  intro s hs
  rw [matrixHessianSpeed, (hd s hs).deriv]
  have hU : (v s).IsSymm := matrix_spd_path_velocity_symmetric hp hs (hd s hs)
  exact matrix_spd_log_spectral_differential_norm_bound (γ s) (v s) (hpos s) hU

/-- The endpoint version for the paper's finite-piece path class, conditional
on the same spectral-log chain rule on each piece.  This handles corners by
integrating on the supplied partition and telescoping the log increments. -/
theorem matrix_spd_log_piecewise_length_lower_bound
    (X Y : Matrix n n ℝ) (γ : ℝ → Matrix n n ℝ)
    (hγ : MatrixPiecewiseAdmissiblePath X Y γ)
    (hpos : ∀ s, (γ s).PosDef)
    (hZ : ContinuousOn (matrixSPDLogPath γ hpos) (Set.Icc (0:ℝ) 1))
    (hlog : ∀ (N : ℕ) (a : ℕ → ℝ) (v : ℕ → ℝ → Matrix n n ℝ),
      0 < N → a 0 = 0 → a N = 1 →
      (∀ j ≤ N, a j ∈ Set.Icc (0:ℝ) 1) →
      (∀ j < N, a j < a (j+1)) →
      (∀ j < N, ContinuousOn (v j) (Set.Icc (a j) (a (j+1))) ∧
        ∀ s ∈ Set.Ioo (a j) (a (j+1)), HasDerivAt γ (v j s) s) →
      ∀ j < N, ∀ s ∈ Set.Ioo (a j) (a (j+1)),
        HasDerivAt (matrixSPDLogPath γ hpos)
          (matrixSPDLogSpectralDifferential (γ s) (v j s) (hpos s)) s)
    (hWcont : ∀ (N : ℕ) (a : ℕ → ℝ) (v : ℕ → ℝ → Matrix n n ℝ),
      0 < N → a 0 = 0 → a N = 1 →
      (∀ j ≤ N, a j ∈ Set.Icc (0:ℝ) 1) →
      (∀ j < N, a j < a (j+1)) →
      (∀ j < N, ContinuousOn (v j) (Set.Icc (a j) (a (j+1))) ∧
        ∀ s ∈ Set.Ioo (a j) (a (j+1)), HasDerivAt γ (v j s) s) →
      ∀ j < N, ContinuousOn
        (fun s => matrixSPDLogSpectralDifferential (γ s) (v j s) (hpos s))
      (Set.Icc (a j) (a (j+1)))) :
    ‖matrixSPDLog (γ 1) (hpos 1) - matrixSPDLog (γ 0) (hpos 0)‖ ≤
      matrixHessianPathLength γ := by
  rcases hγ with ⟨h0, h1, hc, hp, N, a, v, hN, ha0, haN, ha, hstep, hv⟩
  let Z := matrixSPDLogPath γ hpos
  let W (j : ℕ) : ℝ → Matrix n n ℝ :=
    fun s => matrixSPDLogSpectralDifferential (γ s) (v j s) (hpos s)
  have hsub (j : ℕ) (hj : j < N) :
      Set.Icc (a j) (a (j+1)) ⊆ Set.Icc (0:ℝ) 1 :=
    Set.Icc_subset_Icc (ha j hj.le).1 (ha (j+1) (Nat.succ_le_of_lt hj)).2
  have hi (j : ℕ) (hj : j < N) :
      IntervalIntegrable (matrixHessianSpeed γ) volume (a j) (a (j+1)) :=
    matrix_segment_speed_integrable γ (v j) (a j) (a (j+1)) (hstep j hj).le
      (hc.mono (hsub j hj)) (hv j hj).1
      (fun s hs => hp s (hsub j hj hs)) (hv j hj).2
  have hseg (j : ℕ) (hj : j < N) :
      ‖Z (a (j+1)) - Z (a j)‖ ≤
        ∫ s : ℝ in a j..a (j+1), matrixHessianSpeed γ s := by
    have hWc : ContinuousOn (W j) (Set.Icc (a j) (a (j+1))) := by
      simpa [W] using hWcont N a v hN ha0 haN ha hstep hv j hj
    have hlogj : ∀ s ∈ Set.Ioo (a j) (a (j+1)), HasDerivAt Z (W j s) s := by
      intro s hs
      simpa [Z, W] using hlog N a v hN ha0 haN ha hstep hv j hj s hs
    have hint := hi j hj
    apply matrix_log_curve_subinterval_contraction Z (W j) (matrixHessianSpeed γ)
      (a j) (a (j+1)) (hstep j hj).le
      (hZ.mono (Set.Icc_subset_Icc (ha j hj.le).1 (ha (j+1) (Nat.succ_le_of_lt hj)).2))
      hWc hlogj hint
    intro s hs
    rw [matrixHessianSpeed, (hv j hj).2 s hs |>.deriv]
    have hU : (v j s).IsSymm :=
      matrix_spd_path_velocity_symmetric
        (fun t ht => hp t (hsub j hj ht)) hs ((hv j hj).2 s hs)
    exact matrix_spd_log_spectral_differential_norm_bound (γ s) (v j s) (hpos s) hU
  have htel : (∑ j ∈ Finset.range N, (Z (a (j+1)) - Z (a j))) = Z 1-Z 0 := by
    simpa only [haN, ha0] using Finset.sum_range_sub (fun j => Z (a j)) N
  have hsum : ‖Z 1-Z 0‖ ≤
      ∑ j ∈ Finset.range N, ‖Z (a (j+1))-Z (a j)‖ := by
    rw [← htel]
    exact norm_sum_le _ _
  have hsum' : (∑ j ∈ Finset.range N, ‖Z (a (j+1))-Z (a j)‖) ≤
      ∑ j ∈ Finset.range N, ∫ s : ℝ in a j..a (j+1), matrixHessianSpeed γ s := by
    exact Finset.sum_le_sum fun j hj => hseg j (Finset.mem_range.mp hj)
  have hpieces : (∑ j ∈ Finset.range N,
      ∫ s : ℝ in a j..a (j+1), matrixHessianSpeed γ s) =
        matrixHessianPathLength γ := by
    change (∑ j ∈ Finset.range N,
      ∫ s : ℝ in a j..a (j+1), matrixHessianSpeed γ s) =
        ∫ s : ℝ in (0:ℝ)..1, matrixHessianSpeed γ s
    rw [← ha0, ← haN, intervalIntegral.sum_integral_adjacent_intervals hi]
  have hfinal := hsum.trans (hsum'.trans_eq hpieces)
  change ‖matrixSPDLog (γ 1) (hpos 1) - matrixSPDLog (γ 0) (hpos 0)‖ ≤
    ∫ s : ℝ in (0:ℝ)..1, matrixHessianSpeed γ s
  simpa only [matrixHessianPathLength] using hfinal

end
end Sigma
