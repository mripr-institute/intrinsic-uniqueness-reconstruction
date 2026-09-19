import SigmaMatrixGeodesic

namespace Sigma
noncomputable section
open scoped Matrix Topology ComplexOrder
open MeasureTheory

attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

/-- The actual one-by-one real matrix with its indicated entry. -/
def rankOneMatrix (x : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => x

theorem rankOneMatrix_mul (x y : ℝ) :
    rankOneMatrix x * rankOneMatrix y = rankOneMatrix (x*y) := by
  ext i j
  simp [rankOneMatrix, Matrix.mul_apply]

theorem rankOneMatrix_one : rankOneMatrix 1 = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  rfl

theorem rankOneMatrix_inv (x : ℝ) (hx : x ≠ 0) :
    (rankOneMatrix x)⁻¹ = rankOneMatrix x⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [rankOneMatrix_mul, inv_mul_cancel₀ hx, rankOneMatrix_one]

theorem rankOneMatrix_posDef (x : ℝ) (hx : 0 < x) : (rankOneMatrix x).PosDef := by
  have he : rankOneMatrix x = Matrix.diagonal (fun _ : Fin 1 => x) := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  rw [he]
  exact Matrix.PosDef.diagonal fun _ => hx

theorem rankOneMatrix_hasDerivAt {f : ℝ → ℝ} {v s : ℝ} (hf : HasDerivAt f v s) :
    HasDerivAt (fun t => rankOneMatrix (f t)) (rankOneMatrix v) s := by
  have he (x : ℝ) : x • rankOneMatrix 1 = rankOneMatrix x := by
    ext i j
    simp [rankOneMatrix]
  simpa only [he] using hf.smul_const (rankOneMatrix 1)

theorem rankOneMatrix_metric (x v : ℝ) (hx : x ≠ 0) :
    precisionMetric (rankOneMatrix x)⁻¹ (rankOneMatrix v) (rankOneMatrix v) = (v/x)^2 := by
  rw [rankOneMatrix_inv x hx]
  unfold precisionMetric
  rw [rankOneMatrix_mul, rankOneMatrix_mul, rankOneMatrix_mul, Matrix.trace_fin_one]
  simp only [rankOneMatrix]
  ring

theorem rankOneMatrix_speed {f : ℝ → ℝ} {v s : ℝ}
    (hf : HasDerivAt f v s) (hx : f s ≠ 0) :
    matrixHessianSpeed (fun t => rankOneMatrix (f t)) s = |v/f s| := by
  rw [matrixHessianSpeed, (rankOneMatrix_hasDerivAt hf).deriv,
    rankOneMatrix_metric _ _ hx, Real.sqrt_sq_eq_abs]

/-- A variational lower bound for every positive differentiable path whose
logarithmic velocity is integrable. No minimizing-path premise is assumed. -/
theorem rank_one_hessian_length_lower_bound (f v : ℝ → ℝ)
    (hpos : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 < f s)
    (hderiv : ∀ s ∈ Set.Icc (0:ℝ) 1, HasDerivAt f (v s) s)
    (hint : IntervalIntegrable (fun s => v s / f s) volume 0 1) :
    |Real.log (f 1) - Real.log (f 0)| ≤
      matrixHessianPathLength (fun s => rankOneMatrix (f s)) := by
  have hi : (∫ s : ℝ in (0:ℝ)..1, v s / f s) = Real.log (f 1) - Real.log (f 0) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => Real.log (f s)) _ hint
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
    exact (hderiv s hs).log (ne_of_gt (hpos s hs))
  have hb := intervalIntegral.norm_integral_le_integral_norm
    (f := fun s : ℝ => v s / f s) (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
  rw [hi, Real.norm_eq_abs] at hb
  refine hb.trans_eq ?_
  unfold matrixHessianPathLength
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
  rw [rankOneMatrix_speed (hderiv s hs) (ne_of_gt (hpos s hs))]
  exact Real.norm_eq_abs _

def rankOneExponentialPath (x y s : ℝ) : ℝ :=
  Real.exp (Real.log x + s * (Real.log y - Real.log x))

theorem rank_one_exponential_path_positive (x y s : ℝ) :
    0 < rankOneExponentialPath x y s := Real.exp_pos _

theorem rank_one_exponential_path_zero (x y : ℝ) (hx : 0 < x) :
    rankOneExponentialPath x y 0 = x := by
  simp [rankOneExponentialPath, Real.exp_log hx]

theorem rank_one_exponential_path_one (x y : ℝ) (hy : 0 < y) :
    rankOneExponentialPath x y 1 = y := by
  simp [rankOneExponentialPath, Real.exp_log hy]

theorem rank_one_exponential_path_hasDerivAt (x y s : ℝ) :
    HasDerivAt (rankOneExponentialPath x y)
      (rankOneExponentialPath x y s * (Real.log y - Real.log x)) s := by
  simpa only [rankOneExponentialPath, one_mul, zero_add] using
    (((hasDerivAt_id s).mul_const (Real.log y - Real.log x)).const_add (Real.log x)).exp

theorem rank_one_exponential_path_continuous (x y : ℝ) :
    Continuous (rankOneExponentialPath x y) :=
  continuous_iff_continuousAt.mpr fun s => (rank_one_exponential_path_hasDerivAt x y s).continuousAt

theorem rank_one_exponential_path_speed (x y s : ℝ) :
    matrixHessianSpeed (fun t => rankOneMatrix (rankOneExponentialPath x y t)) s =
      |Real.log y - Real.log x| := by
  rw [rankOneMatrix_speed (rank_one_exponential_path_hasDerivAt x y s)
    (ne_of_gt (rank_one_exponential_path_positive x y s))]
  congr 1
  exact mul_div_cancel_left₀ _ (ne_of_gt (rank_one_exponential_path_positive x y s))

theorem rank_one_exponential_path_length (x y : ℝ) :
    matrixHessianPathLength (fun t => rankOneMatrix (rankOneExponentialPath x y t)) =
      |Real.log y - Real.log x| := by
  unfold matrixHessianPathLength
  simp_rw [rank_one_exponential_path_speed]
  simp

/-- The ordinary C1 path class on the compact parameter interval; positivity
and endpoint conditions refer to the actual scalar matrix entry. -/
def RankOneAdmissiblePath (x y : ℝ) (f : ℝ → ℝ) : Prop :=
  f 0 = x ∧ f 1 = y ∧
    (∀ s ∈ Set.Icc (0:ℝ) 1, 0 < f s) ∧
    (∀ s ∈ Set.Icc (0:ℝ) 1, DifferentiableAt ℝ f s) ∧
    ContinuousOn (deriv f) (Set.Icc (0:ℝ) 1)

theorem rank_one_admissible_path_length_lower_bound (x y : ℝ) (f : ℝ → ℝ)
    (hf : RankOneAdmissiblePath x y f) :
    |Real.log y - Real.log x| ≤ matrixHessianPathLength (fun s => rankOneMatrix (f s)) := by
  rcases hf with ⟨h0, h1, hp, hd, hc⟩
  have hcF : ContinuousOn f (Set.Icc (0:ℝ) 1) :=
    fun s hs => (hd s hs).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable (fun s => deriv f s / f s) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact hc.div hcF fun s hs => ne_of_gt (hp s hs)
  simpa only [h0, h1] using rank_one_hessian_length_lower_bound f (deriv f) hp
    (fun s hs => (hd s hs).hasDerivAt) hi

theorem rank_one_exponential_path_admissible (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    RankOneAdmissiblePath x y (rankOneExponentialPath x y) := by
  refine ⟨rank_one_exponential_path_zero x y hx, rank_one_exponential_path_one x y hy,
    fun s _ => rank_one_exponential_path_positive x y s,
    fun s _ => (rank_one_exponential_path_hasDerivAt x y s).differentiableAt, ?_⟩
  have he : deriv (rankOneExponentialPath x y) =
      fun s => rankOneExponentialPath x y s * (Real.log y - Real.log x) := by
    funext s
    exact (rank_one_exponential_path_hasDerivAt x y s).deriv
  rw [he]
  exact ((rank_one_exponential_path_continuous x y).mul continuous_const).continuousOn

/-- Variational Hessian distance: an infimum over all positive C1 paths,
not a definition in terms of the candidate logarithmic formula. -/
def rankOneHessianDistance (x y : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ f : ℝ → ℝ, RankOneAdmissiblePath x y f ∧
    matrixHessianPathLength (fun s => rankOneMatrix (f s)) = r}

theorem rank_one_hessian_distance (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    rankOneHessianDistance x y = |Real.log y - Real.log x| := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨rankOneExponentialPath x y, rank_one_exponential_path_admissible x y hx hy,
      rank_one_exponential_path_length x y⟩
  · rintro r ⟨f, hf, rfl⟩
    exact rank_one_admissible_path_length_lower_bound x y f hf

theorem rank_one_hessian_distance_self (x : ℝ) (hx : 0 < x) :
    rankOneHessianDistance x x = 0 := by
  rw [rank_one_hessian_distance x x hx hx, sub_self, abs_zero]

theorem rankOneMatrix_entry (A : Matrix (Fin 1) (Fin 1) ℝ) : rankOneMatrix (A 0 0) = A := by
  ext i j
  fin_cases i
  fin_cases j
  rfl

def rankOneEntry : Matrix (Fin 1) (Fin 1) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A 0 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem rankOneMatrix_posDef_iff (x : ℝ) : (rankOneMatrix x).PosDef ↔ 0 < x := by
  have he : rankOneMatrix x = Matrix.diagonal (fun _ : Fin 1 => x) := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  rw [he, Matrix.posDef_diagonal_iff]
  exact ⟨fun h => h 0, fun h _ => h⟩

/-- Native matrix C1 paths in the open SPD cone, with fixed endpoints. -/
def RankOneMatrixAdmissiblePath (X Y : Matrix (Fin 1) (Fin 1) ℝ)
    (γ : ℝ → Matrix (Fin 1) (Fin 1) ℝ) : Prop :=
  γ 0 = X ∧ γ 1 = Y ∧
    (∀ s ∈ Set.Icc (0:ℝ) 1, (γ s).PosDef) ∧
    (∀ s ∈ Set.Icc (0:ℝ) 1, DifferentiableAt ℝ γ s) ∧
    ContinuousOn (deriv γ) (Set.Icc (0:ℝ) 1)

theorem rank_one_native_path_scalar_admissible (X Y : Matrix (Fin 1) (Fin 1) ℝ)
    (γ : ℝ → Matrix (Fin 1) (Fin 1) ℝ) (hγ : RankOneMatrixAdmissiblePath X Y γ) :
    RankOneAdmissiblePath (X 0 0) (Y 0 0) (fun s => γ s 0 0) := by
  rcases hγ with ⟨h0, h1, hp, hd, hc⟩
  have hder s (hs : s ∈ Set.Icc (0:ℝ) 1) :
      HasDerivAt (fun t => γ t 0 0) (deriv γ s 0 0) s :=
    rankOneEntry.hasFDerivAt.comp_hasDerivAt s (hd s hs).hasDerivAt
  refine ⟨congrArg (fun A => A 0 0) h0, congrArg (fun A => A 0 0) h1, ?_,
    fun s hs => (hder s hs).differentiableAt, ?_⟩
  · intro s hs
    apply (rankOneMatrix_posDef_iff _).mp
    rw [rankOneMatrix_entry]
    exact hp s hs
  · have hcc : ContinuousOn (fun s => rankOneEntry (deriv γ s)) (Set.Icc (0:ℝ) 1) :=
      rankOneEntry.continuous.comp_continuousOn hc
    apply hcc.congr
    intro s hs
    exact (hder s hs).deriv

theorem rank_one_native_path_length_lower_bound (X Y : Matrix (Fin 1) (Fin 1) ℝ)
    (γ : ℝ → Matrix (Fin 1) (Fin 1) ℝ) (hγ : RankOneMatrixAdmissiblePath X Y γ) :
    |Real.log (Y 0 0) - Real.log (X 0 0)| ≤ matrixHessianPathLength γ := by
  have h := rank_one_admissible_path_length_lower_bound (X 0 0) (Y 0 0)
    (fun s => γ s 0 0) (rank_one_native_path_scalar_admissible X Y γ hγ)
  simpa only [rankOneMatrix_entry] using h

theorem rank_one_exponential_native_path_admissible (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    RankOneMatrixAdmissiblePath (rankOneMatrix x) (rankOneMatrix y)
      (fun s => rankOneMatrix (rankOneExponentialPath x y s)) := by
  refine ⟨congrArg rankOneMatrix (rank_one_exponential_path_zero x y hx),
    congrArg rankOneMatrix (rank_one_exponential_path_one x y hy),
    fun s _ => rankOneMatrix_posDef _ (rank_one_exponential_path_positive x y s),
    fun s _ => (rankOneMatrix_hasDerivAt (rank_one_exponential_path_hasDerivAt x y s)).differentiableAt,
    ?_⟩
  have he : deriv (fun s => rankOneMatrix (rankOneExponentialPath x y s)) =
      fun s => rankOneMatrix (rankOneExponentialPath x y s * (Real.log y - Real.log x)) := by
    funext s
    exact (rankOneMatrix_hasDerivAt (rank_one_exponential_path_hasDerivAt x y s)).deriv
  rw [he]
  apply Continuous.continuousOn
  apply continuous_iff_continuousAt.mpr
  intro s
  exact (rankOneMatrix_hasDerivAt
    ((rank_one_exponential_path_hasDerivAt x y s).mul_const _)).continuousAt

def rankOneMatrixHessianDistance (X Y : Matrix (Fin 1) (Fin 1) ℝ) : ℝ :=
  sInf {r : ℝ | ∃ γ : ℝ → Matrix (Fin 1) (Fin 1) ℝ,
    RankOneMatrixAdmissiblePath X Y γ ∧ matrixHessianPathLength γ = r}

theorem rank_one_native_hessian_distance (X Y : Matrix (Fin 1) (Fin 1) ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    rankOneMatrixHessianDistance X Y = |Real.log (Y 0 0) - Real.log (X 0 0)| := by
  have hx : 0 < X 0 0 := (rankOneMatrix_posDef_iff _).mp (by rwa [rankOneMatrix_entry])
  have hy : 0 < Y 0 0 := (rankOneMatrix_posDef_iff _).mp (by rwa [rankOneMatrix_entry])
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨fun s => rankOneMatrix (rankOneExponentialPath (X 0 0) (Y 0 0) s), ?_,
      rank_one_exponential_path_length _ _⟩
    simpa only [rankOneMatrix_entry] using rank_one_exponential_native_path_admissible
      (X 0 0) (Y 0 0) hx hy
  · rintro r ⟨γ, hγ, rfl⟩
    exact rank_one_native_path_length_lower_bound X Y γ hγ

theorem rank_one_divergence (x y : ℝ) (hy : 0 < y) :
    matrixDivergence (rankOneMatrix x) (rankOneMatrix y) =
      x/y - Real.log (x/y) - 1 := by
  rw [matrixDivergence, rankOneMatrix_inv y (ne_of_gt hy), rankOneMatrix_mul,
    Matrix.trace_fin_one, Matrix.det_fin_one]
  simp only [rankOneMatrix, Fintype.card_fin, Nat.cast_one]
  rw [div_eq_mul_inv, mul_comm y⁻¹ x]

theorem rank_one_distance_divergence_symmetrization (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    matrixDivergence (rankOneMatrix x) (rankOneMatrix y) +
      matrixDivergence (rankOneMatrix y) (rankOneMatrix x) =
        4 * Real.sinh (rankOneHessianDistance x y / 2)^2 := by
  rw [rank_one_divergence x y hy, rank_one_divergence y x hx,
    Real.log_div (ne_of_gt hx) (ne_of_gt hy), Real.log_div (ne_of_gt hy) (ne_of_gt hx)]
  have he := positive_eigenvalue_hyperbolic_symmetrization (div_pos hy hx)
  rw [inv_div, Real.log_div (ne_of_gt hy) (ne_of_gt hx)] at he
  rw [rank_one_hessian_distance x y hx hy]
  have ha (z : ℝ) : Real.sinh (|z|/2)^2 = Real.sinh (z/2)^2 := by
    rcases le_total 0 z with hz | hz
    · rw [abs_of_nonneg hz]
    · rw [abs_of_nonpos hz, neg_div, Real.sinh_neg, neg_sq]
  rw [ha]
  linarith

theorem rank_one_native_distance_divergence_symmetrization
    (X Y : Matrix (Fin 1) (Fin 1) ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    matrixDivergence X Y + matrixDivergence Y X =
      4 * Real.sinh (rankOneMatrixHessianDistance X Y / 2)^2 := by
  have hx : 0 < X 0 0 := (rankOneMatrix_posDef_iff _).mp (by rwa [rankOneMatrix_entry])
  have hy : 0 < Y 0 0 := (rankOneMatrix_posDef_iff _).mp (by rwa [rankOneMatrix_entry])
  have h := rank_one_distance_divergence_symmetrization (X 0 0) (Y 0 0) hx hy
  rw [rankOneMatrix_entry, rankOneMatrix_entry, rank_one_hessian_distance _ _ hx hy] at h
  rwa [rank_one_native_hessian_distance X Y hX hY]

end
end Sigma
