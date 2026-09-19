import SigmaMatrixRankOne

namespace Sigma
noncomputable section
open scoped Matrix Topology ComplexOrder BigOperators
open MeasureTheory

attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

/-- A segment allows one-sided endpoint derivatives: only interior derivatives
are used, with a continuous velocity extension to the closed interval. -/
theorem rank_one_segment_speed_integrable_and_bound (f v : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hc : ContinuousOn f (Set.Icc a b))
    (hp : ∀ t ∈ Set.Icc a b, 0 < f t) (hv : ContinuousOn v (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, HasDerivAt f (v t) t) :
    IntervalIntegrable (matrixHessianSpeed (fun t => rankOneMatrix (f t))) volume a b ∧
      |Real.log (f b) - Real.log (f a)| ≤
        ∫ t : ℝ in a..b, matrixHessianSpeed (fun u => rankOneMatrix (f u)) t := by
  have hvf : ContinuousOn (fun t => v t / f t) (Set.Icc a b) :=
    hv.div hc fun t ht => ne_of_gt (hp t ht)
  have hi : IntervalIntegrable (fun t => v t / f t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  have he : ∀ᵐ t : ℝ ∂volume, t ∈ Set.uIoc a b →
      |v t / f t| = matrixHessianSpeed (fun u => rankOneMatrix (f u)) t := by
    have hn : ∀ᵐ t : ℝ ∂volume, t ≠ b := by simp [ae_iff]
    filter_upwards [hn] with t hne ht
    rw [Set.uIoc_of_le hab] at ht
    have ht' : t ∈ Set.Ioo a b := ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩
    exact (rankOneMatrix_speed (hd t ht') (ne_of_gt (hp t ⟨ht.1.le, ht.2⟩))).symm
  have hnorm : IntervalIntegrable (fun t => |v t / f t|) volume a b := by
    simpa only [Real.norm_eq_abs] using hi.norm
  have hspeed := hnorm.congr ((ae_restrict_iff' measurableSet_uIoc).mpr he)
  refine ⟨hspeed, ?_⟩
  have hftc : (∫ t : ℝ in a..b, v t / f t) = Real.log (f b) - Real.log (f a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
      (hc.log fun t ht => ne_of_gt (hp t ht)) _ hi
    intro t ht
    exact (hd t ht).log (ne_of_gt (hp t ⟨ht.1.le, ht.2.le⟩))
  have hnormbound := intervalIntegral.norm_integral_le_integral_norm
    (f := fun t => v t / f t) (μ := volume) hab
  rw [hftc, Real.norm_eq_abs] at hnormbound
  refine hnormbound.trans_eq ?_
  simp only [Real.norm_eq_abs]
  exact intervalIntegral.integral_congr_ae he

/-- A genuine finite-piece C1 native matrix path. The velocity on each
closed segment is continuous, while its derivative identity is required
only in the open segment, so corners and one-sided endpoints are allowed. -/
def RankOnePiecewiseAdmissiblePath (X Y : Matrix (Fin 1) (Fin 1) ℝ)
    (γ : ℝ → Matrix (Fin 1) (Fin 1) ℝ) : Prop :=
  γ 0 = X ∧ γ 1 = Y ∧ ContinuousOn γ (Set.Icc (0:ℝ) 1) ∧
    (∀ s ∈ Set.Icc (0:ℝ) 1, (γ s).PosDef) ∧
    ∃ (n : ℕ) (a : ℕ → ℝ) (v : ℕ → ℝ → Matrix (Fin 1) (Fin 1) ℝ),
      0 < n ∧ a 0 = 0 ∧ a n = 1 ∧
      (∀ j ≤ n, a j ∈ Set.Icc (0:ℝ) 1) ∧
      (∀ j < n, a j < a (j+1)) ∧
      ∀ j < n, ContinuousOn (v j) (Set.Icc (a j) (a (j+1))) ∧
        ∀ s ∈ Set.Ioo (a j) (a (j+1)), HasDerivAt γ (v j s) s

theorem rank_one_piecewise_path_length_lower_bound
    (X Y : Matrix (Fin 1) (Fin 1) ℝ)
    (γ : ℝ → Matrix (Fin 1) (Fin 1) ℝ) (hγ : RankOnePiecewiseAdmissiblePath X Y γ) :
    |Real.log (Y 0 0) - Real.log (X 0 0)| ≤ matrixHessianPathLength γ := by
  rcases hγ with ⟨h0, h1, hc, hp, n, a, v, _, ha0, han, ha, hstep, hv⟩
  have hseg j (hj : j < n) :
      IntervalIntegrable (matrixHessianSpeed γ) volume (a j) (a (j+1)) ∧
        |Real.log (γ (a (j+1)) 0 0) - Real.log (γ (a j) 0 0)| ≤
          ∫ t : ℝ in a j..a (j+1), matrixHessianSpeed γ t := by
    have hsub : Set.Icc (a j) (a (j+1)) ⊆ Set.Icc (0:ℝ) 1 :=
      Set.Icc_subset_Icc (ha j hj.le).1 (ha (j+1) (Nat.succ_le_of_lt hj)).2
    have hh := rank_one_segment_speed_integrable_and_bound
      (fun t => γ t 0 0) (fun t => v j t 0 0) (a j) (a (j+1)) (hstep j hj).le
      (rankOneEntry.continuous.comp_continuousOn (hc.mono hsub))
      (fun t ht => (rankOneMatrix_posDef_iff _).mp (by
        rw [rankOneMatrix_entry]
        exact hp t (hsub ht)))
      (rankOneEntry.continuous.comp_continuousOn (hv j hj).1)
      (fun t ht => rankOneEntry.hasFDerivAt.comp_hasDerivAt t ((hv j hj).2 t ht))
    simpa only [rankOneMatrix_entry] using hh
  have htel : (∑ j ∈ Finset.range n,
      (Real.log (γ (a (j+1)) 0 0) - Real.log (γ (a j) 0 0))) =
        Real.log (Y 0 0) - Real.log (X 0 0) := by
    simpa only [han, ha0, h0, h1] using
      Finset.sum_range_sub (fun j => Real.log (γ (a j) 0 0)) n
  rw [← htel]
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        |Real.log (γ (a (j+1)) 0 0) - Real.log (γ (a j) 0 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, ∫ t : ℝ in a j..a (j+1), matrixHessianSpeed γ t := by
      apply Finset.sum_le_sum
      intro j hj
      exact (hseg j (Finset.mem_range.mp hj)).2
    _ = matrixHessianPathLength γ := by
      rw [intervalIntegral.sum_integral_adjacent_intervals (fun j hj => (hseg j hj).1), ha0, han]
      rfl

theorem rank_one_c1_path_piecewise_admissible
    (X Y : Matrix (Fin 1) (Fin 1) ℝ)
    (γ : ℝ → Matrix (Fin 1) (Fin 1) ℝ) (hγ : RankOneMatrixAdmissiblePath X Y γ) :
    RankOnePiecewiseAdmissiblePath X Y γ := by
  rcases hγ with ⟨h0, h1, hp, hd, hc⟩
  refine ⟨h0, h1, fun s hs => (hd s hs).continuousAt.continuousWithinAt, hp,
    1, (fun j => (j:ℝ)), (fun _ => deriv γ), by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · intro j hj
    interval_cases j <;> norm_num
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    norm_num
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    norm_num only [Nat.cast_zero, Nat.cast_one, zero_add]
    refine ⟨hc, fun s hs => (hd s ⟨hs.1.le, hs.2.le⟩).hasDerivAt⟩

/-- Riemannian distance as the actual length infimum over piecewise-C1
native SPD paths, including paths with corners and one-sided endpoints. -/
def rankOnePiecewiseHessianDistance (X Y : Matrix (Fin 1) (Fin 1) ℝ) : ℝ :=
  sInf {r : ℝ | ∃ γ : ℝ → Matrix (Fin 1) (Fin 1) ℝ,
    RankOnePiecewiseAdmissiblePath X Y γ ∧ matrixHessianPathLength γ = r}

theorem rank_one_piecewise_hessian_distance (X Y : Matrix (Fin 1) (Fin 1) ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    rankOnePiecewiseHessianDistance X Y = |Real.log (Y 0 0) - Real.log (X 0 0)| := by
  have hx : 0 < X 0 0 := (rankOneMatrix_posDef_iff _).mp (by rwa [rankOneMatrix_entry])
  have hy : 0 < Y 0 0 := (rankOneMatrix_posDef_iff _).mp (by rwa [rankOneMatrix_entry])
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨fun s => rankOneMatrix (rankOneExponentialPath (X 0 0) (Y 0 0) s), ?_,
      rank_one_exponential_path_length _ _⟩
    apply rank_one_c1_path_piecewise_admissible
    simpa only [rankOneMatrix_entry] using rank_one_exponential_native_path_admissible
      (X 0 0) (Y 0 0) hx hy
  · rintro r ⟨γ, hγ, rfl⟩
    exact rank_one_piecewise_path_length_lower_bound X Y γ hγ

theorem rank_one_piecewise_distance_eq_c1_distance
    (X Y : Matrix (Fin 1) (Fin 1) ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    rankOnePiecewiseHessianDistance X Y = rankOneMatrixHessianDistance X Y := by
  rw [rank_one_piecewise_hessian_distance X Y hX hY, rank_one_native_hessian_distance X Y hX hY]

theorem rank_one_piecewise_distance_divergence_symmetrization
    (X Y : Matrix (Fin 1) (Fin 1) ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    matrixDivergence X Y + matrixDivergence Y X =
      4 * Real.sinh (rankOnePiecewiseHessianDistance X Y / 2)^2 := by
  rw [rank_one_piecewise_distance_eq_c1_distance X Y hX hY]
  exact rank_one_native_distance_divergence_symmetrization X Y hX hY

end
end Sigma
