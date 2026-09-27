import SigmaMatrixGlobalGeodesic
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Sigma
noncomputable section
open MeasureTheory
open scoped Matrix Topology ComplexOrder

/-- The two endpoint length bounds determine every intermediate point in a
real Hilbert space. This includes coincident endpoints without dividing by
their distance. -/
theorem hilbert_two_endpoint_bounds_unique {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (z k : E) (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1)
    (hl : ‖z‖ ≤ s * ‖k‖) (hr : ‖k-z‖ ≤ (1-s)*‖k‖) : z = s • k := by
  have hl2 : ‖z‖^2 ≤ s^2*‖k‖^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl)
      (add_nonneg (mul_nonneg hs.1 (norm_nonneg k)) (norm_nonneg z))]
  have hr2 : ‖k-z‖^2 ≤ (1-s)^2*‖k‖^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg (mul_nonneg (sub_nonneg.mpr hs.2) (norm_nonneg k)) (norm_nonneg (k-z)))]
  have hid : ‖z-s•k‖^2 = (1-s)*‖z‖^2+s*‖k-z‖^2-s*(1-s)*‖k‖^2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hs.1, real_inner_comm k z]
    ring
  have hn : ‖z-s•k‖^2 ≤ 0 := by
    rw [hid]
    have h1 := mul_le_mul_of_nonneg_left hl2 (sub_nonneg.mpr hs.2)
    have h2 := mul_le_mul_of_nonneg_left hr2 hs.1
    nlinarith
  have he : ‖z-s•k‖ = 0 := by nlinarith [sq_nonneg ‖z-s•k‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp he)

variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

theorem matrix_spd_log_identity (hI : (1 : Matrix n n ℝ).PosDef) :
    matrixSPDLog 1 hI = 0 := by
  have hd := hI.isHermitian.star_mul_self_mul_eq_diagonal
  rw [Matrix.mul_one, unitary.coe_star_mul_self] at hd
  have he (i : n) : hI.isHermitian.eigenvalues i = 1 := by
    have h := congrArg (fun M : Matrix n n ℝ => M i i) hd
    simpa using h.symm
  simp [matrixSPDLog, he]

theorem matrix_relative_spd_self (X : Matrix n n ℝ) (hX : X.PosDef) :
    matrixRelativeSPD X X hX = 1 := by
  let Q := hX.posSemidef.sqrt
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp
    (sqrt_positive_definite_isUnit X hX)
  rw [matrixRelativeSPD, ← matrix_sqrt_inverse X hX]
  change Q⁻¹ * X * Q⁻¹ = 1
  rw [← hX.posSemidef.sqrt_mul_self]
  change Q⁻¹ * (Q*Q) * Q⁻¹ = 1
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Q hd, Matrix.one_mul,
    Matrix.mul_nonsing_inv Q hd]

theorem matrix_relative_spd_log_self (X : Matrix n n ℝ) (hX : X.PosDef) :
    matrixSPDLog (matrixRelativeSPD X X hX) (matrix_relative_spd_positive X X hX hX) = 0 := by
  have hh : ∀ (A : Matrix n n ℝ) (hA : A.PosDef), A = 1 → matrixSPDLog A hA = 0 := by
    intro A hA he
    subst A
    exact matrix_spd_log_identity hA
  exact hh _ _ (matrix_relative_spd_self X hX)

theorem matrix_piecewise_hessian_distance_self (X : Matrix n n ℝ) (hX : X.PosDef) :
    matrixPiecewiseHessianDistance X X = 0 := by
  have hmem : (0:ℝ) ∈ {r : ℝ | ∃ γ : ℝ → Matrix n n ℝ,
      MatrixPiecewiseAdmissiblePath X X γ ∧ matrixHessianPathLength γ = r} := by
    refine ⟨matrixSPDGeodesic X X hX hX, matrix_spd_geodesic_admissible X X hX hX, ?_⟩
    rw [matrix_spd_geodesic_length, matrix_relative_spd_log_self, norm_zero]
  have hnonneg : ∀ r ∈ {r : ℝ | ∃ γ : ℝ → Matrix n n ℝ,
      MatrixPiecewiseAdmissiblePath X X γ ∧ matrixHessianPathLength γ = r}, (0:ℝ) ≤ r := by
    rintro r ⟨γ, _, rfl⟩
    exact matrixHessianPathLength_nonnegative γ
  exact le_antisymm (csInf_le ⟨0,hnonneg⟩ hmem) (le_csInf ⟨0,hmem⟩ hnonneg)

theorem matrix_two_endpoint_bounds_unique (Z K : Matrix n n ℝ) (s : ℝ)
    (hs : s ∈ Set.Icc (0:ℝ) 1)
    (hl : ‖Z‖ ≤ s*‖K‖) (hr : ‖K-Z‖ ≤ (1-s)*‖K‖) : Z = s • K := by
  letI : InnerProductSpace ℝ (Matrix n n ℝ) :=
    inferInstanceAs (InnerProductSpace ℝ (PiLp 2 fun _ : n => PiLp 2 fun _ : n => ℝ))
  exact hilbert_two_endpoint_bounds_unique Z K s hs hl hr

/-- Constant metric speed turns the integrated logarithmic contraction into
the two endpoint bounds. The analytic contraction is kept explicit in this
helper; it is needed only on the two subintervals ending at the chosen time. -/
theorem matrix_log_curve_unique_of_subinterval_bounds
    (γ Z : ℝ → Matrix n n ℝ) (K : Matrix n n ℝ)
    (hZ0 : Z 0 = 0) (hZ1 : Z 1 = K)
    (hbound : ∀ a b, a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 → a ≤ b →
      ‖Z b-Z a‖ ≤ ∫ u : ℝ in a..b, matrixHessianSpeed γ u)
    (c : ℝ) (hc : ∀ᵐ u : ℝ ∂volume,
      u ∈ Set.Icc (0:ℝ) 1 → matrixHessianSpeed γ u = c)
    (hmin : matrixHessianPathLength γ = ‖K‖)
    (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) : Z s = s • K := by
  have hi (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
      (∫ u : ℝ in a..b, matrixHessianSpeed γ u) = (b-a)*c := by
    calc
      _ = ∫ _u : ℝ in a..b, c := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hc] with u hu huab
        rw [Set.uIoc_of_le hab] at huab
        exact hu ⟨ha.trans huab.1.le, huab.2.trans hb⟩
      _ = _ := by simp
  have hcd : c = ‖K‖ := by
    have h := hi 0 1 le_rfl le_rfl (by norm_num)
    change matrixHessianPathLength γ = (1-0)*c at h
    rw [hmin] at h
    simpa using h.symm
  apply matrix_two_endpoint_bounds_unique (Z s) K s hs
  · have h := hbound 0 s (by simp) hs hs.1
    simpa only [hZ0, sub_zero, hi 0 s le_rfl hs.2 hs.1, hcd] using h
  · have h := hbound s 1 hs (by simp) hs.2
    simpa only [hZ1, hi s 1 hs.1 le_rfl hs.2, hcd] using h

/-- The uniqueness endpoint for an actual logarithmic lift of an SPD curve.
It requires the subinterval contraction, rather than assuming collinearity
or the desired geodesic formula. -/
theorem matrix_constant_speed_unique_of_log_bounds
    (X Y : Matrix n n ℝ) (hX : X.PosDef) (hY : Y.PosDef)
    (γ Z : ℝ → Matrix n n ℝ)
    (hZ0 : Z 0 = 0)
    (hZ1 : Z 1 = matrixSPDLog (matrixRelativeSPD X Y hX)
      (matrix_relative_spd_positive X Y hX hY))
    (hLift : ∀ s ∈ Set.Icc (0:ℝ) 1,
      γ s = hX.posSemidef.sqrt * NormedSpace.exp ℝ (Z s) * hX.posSemidef.sqrt)
    (hbound : ∀ a b, a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 → a ≤ b →
      ‖Z b-Z a‖ ≤ ∫ u : ℝ in a..b, matrixHessianSpeed γ u)
    (c : ℝ) (hc : ∀ᵐ u : ℝ ∂volume,
      u ∈ Set.Icc (0:ℝ) 1 → matrixHessianSpeed γ u = c)
    (hmin : matrixHessianPathLength γ = ‖matrixSPDLog (matrixRelativeSPD X Y hX)
      (matrix_relative_spd_positive X Y hX hY)‖)
    (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) : γ s = matrixSPDGeodesic X Y hX hY s := by
  rw [hLift s hs, matrix_log_curve_unique_of_subinterval_bounds γ Z _ hZ0 hZ1
    hbound c hc hmin s hs]
  rfl

/-- A finite-piece SPD curve with zero speed almost everywhere is constant.
This uses positive definiteness of the native Hessian metric and the ordinary
fundamental theorem of calculus on each piece, without matrix-log calculus. -/
theorem matrix_piecewise_zero_speed_constant
    (X Y : Matrix n n ℝ) (γ : ℝ → Matrix n n ℝ)
    (hγ : MatrixPiecewiseAdmissiblePath X Y γ)
    (hz : ∀ᵐ u : ℝ ∂volume,
      u ∈ Set.Icc (0:ℝ) 1 → matrixHessianSpeed γ u = 0)
    (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) : γ s = X := by
  rcases hγ with ⟨h0, _, hc, hp, N, a, v, _, ha0, haN, ha, hstep, hv⟩
  have hsub j (hj : j < N) : Set.Icc (a j) (a (j+1)) ⊆ Set.Icc (0:ℝ) 1 :=
    Set.Icc_subset_Icc (ha j hj.le).1 (ha (j+1) (Nat.succ_le_of_lt hj)).2
  have hvzero j (hj : j < N) : ∀ᵐ u : ℝ ∂volume,
      u ∈ Set.Ioo (a j) (a (j+1)) → v j u = 0 := by
    filter_upwards [hz] with u hu hju
    have hpu := hp u (hsub j hj ⟨hju.1.le,hju.2.le⟩)
    have hsym := matrix_spd_path_velocity_symmetric
      (fun t ht => hp t (hsub j hj ht)) hju ((hv j hj).2 u hju)
    have hspeed := hu (hsub j hj ⟨hju.1.le,hju.2.le⟩)
    rw [matrixHessianSpeed, ((hv j hj).2 u hju).deriv] at hspeed
    exact (precisionMetric_eq_zero_iff _ _ hpu.inv hsym).mp
      ((Real.sqrt_eq_zero (precisionMetric_nonnegative _ _ hpu.inv hsym)).mp hspeed)
  have hseg j (hj : j < N) (t : ℝ) (ht : t ∈ Set.Icc (a j) (a (j+1))) :
      γ t = γ (a j) := by
    have hsmall : Set.Icc (a j) t ⊆ Set.Icc (a j) (a (j+1)) :=
      Set.Icc_subset_Icc le_rfl ht.2
    have hi : IntervalIntegrable (v j) volume (a j) t := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le ht.1]
      exact (hv j hj).1.mono hsmall
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      (hc.mono (hsmall.trans (hsub j hj)))
      (fun u hu => (hv j hj).2 u ⟨hu.1, hu.2.trans_le ht.2⟩) hi
    have he : (∫ u : ℝ in a j..t, v j u) = 0 := by
      calc
        _ = ∫ _u : ℝ in a j..t, (0 : Matrix n n ℝ) := by
          apply intervalIntegral.integral_congr_ae
          have hn : ∀ᵐ u : ℝ ∂volume, u ≠ t := by simp [ae_iff]
          filter_upwards [hvzero j hj, hn] with u hu hne hut
          rw [Set.uIoc_of_le ht.1] at hut
          exact hu ⟨hut.1, (lt_of_le_of_ne hut.2 hne).trans_le ht.2⟩
        _ = 0 := by simp
    exact sub_eq_zero.mp (hftc.symm.trans he)
  have hind : ∀ j ≤ N, ∀ t ∈ Set.Icc (0:ℝ) (a j), γ t = X := by
    intro j
    induction j with
    | zero =>
      intro _ t ht
      rw [ha0] at ht
      have ht0 : t = 0 := le_antisymm ht.2 ht.1
      simpa [ht0] using h0
    | succ j ih =>
      intro hj t ht
      by_cases hleft : t ≤ a j
      · exact ih (Nat.le_of_succ_le hj) t ⟨ht.1,hleft⟩
      · exact (hseg j (Nat.lt_of_succ_le hj) t ⟨(le_of_not_ge hleft),ht.2⟩).trans
          (ih (Nat.le_of_succ_le hj) (a j) ⟨(ha j (Nat.le_of_succ_le hj)).1,le_rfl⟩)
  exact hind N le_rfl s (by simpa [haN] using hs)

theorem matrix_piecewise_zero_length_constant_speed_unique
    (X Y : Matrix n n ℝ) (γ : ℝ → Matrix n n ℝ)
    (hγ : MatrixPiecewiseAdmissiblePath X Y γ)
    (c : ℝ) (hc : ∀ᵐ u : ℝ ∂volume,
      u ∈ Set.Icc (0:ℝ) 1 → matrixHessianSpeed γ u = c)
    (hlen : matrixHessianPathLength γ = 0)
    (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) : γ s = X := by
  have hi : matrixHessianPathLength γ = c := by
    unfold matrixHessianPathLength
    calc
      _ = ∫ _u : ℝ in (0:ℝ)..1, c := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hc] with u hu hus
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hus
        exact hu ⟨hus.1.le,hus.2⟩
      _ = c := by simp
  have hc0 : c = 0 := hi.symm.trans hlen
  apply matrix_piecewise_zero_speed_constant X Y γ hγ _ s hs
  simpa only [hc0] using hc

/-- The equal-endpoint case of M3 holds in every rank for the actual
finite-piece path class, with constant speed assumed only almost everywhere. -/
theorem matrix_piecewise_equal_endpoint_minimizer_unique
    (X : Matrix n n ℝ) (hX : X.PosDef) (γ : ℝ → Matrix n n ℝ)
    (hγ : MatrixPiecewiseAdmissiblePath X X γ)
    (c : ℝ) (hc : ∀ᵐ u : ℝ ∂volume,
      u ∈ Set.Icc (0:ℝ) 1 → matrixHessianSpeed γ u = c)
    (hmin : matrixHessianPathLength γ = matrixPiecewiseHessianDistance X X)
    (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    γ s = X ∧ γ s = matrixSPDGeodesic X X hX hX s := by
  rw [matrix_piecewise_hessian_distance_self X hX] at hmin
  have he := matrix_piecewise_zero_length_constant_speed_unique X X γ hγ c hc hmin s hs
  refine ⟨he, ?_⟩
  rw [he, matrixSPDGeodesic, matrix_relative_spd_log_self]
  simp [matrixExponentialCurve, hX.posSemidef.sqrt_mul_self]

end
end Sigma
