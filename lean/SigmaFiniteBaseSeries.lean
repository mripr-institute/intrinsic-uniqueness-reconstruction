import Mathlib.RingTheory.PowerSeries.Trunc

namespace Sigma
noncomputable section
open scoped BigOperators

variable {R A : Type*} [CommRing R] [CommRing A]

/-- Evaluation through a finite jet. When `u ^ (N+1) = 0`, the theorem below
shows that every cutoff at least `N+1` gives the same actual finite sum. -/
def finiteSeriesEvaluation (φ : R →+* A) (u : A) (m : ℕ)
    (F : PowerSeries R) : A :=
  (PowerSeries.trunc m F).eval₂ φ u

theorem finite_series_evaluation_sum (φ : R →+* A) (u : A) (m : ℕ)
    (F : PowerSeries R) :
    finiteSeriesEvaluation φ u m F =
      ∑ i ∈ Finset.range m, φ (PowerSeries.coeff R i F) * u^i :=
  PowerSeries.eval₂_trunc_eq_sum_range u φ m F

/-- Nilpotence justifies discarding the entire infinite tail, not merely
the choice of a particular presentation of its finite jet. -/
theorem nilpotent_series_evaluation_stable (φ : R →+* A) (u : A) (N m : ℕ)
    (hu : u^(N+1)=0) (hm : N+1 ≤ m) (F : PowerSeries R) :
    finiteSeriesEvaluation φ u m F=finiteSeriesEvaluation φ u (N+1) F := by
  rw [finite_series_evaluation_sum, finite_series_evaluation_sum]
  symm
  apply Finset.sum_subset (Finset.range_mono hm)
  intro i hi hin
  have hNi : N+1 ≤ i := by simpa only [Finset.mem_range, not_lt] using hin
  rw [pow_eq_zero_of_le hNi hu, mul_zero]

/-- This finite-series evaluation agrees with native polynomial evaluation
even when the polynomial degree exceeds the nilpotence cutoff. -/
theorem nilpotent_series_evaluation_polynomial (φ : R →+* A) (u : A) (N : ℕ)
    (hu : u^(N+1)=0) (P : Polynomial R) :
    finiteSeriesEvaluation φ u (N+1) (P : PowerSeries R)=P.eval₂ φ u := by
  let m := max (N+1) (P.natDegree+1)
  rw [← nilpotent_series_evaluation_stable φ u N m hu (le_max_left _ _)]
  unfold finiteSeriesEvaluation
  rw [PowerSeries.trunc_coe_eq_self]
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)

theorem finite_series_evaluation_tail (φ : R →+* A) (u : A) (N : ℕ)
    (F G : PowerSeries R) :
    finiteSeriesEvaluation φ u (N+1) (F+PowerSeries.X^(N+1)*G)=
      finiteSeriesEvaluation φ u (N+1) F := by
  rw [finite_series_evaluation_sum, finite_series_evaluation_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hz : PowerSeries.coeff R i (PowerSeries.X^(N+1)*G)=0 :=
    PowerSeries.X_pow_dvd_iff.mp (dvd_mul_right _ _) i (Finset.mem_range.mp hi)
  rw [map_add, hz, add_zero]

/-- Every sufficiently long finite evaluation has the same tail ambiguity
at a nilpotent class, with no restrictions on the omitted coefficients. -/
theorem nilpotent_series_evaluation_tail (φ : R →+* A) (u : A) (N m : ℕ)
    (hu : u^(N+1)=0) (hm : N+1 ≤ m) (F G : PowerSeries R) :
    finiteSeriesEvaluation φ u m (F+PowerSeries.X^(N+1)*G)=
      finiteSeriesEvaluation φ u m F := by
  rw [nilpotent_series_evaluation_stable φ u N m hu hm,
    nilpotent_series_evaluation_stable φ u N m hu hm]
  exact finite_series_evaluation_tail φ u N F G

/-- A single nilpotent base cannot recover a complete rational series,
even after its constant coefficient is retained. The two series differ by
the concrete nonzero term `X^(N+1)`. -/
theorem nilpotent_complete_series_nonidentification (φ : ℚ →+* A) (u : A)
    (N : ℕ) (hu : u^(N+1)=0) (F : PowerSeries ℚ) :
    ∃ G : PowerSeries ℚ, G ≠ F ∧
      PowerSeries.constantCoeff ℚ G=PowerSeries.constantCoeff ℚ F ∧
      ∀ m : ℕ, N+1 ≤ m →
        finiteSeriesEvaluation φ u m G=finiteSeriesEvaluation φ u m F := by
  refine ⟨F+PowerSeries.X^(N+1), ?_, ?_, ?_⟩
  · intro he
    have hz : (PowerSeries.X : PowerSeries ℚ)^(N+1)=0 := add_left_cancel (he.trans (add_zero F).symm)
    exact (pow_ne_zero _ PowerSeries.X_ne_zero) hz
  · simp
  · intro m hm
    simpa using nilpotent_series_evaluation_tail φ u N m hu hm F 1

end
end Sigma
