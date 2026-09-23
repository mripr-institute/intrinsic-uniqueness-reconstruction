import SigmaOpCanonicalCalculus
import SigmaOpResolvent

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology

theorem laguerre_canonical_positive_shift_resolvent (α : ℝ) (hα : 0 < α) :
    OpIsResolvent laguerreCanonicalOperator (α:ℂ) (laguerreResolvent α hα) := by
  rw [laguerre_canonical_eq_spectral]
  exact ⟨laguerre_resolvent_mem_domain α hα, laguerre_resolvent_right_inverse α hα,
    laguerre_resolvent_left_inverse α hα⟩

theorem laguerre_complete_resolvent_identifies (α : ℝ) (hα : 0 < α)
    (A : LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert)
    (hA : OpIsResolvent A (α:ℂ) (laguerreResolvent α hα)) :
    A = laguerreCanonicalOperator :=
  operator_full_resolvent_unique A _ (α:ℂ) _ hA
    (laguerre_canonical_positive_shift_resolvent α hα)

theorem laguerre_heat_coefficient_bound (τ : ℝ) (hτ : 0 ≤ τ) (n : ℕ) :
    |Real.exp (-τ*(n:ℝ))| ≤ 1 := by
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hτ) (Nat.cast_nonneg n)

/-- The actual bounded heat operator on the original Gamma-weighted L². -/
def laguerreHeatOperator (τ : ℝ) (hτ : 0 ≤ τ) :
    LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert :=
  laguerreBoundedDiagonal (fun n => Real.exp (-τ*(n:ℝ))) 1 zero_le_one
    (laguerre_heat_coefficient_bound τ hτ)

theorem laguerre_heat_coordinate (τ : ℝ) (hτ : 0 ≤ τ) (x : LaguerreWeightedHilbert) (n : ℕ) :
    laguerreHilbertBasis.repr (laguerreHeatOperator τ hτ x) n =
      Complex.ofReal (Real.exp (-τ*(n:ℝ)))*laguerreHilbertBasis.repr x n :=
  laguerre_bounded_diagonal_coordinate _ _ _ _ _ _

/-- Boundedness supplies membership in the full maximal exponential
multiplier domain for every vector, not merely finite spectral sums. -/
theorem laguerre_heat_mem_spectral_domain (τ : ℝ) (hτ : 0 ≤ τ)
    (x : LaguerreWeightedHilbert) :
    x ∈ (laguerreSpectralOperator (fun r => Real.exp (-τ*r))).domain := by
  change Memℓp (fun n : ℕ => (Real.exp (-τ*(n:ℝ)):ℂ)*laguerreHilbertBasis.repr x n) 2
  have he : (fun n : ℕ => (Real.exp (-τ*(n:ℝ)):ℂ)*laguerreHilbertBasis.repr x n) =
      fun n => laguerreHilbertBasis.repr (laguerreHeatOperator τ hτ x) n := by
    funext n
    exact (laguerre_heat_coordinate τ hτ x n).symm
  rw [he]
  exact (laguerreHilbertBasis.repr (laguerreHeatOperator τ hτ x)).property

theorem laguerre_heat_spectral_domain_top (τ : ℝ) (hτ : 0 ≤ τ) :
    (laguerreSpectralOperator (fun r => Real.exp (-τ*r))).domain = ⊤ := by
  apply top_unique
  intro x _
  exact laguerre_heat_mem_spectral_domain τ hτ x

/-- Equality with the canonical exponential functional calculus on its
entire domain, explicitly connecting the bounded semigroup to `exp(-τA)`. -/
theorem laguerre_heat_spectral_action (τ : ℝ) (hτ : 0 ≤ τ)
    (x : (laguerreSpectralOperator (fun r => Real.exp (-τ*r))).domain) :
    laguerreSpectralOperator (fun r => Real.exp (-τ*r)) x =
      laguerreHeatOperator τ hτ x.val := by
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext n
  rw [laguerre_spectral_coordinate, laguerre_heat_coordinate]

theorem laguerre_heat_contracts (τ : ℝ) (hτ : 0 ≤ τ) (x : LaguerreWeightedHilbert) :
    ‖laguerreHeatOperator τ hτ x‖ ≤ ‖x‖ := by
  simpa only [one_mul] using laguerre_bounded_diagonal_norm _ _ _
    (laguerre_heat_coefficient_bound τ hτ) x

theorem laguerre_heat_injective (τ : ℝ) (hτ : 0 ≤ τ) :
    Function.Injective (laguerreHeatOperator τ hτ) := by
  intro x y he
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext n
  have hc := congrArg (fun z : LaguerreWeightedHilbert => laguerreHilbertBasis.repr z n) he
  dsimp only at hc
  rw [laguerre_heat_coordinate, laguerre_heat_coordinate] at hc
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) hc

theorem laguerre_heat_zero :
    laguerreHeatOperator 0 le_rfl = ContinuousLinearMap.id ℂ LaguerreWeightedHilbert := by
  apply ContinuousLinearMap.ext
  intro x
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext n
  simp only [laguerre_heat_coordinate, neg_zero, zero_mul, Real.exp_zero,
    Complex.ofReal_one, one_mul, ContinuousLinearMap.id_apply]

theorem laguerre_heat_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    laguerreHeatOperator (s+t) (add_nonneg hs ht) =
      (laguerreHeatOperator s hs).comp (laguerreHeatOperator t ht) := by
  apply ContinuousLinearMap.ext
  intro x
  apply laguerreHilbertBasis.repr.injective
  apply lp.ext
  funext n
  simp only [ContinuousLinearMap.comp_apply, laguerre_heat_coordinate]
  rw [show -(s+t)*(n:ℝ) = -s*(n:ℝ)+(-t*(n:ℝ)) by ring,
    Real.exp_add, Complex.ofReal_mul, mul_assoc]

def laguerreMarkedHeatSample (T : LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert)
    (n : ℕ) : ℝ := (laguerreHilbertBasis.repr (T (laguerreHilbertBasis n)) n).re

theorem laguerre_heat_sample (τ : ℝ) (hτ : 0 ≤ τ) (n : ℕ) :
    laguerreMarkedHeatSample (laguerreHeatOperator τ hτ) n = Real.exp (-τ*(n:ℝ)) := by
  simp only [laguerreMarkedHeatSample, laguerre_heat_coordinate, HilbertBasis.repr_self,
    lp.single_apply_self, mul_one, Complex.ofReal_re]

theorem laguerre_heat_samples_positive (τ : ℝ) (hτ : 0 ≤ τ) (n : ℕ) :
    0 < laguerreMarkedHeatSample (laguerreHeatOperator τ hτ) n := by
  rw [laguerre_heat_sample]
  exact Real.exp_pos _

theorem laguerre_heat_samples_tendsto_zero (τ : ℝ) (hτ : 0 < τ) :
    Tendsto (laguerreMarkedHeatSample (laguerreHeatOperator τ hτ.le)) atTop (𝓝 0) := by
  have he := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-τ)).le
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hτ))
  convert he using 1
  funext n
  rw [laguerre_heat_sample, ← Real.exp_nat_mul]
  congr 1
  ring

/-- The inverse is read from the marked complete operator itself. It is a
maximal unbounded multiplier, so no positive lower bound on heat eigenvalues
is required. Values away from natural indices are immaterial. -/
def laguerreMarkedHeatInverse (τ : ℝ)
    (T : LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert) :
    LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert :=
  laguerreSpectralOperator (fun r => -Real.log (laguerreMarkedHeatSample T ⌊r⌋₊)/τ)

theorem laguerre_marked_heat_inverse (τ : ℝ) (hτ : 0 < τ) :
    laguerreMarkedHeatInverse τ (laguerreHeatOperator τ hτ.le) = laguerreCanonicalOperator := by
  rw [laguerre_canonical_eq_spectral]
  apply laguerre_spectral_congr
  intro n
  simp only [Nat.floor_natCast, laguerre_heat_sample, Real.log_exp, id_eq]
  field_simp

theorem laguerre_marked_heat_inverse_domain (τ : ℝ) (hτ : 0 < τ) (x : LaguerreWeightedHilbert) :
    x ∈ (laguerreMarkedHeatInverse τ (laguerreHeatOperator τ hτ.le)).domain ↔
      Summable (fun n : ℕ => (n:ℝ)^2*‖laguerreCoefficient x n‖^2) := by
  rw [laguerre_marked_heat_inverse τ hτ]
  exact laguerre_canonical_domain_iff x

end
end Sigma
