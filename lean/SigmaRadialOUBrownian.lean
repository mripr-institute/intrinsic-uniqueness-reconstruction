import SigmaRadialOUNormalization
import SigmaMatrixGaussianMeasure

/-!
The native Brownian category needed for the stochastic clause of R1.
The defining laws concern only Brownian motion: independent Gaussian increments,
zero initial value and continuous paths. No OU law, stochastic integral, Itô
formula or radial SDE is included in the assumptions. Existence is not asserted.
-/

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- Centered Euclidean Gaussian with covariance `v` times the identity, including
the degenerate variance zero case. -/
def radialBrownianGaussian (D : ℕ) (v : ℝ≥0) : Measure (EuclideanSpace ℝ (Fin D)) :=
  (Measure.pi (fun _ : Fin D => gaussianReal 0 v)).map
    (EuclideanSpace.measurableEquiv (Fin D)).symm

instance radial_brownian_gaussian_probability (D : ℕ) (v : ℝ≥0) :
    IsProbabilityMeasure (radialBrownianGaussian D v) :=
  isProbabilityMeasure_map (EuclideanSpace.measurableEquiv (Fin D)).symm.measurable.aemeasurable

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A genuine standard `D`-dimensional Brownian process, on the supplied native
probability space. The increment covariance is precisely elapsed time. -/
structure IsRadialBrownian (D : ℕ) (P : Measure Ω)
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D)) : Prop where
  probability : IsProbabilityMeasure P
  measurable : ∀ t, Measurable (B t)
  zero : ∀ᵐ ω ∂P, B 0 ω = 0
  continuous : ∀ᵐ ω ∂P, Continuous (fun t => B t ω)
  increment_law : ∀ s t : ℝ≥0, s ≤ t →
    P.map (fun ω => B t ω - B s ω) = radialBrownianGaussian D (t-s)
  independent_increments : ∀ (n : ℕ) (t : Fin (n+1) → ℝ≥0), Monotone t →
    iIndepFun (fun _ : Fin n => inferInstance)
      (fun i ω => B (t i.succ) ω - B (t i.castSucc) ω) P

theorem radial_brownian_time_law {D : ℕ} {P : Measure Ω}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D)}
    (hB : IsRadialBrownian D P B) (t : ℝ≥0) :
    P.map (B t) = radialBrownianGaussian D t := by
  have he : P.map (B t) = P.map (fun ω => B t ω - B 0 ω) :=
    Measure.map_congr (hB.zero.mono fun ω h => by simp [h])
  rw [he, hB.increment_law 0 t (zero_le _), tsub_zero]

theorem radial_brownian_stationary_increments {D : ℕ} {P : Measure Ω}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D)}
    (hB : IsRadialBrownian D P B) (s t : ℝ≥0) :
    P.map (fun ω => B (s+t) ω - B s ω) = P.map (B t) := by
  rw [hB.increment_law s (s+t) (le_add_of_nonneg_right (zero_le _)),
    add_tsub_cancel_left, radial_brownian_time_law hB]

/-- Every finite partition has the actual product Gaussian increment law. -/
theorem radial_brownian_increment_joint_law {D : ℕ} {P : Measure Ω}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D)}
    (hB : IsRadialBrownian D P B) (n : ℕ) (t : Fin (n+1) → ℝ≥0)
    (ht : Monotone t) :
    P.map (fun ω (i : Fin n) => B (t i.succ) ω - B (t i.castSucc) ω) =
      Measure.pi (fun i : Fin n => radialBrownianGaussian D (t i.succ-t i.castSucc)) := by
  classical
  letI := hB.probability
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (measurable_pi_lambda _ (fun i =>
    (hB.measurable _).sub (hB.measurable _)))
    (MeasurableSet.pi (Set.to_countable univ) (fun i _ => hs i))]
  have he : (fun ω (i : Fin n) => B (t i.succ) ω - B (t i.castSucc) ω) ⁻¹'
      Set.pi univ s = ⋂ i ∈ Finset.univ, (fun ω =>
        B (t i.succ) ω - B (t i.castSucc) ω) ⁻¹' s i := by
    ext ω
    simp
  rw [he, (hB.independent_increments n t ht).measure_inter_preimage_eq_mul
    Finset.univ (fun i _ => hs i)]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Measure.map_apply ((hB.measurable _).sub (hB.measurable _)) (hs i),
    hB.increment_law _ _ (ht (by exact Nat.le_succ i.val))]

/-- Adaptedness to the actual natural filtration is derived from coordinate
measurability, without supplying a filtration as an extra identifying mark. -/
theorem radial_brownian_naturally_adapted {D : ℕ} {P : Measure Ω}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D)} (hB : IsRadialBrownian D P B) :
    Adapted (Filtration.natural B (fun t => (hB.measurable t).stronglyMeasurable)) B :=
  Filtration.adapted_natural _

end
end Sigma
