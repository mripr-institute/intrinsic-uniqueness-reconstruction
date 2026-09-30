import SigmaRadialBrownianSelfIntegral
import Mathlib.Probability.Martingale.Basic

/-!
The general stochastic-calculus foundations retained by R1 in the paper.
These are explicit hypotheses, not newly declared Lean axioms. They are
universal Itô, bounded-integrand martingale, substitution and Lévy theorems;
none mentions OU, radial energy, normalization, or dimension four.

The processes, measures, filtrations, conditional-expectation martingales,
Gaussian laws, Bochner integrals and Fréchet derivatives are native objects.
The supplied stochastic integral also agrees with actual left-point sums for
continuous progressive integrands. Construction of this general calculus is
outside this interface, as explicitly permitted by the paper's foundations.
-/

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Standard real Brownian motion, expressed by its actual probability laws. -/
structure IsScalarBrownian (P : Measure Ω) (β : ℝ≥0 → Ω → ℝ) : Prop where
  probability : IsProbabilityMeasure P
  measurable : ∀ t, Measurable (β t)
  zero : ∀ᵐ ω ∂P, β 0 ω = 0
  continuous : ∀ᵐ ω ∂P, Continuous (fun t => β t ω)
  increment_law : ∀ s t : ℝ≥0, s ≤ t →
    P.map (fun ω => β t ω - β s ω) = gaussianReal 0 (t-s)
  independent_increments : ∀ (n : ℕ) (t : Fin (n+1) → ℝ≥0), Monotone t →
    iIndepFun (fun _ : Fin n => inferInstance)
      (fun i ω => β (t i.succ) ω - β (t i.castSucc) ω) P

/-- Uniform boundedness in both time and sample; used only for the general
square-integrable martingale theorem, not imposed on the OU process. -/
def UniformlyBoundedProcess {V : Type*} [Norm V] (H : ℝ≥0 → Ω → V) : Prop :=
  ∃ C : ℝ, ∀ t ω, ‖H t ω‖ ≤ C

def brownianLeftSum {D : ℕ} (B H : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D))
    (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i : Fin n, ⟪H (radialBrownianUniformTimes T n i.castSucc) ω,
    B (radialBrownianUniformTimes T n i.succ) ω -
      B (radialBrownianUniformTimes T n i.castSucc) ω⟫_ℝ

/-- A specified additive-noise SDE, with a common full-measure event for all
times. This is the input process equation, not an equation for a function of it. -/
def AdditiveBrownianEquation {D : ℕ} (P : Measure Ω)
    (B X a : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D)) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
    X t ω = X 0 ω + B t ω + ∫ s in (0 : ℝ)..(t : ℝ), a s.toNNReal ω

/-- General foundations on a supplied filtered Brownian probability space.
`vectorIntegral H` denotes ∫ H·dB, and `scalarIntegral M h` denotes ∫ h dM.
The local Itô/substitution laws allow unbounded continuous integrands. -/
structure BrownianItoLevyCalculus (D : ℕ) (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D)) where
  brownian : IsRadialBrownian D P B
  adapted : Adapted ℱ B
  vectorIntegral : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D)) → ℝ≥0 → Ω → ℝ
  scalarIntegral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ
  continuous_integral_limit : ∀ H, ProgMeasurable ℱ H →
    (∀ᵐ ω ∂P, Continuous (fun t => H t ω)) → ∀ T,
    TendstoInMeasure P (brownianLeftSum B H T) atTop (vectorIntegral H T)
  bounded_integral_martingale : ∀ H, ProgMeasurable ℱ H → UniformlyBoundedProcess H →
    Martingale (vectorIntegral H) ℱ P
  bounded_integral_compensator : ∀ H, ProgMeasurable ℱ H → UniformlyBoundedProcess H →
    Martingale (fun t ω => (vectorIntegral H t ω)^2 -
      ∫ s in (0 : ℝ)..(t : ℝ), ‖H s.toNNReal ω‖^2) ℱ P
  bounded_integral_continuous : ∀ H, ProgMeasurable ℱ H → UniformlyBoundedProcess H →
    ∀ᵐ ω ∂P, Continuous (fun t => vectorIntegral H t ω)
  bounded_integral_zero : ∀ H, ProgMeasurable ℱ H → UniformlyBoundedProcess H →
    ∀ᵐ ω ∂P, vectorIntegral H 0 ω = 0
  ito : ∀ (X a : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D))
    (F : EuclideanSpace ℝ (Fin D) → ℝ)
    (g : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D)),
    ProgMeasurable ℱ X → (∀ᵐ ω ∂P, Continuous (fun t => X t ω)) →
    ProgMeasurable ℱ a → (∀ᵐ ω ∂P, Continuous (fun t => a t ω)) →
    AdditiveBrownianEquation P B X a → ContDiff ℝ 2 F →
    (∀ x, HasFDerivAt F (innerSL ℝ (g x)) x) →
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      F (X t ω) = F (X 0 ω) +
        (∫ s in (0 : ℝ)..(t : ℝ),
          fderiv ℝ F (X s.toNNReal ω) (a s.toNNReal ω) +
            (1/2 : ℝ) * euclideanLaplacian (EuclideanSpace.basisFun (Fin D) ℝ)
              F (X s.toNNReal ω)) +
        vectorIntegral (fun s ω => g (X s ω)) t ω
  substitution : ∀ H h, ProgMeasurable ℱ H → UniformlyBoundedProcess H →
    ProgMeasurable ℱ h → (∀ᵐ ω ∂P, Continuous (fun t => h t ω)) →
    ∀ᵐ ω ∂P, ∀ t,
      scalarIntegral (vectorIntegral H) h t ω =
        vectorIntegral (fun s ω => h s ω • H s ω) t ω
  levy : ∀ M : ℝ≥0 → Ω → ℝ, Martingale M ℱ P →
    Martingale (fun t ω => (M t ω)^2 - (t : ℝ)) ℱ P →
    (∀ᵐ ω ∂P, Continuous (fun t => M t ω)) → (∀ᵐ ω ∂P, M 0 ω = 0) →
    IsScalarBrownian P M

end
end Sigma
