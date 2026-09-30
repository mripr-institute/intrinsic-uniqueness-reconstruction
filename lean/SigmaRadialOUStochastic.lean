import SigmaItoLevyFoundations

/-!
R1's radial stochastic equation from the general foundations retained in the
paper. No radial Itô formula, Brownian property of the normalized integral, or
OU conclusion is a field of those foundations: each is derived here.
-/

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] {D : ℕ} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
  {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D)}

namespace BrownianItoLevyCalculus

variable (C : BrownianItoLevyCalculus D P ℱ B)

/-- Every progressive unit-vector integrand produces a genuine real Brownian
motion. The compensator is computed as the actual integral of its squared norm. -/
theorem unit_integral_brownian (H : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D))
    (hH : ProgMeasurable ℱ H) (hn : ∀ t ω, ‖H t ω‖ = 1) :
    IsScalarBrownian P (C.vectorIntegral H) := by
  have hb : UniformlyBoundedProcess H := ⟨1, fun t ω => (hn t ω).le⟩
  apply C.levy _ (C.bounded_integral_martingale H hH hb) _
    (C.bounded_integral_continuous H hH hb) (C.bounded_integral_zero H hH hb)
  simpa only [hn, one_pow, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    using C.bounded_integral_compensator H hH hb

theorem normalized_integral_brownian (Z : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D))
    (hZ : ProgMeasurable ℱ Z) (e : EuclideanSpace ℝ (Fin D)) (he : ‖e‖ = 1) :
    IsScalarBrownian P (C.vectorIntegral (fun t ω => radialOUNormalize e (Z t ω))) :=
  C.unit_integral_brownian _ (radial_ou_normalize_progressive ℱ Z hZ e)
    (fun t ω => radial_ou_normalize_norm e (Z t ω) he)

/-- Native differentiation of the energy; this supplies the gradient premise
of the general Itô theorem. -/
theorem energy_hasFDerivAt (x : EuclideanSpace ℝ (Fin D)) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin D) => ‖y‖^2/2) (innerSL ℝ x) x := by
  simpa using radial_energy_hasFDerivAt (fun t : ℝ => t) x (differentiableAt_id)

theorem energy_laplacian (x : EuclideanSpace ℝ (Fin D)) :
    euclideanLaplacian (EuclideanSpace.basisFun (Fin D) ℝ)
      (fun y => ‖y‖^2/2) x = (D : ℝ) := by
  simpa using radial_energy_euclidean_laplacian
    (EuclideanSpace.basisFun (Fin D) ℝ) (fun t : ℝ => t)
    (fun _ _ => differentiableAt_id) x (by simpa using differentiableAt_const (c := (1 : ℝ)))

/-- Itô applied to the actual energy of any specified OU solution, in every
dimension. The drift is calculated from native Fréchet and second derivatives. -/
theorem radial_ou_energy_ito (Z : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D))
    (hZ : ProgMeasurable ℱ Z)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω))
    (hOU : AdditiveBrownianEquation P B Z (fun t ω => -(1/2 : ℝ) • Z t ω)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ‖Z t ω‖^2/2 = ‖Z 0 ω‖^2/2 +
        (∫ s in (0 : ℝ)..(t : ℝ), (D : ℝ)/2 - ‖Z s.toNNReal ω‖^2/2) +
        C.vectorIntegral Z t ω := by
  have ha : ProgMeasurable ℱ (fun t ω => -(1/2 : ℝ) • Z t ω) :=
    fun t => (hZ t).const_smul _
  have hac : ∀ᵐ ω ∂P, Continuous (fun t => -(1/2 : ℝ) • Z t ω) :=
    hc.mono fun ω hω => hω.const_smul _
  have hf : ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin D) => ‖x‖^2/2) :=
    (contDiff_norm_sq ℝ).div_const 2
  have hi := C.ito Z (fun t ω => -(1/2 : ℝ) • Z t ω)
    (fun x => ‖x‖^2/2) id hZ hc ha hac hOU hf energy_hasFDerivAt
  have hd (x : EuclideanSpace ℝ (Fin D)) :
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin D) => ‖y‖^2/2) x (-(1/2 : ℝ) • x) +
        (1/2 : ℝ) * euclideanLaplacian (EuclideanSpace.basisFun (Fin D) ℝ)
          (fun y => ‖y‖^2/2) x = (D : ℝ)/2 - ‖x‖^2/2 := by
    rw [(energy_hasFDerivAt x).fderiv, energy_laplacian]
    simp only [innerSL_apply, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  simpa only [hd, id_eq] using hi

/-- The scalar stochastic integral agrees with the original vector integral,
including when the OU position is zero. -/
theorem radial_ou_integral_substitution (Z : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D))
    (hZ : ProgMeasurable ℱ Z)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω))
    (e : EuclideanSpace ℝ (Fin D)) (he : ‖e‖ = 1) :
    ∀ᵐ ω ∂P, ∀ t,
      C.scalarIntegral (C.vectorIntegral (fun s ω => radialOUNormalize e (Z s ω)))
        (fun s ω => Real.sqrt (2 * (‖Z s ω‖^2/2))) t ω = C.vectorIntegral Z t ω := by
  have hn (s : ℝ≥0) (ω : Ω) : Real.sqrt (2 * (‖Z s ω‖^2/2)) = ‖Z s ω‖ := by
    rw [show 2 * (‖Z s ω‖^2/2) = ‖Z s ω‖^2 by ring, Real.sqrt_sq (norm_nonneg _)]
  have hp : ProgMeasurable ℱ (fun s ω => Real.sqrt (2 * (‖Z s ω‖^2/2))) := by
    simp only [hn]
    exact fun t => (hZ t).norm
  have hpc : ∀ᵐ ω ∂P, Continuous (fun s => Real.sqrt (2 * (‖Z s ω‖^2/2))) := by
    simp only [hn]
    exact hc.mono fun ω hω => hω.norm
  have hi := C.substitution (fun s ω => radialOUNormalize e (Z s ω))
    (fun s ω => Real.sqrt (2 * (‖Z s ω‖^2/2)))
    (radial_ou_normalize_progressive ℱ Z hZ e)
    ⟨1, fun s ω => (radial_ou_normalize_norm e (Z s ω) he).le⟩ hp hpc
  simpa only [radial_ou_normalize_energy_reconstruct] using hi

/-- R1's stochastic clause, in general positive dimension with a designated
unit vector at zero. The Brownian driver and integral equation are conclusions. -/
theorem radial_ou_stochastic_equation (Z : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin D))
    (hZ : ProgMeasurable ℱ Z)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω))
    (hOU : AdditiveBrownianEquation P B Z (fun t ω => -(1/2 : ℝ) • Z t ω))
    (e : EuclideanSpace ℝ (Fin D)) (he : ‖e‖ = 1) :
    ∃ β : ℝ≥0 → Ω → ℝ, IsScalarBrownian P β ∧
      β = C.vectorIntegral (fun s ω => radialOUNormalize e (Z s ω)) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ‖Z t ω‖^2/2 = ‖Z 0 ω‖^2/2 +
          (∫ s in (0 : ℝ)..(t : ℝ), (D : ℝ)/2 - ‖Z s.toNNReal ω‖^2/2) +
          C.scalarIntegral β (fun s ω => Real.sqrt (2 * (‖Z s ω‖^2/2))) t ω := by
  refine ⟨_, C.normalized_integral_brownian Z hZ e he, rfl, ?_⟩
  filter_upwards [C.radial_ou_energy_ito Z hZ hc hOU,
    C.radial_ou_integral_substitution Z hZ hc e he] with ω hω hs
  intro t
  rw [hs t]
  exact hω t

end BrownianItoLevyCalculus

/-- The dimension-four assertion in the paper: dT=(2-T)dt+√(2T)dβ,
for a genuine one-dimensional Brownian motion, on the supplied probability
space and with one common full-measure event for the integral equation. -/
theorem radial_four_ou_stochastic_equation
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 4)}
    (C : BrownianItoLevyCalculus 4 P ℱ B)
    (Z : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 4)) (hZ : ProgMeasurable ℱ Z)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω))
    (hOU : AdditiveBrownianEquation P B Z (fun t ω => -(1/2 : ℝ) • Z t ω)) :
    ∃ β : ℝ≥0 → Ω → ℝ, IsScalarBrownian P β ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ‖Z t ω‖^2/2 = ‖Z 0 ω‖^2/2 +
          (∫ s in (0 : ℝ)..(t : ℝ), 2 - ‖Z s.toNNReal ω‖^2/2) +
          C.scalarIntegral β (fun s ω => Real.sqrt (2 * (‖Z s ω‖^2/2))) t ω := by
  obtain ⟨β, hβ, _, heq⟩ := C.radial_ou_stochastic_equation Z hZ hc hOU
    (EuclideanSpace.single (0 : Fin 4) 1) (by simp)
  refine ⟨β, hβ, ?_⟩
  norm_num only [Nat.cast_ofNat, show (4 : ℝ)/2 = 2 by norm_num] at heq
  exact heq

end
end Sigma
