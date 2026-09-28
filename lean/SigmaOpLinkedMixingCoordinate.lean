import SigmaOpNonnegativeMixingFinal
import SigmaOperatorPearsonRepresentative

namespace Sigma
noncomputable section
open MeasureTheory Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- When the unknown coordinate probability is explicitly linked to the
mixing measure, the actual operator identity and integer eigenvectors recover
the coordinate law. The link is genuine retained information. -/
theorem op_linked_coordinate_probability_unique
    (B : H →ₗ.[ℂ] H) (hsa : IsSelfAdjoint B) (hB : OpNonnegative B)
    (heigen : ∀ n : ℕ, ∃ x : B.domain, x.val ≠ 0 ∧ B x = (n : ℂ) • x.val)
    (μ : ComplexMeasure OpNonnegativeRay) (ν : Measure OpNonnegativeRay)
    [IsProbabilityMeasure ν]
    (hlink : μ = ν.toSignedMeasure.toComplexMeasure 0)
    (hmix : ∀ x : H,
      complexStrongIntegral μ (fun s => opNonnegativeHeat B hsa hB s.val x) =
        opNonnegativeResolvent B hsa hB (opNonnegativeResolvent B hsa hB x)) :
    ν = nonnegativeGammaMixingMeasure ∧
      ν.map (fun s : OpNonnegativeRay => (s : ℝ)) = gammaProbability := by
  have hμ := (op_nonnegative_complex_mixing_iff B hsa hB heigen μ).mp hmix
  have hs : ν.toSignedMeasure = nonnegativeGammaMixingMeasure.toSignedMeasure := by
    have hh := congrArg ComplexMeasure.re (hlink.symm.trans hμ)
    simpa only [nonnegativeGammaComplexMeasure,
      SignedMeasure.re_toComplexMeasure] using hh
  have hν : ν = nonnegativeGammaMixingMeasure := by
    apply Measure.ext
    intro E hE
    have he := congrArg (fun ρ : SignedMeasure OpNonnegativeRay => ρ E) hs
    dsimp only at he
    rw [Measure.toSignedMeasure_apply_measurable hE,
      Measure.toSignedMeasure_apply_measurable hE] at he
    calc
      ν E = ENNReal.ofReal (ν E).toReal :=
        (ENNReal.ofReal_toReal (measure_ne_top ν E)).symm
      _ = ENNReal.ofReal (nonnegativeGammaMixingMeasure E).toReal := by rw [he]
      _ = nonnegativeGammaMixingMeasure E :=
        ENNReal.ofReal_toReal (measure_ne_top nonnegativeGammaMixingMeasure E)
  exact ⟨hν, hν ▸ nonnegative_gamma_mixing_on_real_line⟩

/-- The second identification route uses the paper's actual locally AC
Pearson realization of a normalized coordinate density. -/
theorem op_pearson_coordinate_probability_unique
    (a b w : ℝ → ℝ)
    (hw : LocallyIntegralAbsolutelyContinuousPositive w)
    (hmass : (∫ t : ℝ in Ioi 0, w t) = 1)
    (hl : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      opExpression a b opLinearProbe t = 2 - t)
    (hq : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      opExpression a b opQuadraticProbe t = t ^ 2 - 6 * t + 6)
    (hP : HasLocalACPearsonFlux a b w)
    (ν : Measure ℝ)
    (hcoord : ν = volume.withDensity
      ((Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal (w t)))) :
    ν = gammaProbability := by
  exact hcoord.trans
    (operator_two_probe_pearson_representative_inverse_ae a b w hw hmass hl hq hP).2.2

end
end Sigma
