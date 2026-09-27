import SigmaOpBorelInverse
import SigmaProbCompletionSamples

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem BernsteinRepresentation.exponent_nonnegative (B : BernsteinRepresentation)
    {l : ℝ} (hl : 0 ≤ l) : 0 ≤ B.exponent l := by
  have hi : 0 ≤ ∫ x, 1 - Real.exp (-(l * x)) ∂B.levy := by
    apply integral_nonneg_of_ae
    filter_upwards [B.levy_positive_support] with x hx
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hl hx.le)))
  exact add_nonneg (add_nonneg B.killing_nonnegative (mul_nonneg B.drift_nonnegative hl)) hi

/-- Continuity, including the endpoint zero, follows from the literal
Lévy integrability condition by locally uniform domination. -/
theorem BernsteinRepresentation.exponent_continuous (B : BernsteinRepresentation) :
    ContinuousOn B.exponent (Ici 0) := by
  have hI : ContinuousOn (fun l : ℝ => ∫ x, 1 - Real.exp (-(l * x)) ∂B.levy) (Ici 0) := by
    intro l hl
    apply continuousWithinAt_of_dominated (bound := fun x => max 1 (l + 1) * min 1 x)
    · filter_upwards with r
      exact ((continuous_const.sub ((continuous_const.mul continuous_id).neg.rexp)).aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (eventually_lt_nhds (by linarith : l < l + 1))] with r hr hrl
      filter_upwards [B.levy_positive_support] with x hx
      exact (levy_exponent_kernel_bound r x hr hx.le).trans
        (mul_le_mul_of_nonneg_right (max_le_max le_rfl hrl.le) (le_min zero_le_one hx.le))
    · exact B.levy_integrable.const_mul (max 1 (l + 1))
    · filter_upwards with x
      exact (continuous_const.sub ((continuous_id.mul continuous_const).neg.rexp)).continuousWithinAt
  exact (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).add hI

theorem HasBernsteinRepresentation.nonnegative {f : ℝ → ℝ}
    (hf : HasBernsteinRepresentation f) : ∀ l : ℝ, 0 ≤ l → 0 ≤ f l := by
  obtain ⟨B, hB⟩ := hf
  intro l hl
  rw [hB l hl]
  exact B.exponent_nonnegative hl

theorem HasBernsteinRepresentation.continuous {f : ℝ → ℝ}
    (hf : HasBernsteinRepresentation f) : ContinuousOn f (Ici 0) := by
  obtain ⟨B, hB⟩ := hf
  exact B.exponent_continuous.congr (fun l hl => hB l hl)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual native calculus in the paper's existing Bernstein category;
its scalar regularity is derived, not added to the assumptions. -/
def opBernsteinFunctionalCalculus (B : H →ₗ.[ℂ] H) (hsa : IsSelfAdjoint B)
    (hB : OpNonnegative B) (f : ℝ → ℝ) (hf : HasBernsteinRepresentation f)
    (hm : StrictMonoOn f (Ici 0)) : H →ₗ.[ℂ] H :=
  opMonotoneFunctionalCalculus B hsa hB f hf.nonnegative hf.continuous hm

theorem op_bernstein_functional_calculus_selfAdjoint (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) (f : ℝ → ℝ)
    (hf : HasBernsteinRepresentation f) (hm : StrictMonoOn f (Ici 0)) :
    IsSelfAdjoint (opBernsteinFunctionalCalculus B hsa hB f hf hm) :=
  op_monotone_functional_calculus_selfAdjoint B hsa hB f hf.nonnegative hf.continuous hm

theorem op_bernstein_functional_calculus_nonnegative (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) (f : ℝ → ℝ)
    (hf : HasBernsteinRepresentation f) (hm : StrictMonoOn f (Ici 0)) :
    OpNonnegative (opBernsteinFunctionalCalculus B hsa hB f hf hm) :=
  op_monotone_functional_calculus_nonnegative B hsa hB f hf.nonnegative hf.continuous hm

def opKnownBernsteinInverse (C : H →ₗ.[ℂ] H) (hsa : IsSelfAdjoint C)
    (hC : OpNonnegative C) (f : ℝ → ℝ) (hf : HasBernsteinRepresentation f)
    (hm : StrictMonoOn f (Ici 0)) : H →ₗ.[ℂ] H :=
  opKnownMonotoneInverse C hsa hC f hf.nonnegative hf.continuous hm

/-- Exact O6 reconstruction in the paper's original scalar category. -/
theorem op_known_bernstein_inverse_reconstruction (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) (f : ℝ → ℝ)
    (hf : HasBernsteinRepresentation f) (hm : StrictMonoOn f (Ici 0)) :
    opKnownBernsteinInverse (opBernsteinFunctionalCalculus B hsa hB f hf hm)
      (op_bernstein_functional_calculus_selfAdjoint B hsa hB f hf hm)
      (op_bernstein_functional_calculus_nonnegative B hsa hB f hf hm) f hf hm = B :=
  op_known_monotone_inverse_reconstruction B hsa hB f hf.nonnegative hf.continuous hm

theorem op_known_bernstein_inverse_domain (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) (f : ℝ → ℝ)
    (hf : HasBernsteinRepresentation f) (hm : StrictMonoOn f (Ici 0)) :
    (opKnownBernsteinInverse (opBernsteinFunctionalCalculus B hsa hB f hf hm)
      (op_bernstein_functional_calculus_selfAdjoint B hsa hB f hf hm)
      (op_bernstein_functional_calculus_nonnegative B hsa hB f hf hm) f hf hm).domain = B.domain := by
  rw [op_known_bernstein_inverse_reconstruction B hsa hB f hf hm]

theorem op_bernstein_functional_calculus_determines_operator
    (A B : H →ₗ.[ℂ] H) (hsaA : IsSelfAdjoint A) (hsaB : IsSelfAdjoint B)
    (hA : OpNonnegative A) (hB : OpNonnegative B) (f : ℝ → ℝ)
    (hf : HasBernsteinRepresentation f) (hm : StrictMonoOn f (Ici 0))
    (hdata : opBernsteinFunctionalCalculus A hsaA hA f hf hm =
      opBernsteinFunctionalCalculus B hsaB hB f hf hm) : A = B :=
  op_monotone_functional_calculus_determines_operator A B hsaA hsaB hA hB f
    hf.nonnegative hf.continuous hm hdata

end
end Sigma
