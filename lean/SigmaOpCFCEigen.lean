import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

namespace Sigma
noncomputable section
open scoped Topology ContinuousFunctionalCalculus
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Continuous functional calculus acts on every eigenvector, without a
complete eigenbasis or a pure-point-spectrum hypothesis. -/
theorem op_cfc_eigenvector (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (a : ℝ) (ha : a ∈ spectrum ℝ R) (x : H) (hx : R x = (a : ℂ) • x)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ R)) :
    cfc f R x = (f a : ℂ) • x := by
  let z : spectrum ℝ R := ⟨a, ha⟩
  have hc : Continuous (fun g : C(spectrum ℝ R, ℝ) => cfcHom hR g x) :=
    (cfcHom_continuous hR).clm_apply continuous_const
  have he : Continuous (fun g : C(spectrum ℝ R, ℝ) => (g z : ℂ) • x) := by
    fun_prop
  have hclosed : IsClosed {g : C(spectrum ℝ R, ℝ) |
      cfcHom hR g x = (g z : ℂ) • x} := isClosed_eq hc he
  have hall (g : C(spectrum ℝ R, ℝ)) : cfcHom hR g x = (g z : ℂ) • x := by
    induction g using ContinuousMap.induction_on_of_compact with
    | const r =>
      rw [show cfcHom hR (ContinuousMap.const (spectrum ℝ R) r) =
        algebraMap ℝ (H →L[ℂ] H) r from (cfcHom hR).commutes r]
      simp [z, Algebra.algebraMap_eq_smul_one]
    | id => simpa [cfcHom_id, z] using hx
    | star_id =>
      rw [star_trivial, cfcHom_id]
      exact hx
    | add f g hf hg => simp only [map_add, ContinuousLinearMap.add_apply,
        ContinuousMap.add_apply, Complex.ofReal_add, add_smul, hf, hg]
    | mul f g hf hg =>
      simp only [map_mul, ContinuousLinearMap.mul_apply, hg, map_smul,
        hf, ContinuousMap.mul_apply, Complex.ofReal_mul, smul_smul]
      congr 1
      ring
    | frequently g hg => exact hclosed.mem_of_frequently_of_tendsto hg Filter.tendsto_id
  simpa only [cfc_apply f R hR hf] using hall ⟨_, hf.restrict⟩

theorem op_eigenvalue_mem_spectrum (R : H →L[ℂ] H) (a : ℝ)
    (x : H) (hx0 : x ≠ 0) (hx : R x = (a : ℂ) • x) :
    a ∈ spectrum ℝ R := by
  rw [spectrum.mem_iff]
  intro hu
  have hinj := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).injective
  apply hx0
  apply hinj
  simp [Algebra.algebraMap_eq_smul_one, hx]

theorem op_cfc_eigenvector_action (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (a : ℝ) (x : H) (hx : R x = (a : ℂ) • x)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ R)) :
    cfc f R x = (f a : ℂ) • x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · exact op_cfc_eigenvector R hR a (op_eigenvalue_mem_spectrum R a x hx0 hx) x hx f hf

end
end Sigma
