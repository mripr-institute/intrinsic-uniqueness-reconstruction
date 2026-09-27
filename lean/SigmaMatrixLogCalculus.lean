import SigmaMatrixLogInverse
import SigmaMatrixExpFrechet
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace Sigma
noncomputable section
open Filter Set
open scoped Matrix Topology
variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

omit [Fintype n] [DecidableEq n] in
private theorem matrix_transpose_continuous :
    Continuous (fun M : Matrix n n ℝ => Mᵀ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  change Continuous (fun M : Matrix n n ℝ => M j i)
  exact (continuous_apply i).comp (continuous_apply j)

/-- The local inverse supplied by the ordinary full-matrix inverse function
theorem agrees with the native SPD logarithm on all nearby SPD matrices.
Transposition and local injectivity force this inverse to be symmetric. -/
theorem matrix_exp_local_inverse_eq_log (A : Matrix n n ℝ) (hA : A.PosDef)
    (e : Matrix n n ℝ ≃L[ℝ] Matrix n n ℝ)
    (he : (e : Matrix n n ℝ →L[ℝ] Matrix n n ℝ) =
      matrixExpDifferential (matrixSPDLog A hA)) :
    let hf : HasStrictFDerivAt (NormedSpace.exp ℝ)
        (e : Matrix n n ℝ →L[ℝ] Matrix n n ℝ) (matrixSPDLog A hA) :=
      he.symm ▸ matrix_exp_hasStrictFDerivAt (matrixSPDLog A hA)
    ∀ᶠ B in 𝓝 A, B.PosDef →
      hf.localInverse (NormedSpace.exp ℝ) e (matrixSPDLog A hA) B = CFC.log B := by
  let Z := matrixSPDLog A hA
  let hf : HasStrictFDerivAt (NormedSpace.exp ℝ)
      (e : Matrix n n ℝ →L[ℝ] Matrix n n ℝ) Z :=
    he.symm ▸ matrix_exp_hasStrictFDerivAt Z
  let g := hf.localInverse (NormedSpace.exp ℝ) e Z
  let L := hf.toPartialHomeomorph (NormedSpace.exp ℝ)
  have hexp : NormedSpace.exp ℝ Z = A := matrix_exp_spd_log A hA
  have hZ : Zᵀ = Z := matrix_spd_log_symmetric A hA
  have hg : Tendsto g (𝓝 A) (𝓝 Z) := by
    simpa only [hexp] using hf.localInverse_tendsto
  have hgT : Tendsto (fun B => (g B)ᵀ) (𝓝 A) (𝓝 Z) := by
    have h := matrix_transpose_continuous.continuousAt.tendsto.comp hg
    simpa only [hZ, Function.comp_def] using h
  have hn : L.source ∈ 𝓝 Z := L.open_source.mem_nhds hf.mem_toPartialHomeomorph_source
  have hs := hg.eventually hn
  have hsT := hgT.eventually hn
  have hr : ∀ᶠ B in 𝓝 A, NormedSpace.exp ℝ (g B) = B := by
    simpa only [hexp] using hf.eventually_right_inverse
  filter_upwards [hs, hsT, hr] with B hBsource hBTsource hright hB
  have hBsymm : Bᵀ = B := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hB.isHermitian.eq
  have hgsymm : (g B).IsSymm := by
    apply L.injOn hBTsource hBsource
    change NormedSpace.exp ℝ (g B)ᵀ = NormedSpace.exp ℝ (g B)
    rw [Matrix.exp_transpose, hright, hBsymm]
  have hu := matrix_symmetric_log_unique B (g B) hB hgsymm hright
  simpa only [matrix_spd_log_eq_cfc_log B hB] using hu

/-- An invertible native exponential differential gives continuity of the
actual logarithm within the SPD locus, without assumptions on eigenbases. -/
theorem matrix_cfc_log_continuousWithinAt (A : Matrix n n ℝ) (hA : A.PosDef)
    (e : Matrix n n ℝ ≃L[ℝ] Matrix n n ℝ)
    (he : (e : Matrix n n ℝ →L[ℝ] Matrix n n ℝ) =
      matrixExpDifferential (matrixSPDLog A hA)) :
    ContinuousWithinAt (CFC.log : Matrix n n ℝ → Matrix n n ℝ)
      {B | B.PosDef} A := by
  let hf : HasStrictFDerivAt (NormedSpace.exp ℝ)
      (e : Matrix n n ℝ →L[ℝ] Matrix n n ℝ) (matrixSPDLog A hA) :=
    he.symm ▸ matrix_exp_hasStrictFDerivAt (matrixSPDLog A hA)
  have hcont : ContinuousAt
      (hf.localInverse (NormedSpace.exp ℝ) e (matrixSPDLog A hA)) A := by
    simpa only [matrix_exp_spd_log] using hf.localInverse_continuousAt
  have hEq := matrix_exp_local_inverse_eq_log A hA e he
  have hEq' : (CFC.log : Matrix n n ℝ → Matrix n n ℝ) =ᶠ[𝓝[{B | B.PosDef}] A]
      hf.localInverse (NormedSpace.exp ℝ) e (matrixSPDLog A hA) := by
    filter_upwards [hEq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with B hb hpos
    exact (hb hpos).symm
  exact hcont.continuousWithinAt.congr_of_eventuallyEq_of_mem hEq' hA

/-- The inverse-function chain rule for a differentiable SPD path. The only
operator input is the actual invertible exponential differential. -/
theorem matrix_spd_log_path_hasDerivAt
    (γ : ℝ → Matrix n n ℝ) (hpos : ∀ t, (γ t).PosDef)
    (s : ℝ) (U : Matrix n n ℝ) (hγ : HasDerivAt γ U s)
    (e : Matrix n n ℝ ≃L[ℝ] Matrix n n ℝ)
    (he : (e : Matrix n n ℝ →L[ℝ] Matrix n n ℝ) =
      matrixExpDifferential (matrixSPDLog (γ s) (hpos s))) :
    HasDerivAt (fun t => matrixSPDLog (γ t) (hpos t)) (e.symm U) s := by
  let Z := matrixSPDLog (γ s) (hpos s)
  let hf : HasStrictFDerivAt (NormedSpace.exp ℝ)
      (e : Matrix n n ℝ →L[ℝ] Matrix n n ℝ) Z :=
    he.symm ▸ matrix_exp_hasStrictFDerivAt Z
  let g := hf.localInverse (NormedSpace.exp ℝ) e Z
  have hdg : HasFDerivAt g (e.symm : Matrix n n ℝ →L[ℝ] Matrix n n ℝ) (γ s) := by
    simpa only [Z, matrix_exp_spd_log] using hf.to_localInverse.hasFDerivAt
  have hcomp := hdg.comp_hasDerivAt s hγ
  have hEq := matrix_exp_local_inverse_eq_log (γ s) (hpos s) e he
  have hEq' : (fun t => matrixSPDLog (γ t) (hpos t)) =ᶠ[𝓝 s] (fun t => g (γ t)) := by
    filter_upwards [hγ.continuousAt.tendsto.eventually hEq] with t ht
    rw [matrix_spd_log_eq_cfc_log]
    exact (ht (hpos t)).symm
  exact hcomp.congr_of_eventuallyEq hEq'

/-- Continuity of the native logarithm along a continuous SPD path follows
from the local inverse, without imposing regularity of the chosen eigenbasis. -/
theorem matrix_spd_log_path_continuousWithinAt
    (γ : ℝ → Matrix n n ℝ) (hpos : ∀ t, (γ t).PosDef)
    (s : ℝ) (S : Set ℝ) (hγ : ContinuousWithinAt γ S s)
    (e : Matrix n n ℝ ≃L[ℝ] Matrix n n ℝ)
    (he : (e : Matrix n n ℝ →L[ℝ] Matrix n n ℝ) =
      matrixExpDifferential (matrixSPDLog (γ s) (hpos s))) :
    ContinuousWithinAt (fun t => matrixSPDLog (γ t) (hpos t)) S s := by
  have h := (matrix_cfc_log_continuousWithinAt (γ s) (hpos s) e he).comp hγ
    (fun t _ => hpos t)
  have heq : (fun t => matrixSPDLog (γ t) (hpos t)) = fun t => CFC.log (γ t) := by
    funext t
    exact matrix_spd_log_eq_cfc_log _ _
  rw [heq]
  exact h

theorem matrix_spd_log_path_continuousOn
    (γ : ℝ → Matrix n n ℝ) (hpos : ∀ t, (γ t).PosDef)
    (S : Set ℝ) (hγ : ContinuousOn γ S)
    (e : ℝ → (Matrix n n ℝ ≃L[ℝ] Matrix n n ℝ))
    (he : ∀ s ∈ S, (e s : Matrix n n ℝ →L[ℝ] Matrix n n ℝ) =
      matrixExpDifferential (matrixSPDLog (γ s) (hpos s))) :
    ContinuousOn (fun t => matrixSPDLog (γ t) (hpos t)) S := by
  intro s hs
  exact matrix_spd_log_path_continuousWithinAt γ hpos s S (hγ s hs) (e s) (he s hs)

end
end Sigma
