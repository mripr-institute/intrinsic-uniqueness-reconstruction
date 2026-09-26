import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace Sigma
noncomputable section
open Filter
open scoped Topology BigOperators

/-- An antiderivative of an exponential, including the zero exponent. This
uniformly encodes zeta samples and the logarithm of a zeta determinant. -/
def finiteInvariantPrimitive (a x : ℝ) : ℝ :=
  if a = 0 then x else Real.exp (a * x) / a

theorem finite_invariant_primitive_derivative (a x : ℝ) :
    HasStrictDerivAt (finiteInvariantPrimitive a) (Real.exp (a*x)) x := by
  change HasStrictDerivAt (fun y => if a = 0 then y else Real.exp (a*y)/a) _ _
  by_cases ha : a = 0
  · subst a
    simpa [finiteInvariantPrimitive] using hasStrictDerivAt_id x
  · simpa [finiteInvariantPrimitive, ha, mul_div_cancel_right₀ _ ha] using
      (((hasStrictDerivAt_id x).const_mul a).exp.div_const a)

def finiteInvariantMap {n : ℕ} (a : Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j, finiteInvariantPrimitive (a i) (x j)

def finiteInvariantDerivative {n : ℕ} (a x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => ∑ j, Real.exp (a i*x j) •
    ContinuousLinearMap.proj j

theorem finite_invariant_map_derivative {n : ℕ} (a x : Fin n → ℝ) :
    HasStrictFDerivAt (finiteInvariantMap a) (finiteInvariantDerivative a x) x := by
  apply hasStrictFDerivAt_pi.mpr
  intro i
  apply HasStrictFDerivAt.sum
  intro j _
  exact (finite_invariant_primitive_derivative (a i) (x j)).comp_hasStrictFDerivAt
    (𝕜 := ℝ) x (hasStrictFDerivAt_apply j x)

def finiteInvariantBase (n : ℕ) : Fin n → ℝ :=
  fun j => ((j : ℝ)+1)*Real.log 2

theorem finite_invariant_matrix {n : ℕ} (a : Fin n → ℝ) :
    (fun i j => Real.exp (a i * finiteInvariantBase n j)) =
      Matrix.diagonal (fun i => Real.exp (a i*Real.log 2)) *
        Matrix.vandermonde (fun i => Real.exp (a i*Real.log 2)) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.vandermonde_apply, finiteInvariantBase]
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

theorem finite_invariant_matrix_det_ne_zero {n : ℕ} (a : Fin n → ℝ)
    (ha : Function.Injective a) :
    Matrix.det (fun i j => Real.exp (a i * finiteInvariantBase n j)) ≠ 0 := by
  rw [finite_invariant_matrix, Matrix.det_mul, Matrix.det_diagonal]
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => Real.exp_ne_zero _
  · apply Matrix.det_vandermonde_ne_zero_iff.mpr
    intro i j h
    apply ha
    exact (mul_left_inj' (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ)<2)))).mp
      (Real.exp_injective h)

theorem finite_invariant_derivative_bijective {n : ℕ} (a : Fin n → ℝ)
    (ha : Function.Injective a) :
    Function.Bijective (finiteInvariantDerivative a (finiteInvariantBase n)) := by
  have he : (finiteInvariantDerivative a (finiteInvariantBase n) :
      (Fin n → ℝ) → (Fin n → ℝ)) =
      Matrix.mulVec (fun i j => Real.exp (a i*finiteInvariantBase n j)) := by
    funext x i
    simp [finiteInvariantDerivative, Matrix.mulVec, Matrix.dotProduct]
  rw [he]
  have hu := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (finite_invariant_matrix_det_ne_zero a ha))
  exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu,
    Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩

/-- Prescribing fewer invariants than varied coordinates gives a genuine
nonconstant local curve, through the original geometric integer spectrum. -/
theorem finite_invariant_local_curve {n : ℕ} (a : Fin (n+1) → ℝ)
    (ha : Function.Injective a) :
    ∃ γ : ℝ → (Fin (n+1) → ℝ),
      γ 0 = finiteInvariantBase (n+1) ∧
      ContinuousAt γ 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),
        (∀ i : Fin n, finiteInvariantMap a (γ t) i.castSucc =
          finiteInvariantMap a (finiteInvariantBase (n+1)) i.castSucc) ∧
        (t ≠ 0 → γ t ≠ finiteInvariantBase (n+1)) ∧ ContinuousAt γ t) := by
  let x := finiteInvariantBase (n+1)
  let f := finiteInvariantMap a
  let L := finiteInvariantDerivative a x
  let e : (Fin (n+1) → ℝ) ≃L[ℝ] (Fin (n+1) → ℝ) :=
    (LinearEquiv.ofBijective L.toLinearMap
      (finite_invariant_derivative_bijective a ha)).toContinuousLinearEquiv
  have hd : HasStrictFDerivAt f (e : _ →L[ℝ] _) x :=
    finite_invariant_map_derivative a x
  let y : ℝ → (Fin (n+1) → ℝ) :=
    fun t => f x + t • (Pi.single (Fin.last n) (1 : ℝ) : Fin (n+1) → ℝ)
  have hy0 : y 0 = f x := by simp [y]
  have hy : ContinuousAt y 0 := continuousAt_const.add
    (continuousAt_id.smul continuousAt_const)
  let γ := fun t => hd.localInverse f e x (y t)
  have hg0 : γ 0 = x := by simp [γ,hy0]
  have hy' : Tendsto y (𝓝 0) (𝓝 (f x)) := by simpa only [hy0] using hy.tendsto
  have hgc : ContinuousAt γ 0 := by
    rw [ContinuousAt, hg0]
    exact hd.localInverse_tendsto.comp hy'
  have hr : ∀ᶠ t in 𝓝 (0 : ℝ), f (γ t) = y t :=
    hy'.eventually hd.eventually_right_inverse
  have hyglobal : Continuous y := continuous_const.add
    (continuous_id.smul continuous_const)
  have htarget : ∀ᶠ t in 𝓝 (0 : ℝ), y t ∈ (hd.toPartialHomeomorph f).target :=
    hy'.eventually ((hd.toPartialHomeomorph f).open_target.mem_nhds
      hd.image_mem_toPartialHomeomorph_target)
  refine ⟨γ,hg0,hgc,?_⟩
  filter_upwards [hr,htarget] with t ht htarget
  refine ⟨?_,?_,?_⟩
  · intro i
    have h := congrFun ht i.castSucc
    simpa [y,Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne] using h
  · intro ht0 htx
    have h := congrFun ht (Fin.last n)
    rw [htx] at h
    simp [y] at h
    exact ht0 h
  · exact ((hd.toPartialHomeomorph f).continuousAt_symm htarget).comp
      hyglobal.continuousAt

/-- Any finite set of distinct exponential or logarithmic constraints can be
preserved by varying one more coordinate. -/
theorem finite_invariant_preserving_curve {n : ℕ} (a : Fin n → ℝ)
    (ha : Function.Injective a) :
    ∃ γ : ℝ → (Fin (n+1) → ℝ),
      γ 0 = finiteInvariantBase (n+1) ∧ ContinuousAt γ 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),
        (∀ i : Fin n, (∑ j, finiteInvariantPrimitive (a i) (γ t j)) =
          ∑ j, finiteInvariantPrimitive (a i) (finiteInvariantBase (n+1) j)) ∧
        (t ≠ 0 → γ t ≠ finiteInvariantBase (n+1)) ∧ ContinuousAt γ t) := by
  obtain ⟨b,hb⟩ := (Set.finite_range a).exists_not_mem
  have hab : Function.Injective (Fin.snoc a b) := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i <;> intro j <;>
      refine Fin.lastCases ?_ (fun j => ?_) j <;> intro h
    · rfl
    · simp only [Fin.snoc_last,Fin.snoc_castSucc] at h
      exact False.elim (hb ⟨j,h.symm⟩)
    · simp only [Fin.snoc_last,Fin.snoc_castSucc] at h
      exact False.elim (hb ⟨i,h⟩)
    · simp only [Fin.snoc_castSucc] at h
      exact congrArg Fin.castSucc (ha h)
  obtain ⟨γ,h0,hc,hγ⟩ := finite_invariant_local_curve (Fin.snoc a b) hab
  refine ⟨γ,h0,hc,hγ.mono ?_⟩
  intro t ht
  exact ⟨fun i => by simpa [finiteInvariantMap] using ht.1 i,ht.2⟩

end
end Sigma
