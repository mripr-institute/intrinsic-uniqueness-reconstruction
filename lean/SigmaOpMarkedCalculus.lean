import SigmaProbCompletionSamples
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Normed.Lp.lpSpace

namespace Sigma
noncomputable section

open scoped ENNReal NNReal

/-- The marked spectral Hilbert space, with one coordinate for every
nonnegative integer eigenvalue. -/
abbrev MarkedIntegerHilbert := lp (fun _ : ℕ => ℂ) 2

/-- The exact weighted-square-summability domain of a scalar function of the
marked integer-spectrum operator. -/
def markedFunctionalDomain (f : ℝ → ℝ) : Submodule ℂ MarkedIntegerHilbert where
  carrier := {x | Memℓp (fun n : ℕ => (f n : ℂ) * x n) 2}
  zero_mem' := by
    change Memℓp (fun n : ℕ => (f n : ℂ) * (0 : MarkedIntegerHilbert) n) 2
    simpa using (0 : MarkedIntegerHilbert).2
  add_mem' {x y} hx hy := by
    change Memℓp (fun n : ℕ => (f n : ℂ) * (x + y) n) 2
    rw [show (fun n : ℕ => (f n : ℂ) * (x + y) n) =
        (fun n : ℕ => (f n : ℂ) * x n + (f n : ℂ) * y n) by
          funext n
          change (f n : ℂ) * (x n + y n) = _
          ring]
    exact hx.add hy
  smul_mem' c x hx := by
    change Memℓp (fun n : ℕ => (f n : ℂ) * (c • x) n) 2
    rw [show (fun n : ℕ => (f n : ℂ) * (c • x) n) =
        (fun n : ℕ => c * ((f n : ℂ) * x n)) by
          funext n
          change (f n : ℂ) * (c * x n) = _
          ring]
    exact hx.const_smul c

/-- The genuine partially defined diagonal functional-calculus operator on
the marked Hilbert space, with its exact maximal weighted `ℓ²` domain. -/
def markedFunctionalCalculus (f : ℝ → ℝ) :
    MarkedIntegerHilbert →ₗ.[ℂ] MarkedIntegerHilbert where
  domain := markedFunctionalDomain f
  toFun :=
    { toFun := fun x => ⟨fun n : ℕ => (f n : ℂ) * x.1 n, x.2⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext n
        change (f n : ℂ) * (x.1 n + y.1 n) =
          (f n : ℂ) * x.1 n + (f n : ℂ) * y.1 n
        exact mul_add _ _ _
      map_smul' := by
        intro c x
        apply lp.ext
        funext n
        change (f n : ℂ) * (c * x.1 n) = c * ((f n : ℂ) * x.1 n)
        ring }

/-- The marked unit eigenvector in the `n`th integer eigenspace. -/
def markedIntegerEigenvector (n : ℕ) : MarkedIntegerHilbert :=
  lp.single (E := fun _ : ℕ => ℂ) 2 n (1 : ℂ)

/-- The canonical marked nonnegative integer-spectrum operator itself. -/
def markedIntegerSpectrumOperator :
    MarkedIntegerHilbert →ₗ.[ℂ] MarkedIntegerHilbert :=
  markedFunctionalCalculus id

theorem markedIntegerEigenvector_mem_domain (f : ℝ → ℝ) (n : ℕ) :
    markedIntegerEigenvector n ∈ (markedFunctionalCalculus f).domain := by
  change Memℓp (fun k : ℕ => (f k : ℂ) * markedIntegerEigenvector n k) 2
  have heq : (fun k : ℕ => (f k : ℂ) * markedIntegerEigenvector n k) =
      fun k => (lp.single (E := fun _ : ℕ => ℂ) 2 n (f n : ℂ)) k := by
    funext k
    by_cases hkn : k = n
    · subst k
      simp [markedIntegerEigenvector, lp.single_apply_self]
    · rw [show markedIntegerEigenvector n k = 0 by
      exact lp.single_apply_ne (E := fun _ : ℕ => ℂ) 2 n (1 : ℂ) hkn]
      rw [lp.single_apply_ne (E := fun _ : ℕ => ℂ) 2 n (f n : ℂ) hkn]
      simp
  rw [heq]
  exact (lp.single (E := fun _ : ℕ => ℂ) 2 n (f n : ℂ)).2

/-- Functional calculus on the marked eigenspace reads off the scalar sample
`f(n)` exactly. -/
theorem markedFunctionalCalculus_eigenvector_action (f : ℝ → ℝ) (n : ℕ) :
    markedFunctionalCalculus f
        ⟨markedIntegerEigenvector n, markedIntegerEigenvector_mem_domain f n⟩ =
      (f n : ℂ) • markedIntegerEigenvector n := by
  apply lp.ext
  funext k
  change (f k : ℂ) * markedIntegerEigenvector n k =
    (f n : ℂ) * markedIntegerEigenvector n k
  by_cases hkn : k = n
  · subst k; rfl
  · rw [show markedIntegerEigenvector n k = 0 by
      exact lp.single_apply_ne (E := fun _ : ℕ => ℂ) 2 n (1 : ℂ) hkn]
    simp

theorem markedIntegerSpectrumOperator_eigenvector_action (n : ℕ) :
    markedIntegerSpectrumOperator
        ⟨markedIntegerEigenvector n, markedIntegerEigenvector_mem_domain id n⟩ =
      (n : ℂ) • markedIntegerEigenvector n := by
  simpa [markedIntegerSpectrumOperator] using
    markedFunctionalCalculus_eigenvector_action id n

/-- Equality of actual functional-calculus actions on every marked integer
eigenspace extracts equality of all scalar samples. -/
theorem marked_samples_of_eigenvector_actions (f g : ℝ → ℝ)
    (h : ∀ n : ℕ,
      markedFunctionalCalculus f
          ⟨markedIntegerEigenvector n, markedIntegerEigenvector_mem_domain f n⟩ =
        markedFunctionalCalculus g
          ⟨markedIntegerEigenvector n, markedIntegerEigenvector_mem_domain g n⟩) :
    ∀ n : ℕ, f n = g n := by
  intro n
  have hn := h n
  rw [markedFunctionalCalculus_eigenvector_action,
    markedFunctionalCalculus_eigenvector_action] at hn
  have hc : ((f n : ℂ) • markedIntegerEigenvector n) n =
      ((g n : ℂ) • markedIntegerEigenvector n) n :=
    congrArg (fun x : MarkedIntegerHilbert => x n) hn
  change (f n : ℂ) * markedIntegerEigenvector n n =
    (g n : ℂ) * markedIntegerEigenvector n n at hc
  rw [show markedIntegerEigenvector n n = 1 by
    exact lp.single_apply_self (E := fun _ : ℕ => ℂ) 2 n (1 : ℂ)] at hc
  simp only [mul_one] at hc
  exact Complex.ofReal_injective hc

/-- Functions agreeing on the nonnegative integer spectrum have exactly the
same partially defined marked functional-calculus operator, including domain. -/
theorem markedFunctionalCalculus_congr (f g : ℝ → ℝ)
    (h : ∀ n : ℕ, f n = g n) :
    markedFunctionalCalculus f = markedFunctionalCalculus g := by
  apply LinearPMap.ext
  · apply Submodule.ext
    intro x
    change Memℓp (fun n : ℕ => (f n : ℂ) * x n) 2 ↔
        Memℓp (fun n : ℕ => (g n : ℂ) * x n) 2
    simp_rw [h]
  · intro x y hxy
    apply lp.ext
    funext n
    change (f n : ℂ) * x.1 n = (g n : ℂ) * y.1 n
    rw [h n]
    exact congrArg (fun z : MarkedIntegerHilbert => (g n : ℂ) * z n) hxy

/-- The smooth nonnegative non-Bernstein perturbation is invisible to the
actual marked functional calculus on the complete integer spectrum. -/
theorem smooth_integer_invisible_marked_functional_calculus :
    ContDiffOn ℝ ⊤ smoothIntegerInvisibleExponent (Set.Ici 0) ∧
    (∀ l : ℝ, 0 ≤ l → 0 ≤ smoothIntegerInvisibleExponent l) ∧
    smoothIntegerInvisibleExponent ≠ gammaLaplaceExponent ∧
    markedFunctionalCalculus smoothIntegerInvisibleExponent =
      markedFunctionalCalculus gammaLaplaceExponent := by
  have h := smooth_integer_invisible_exponent_boundary
  refine ⟨h.1, h.2.1, ?_, markedFunctionalCalculus_congr _ _ h.2.2.1⟩
  intro heq
  exact h.2.2.2.1 (congrFun heq (1 / 2))

end
end Sigma
