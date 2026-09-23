import SigmaArithmeticEulerGenerators
import Mathlib.Data.Set.Card

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology BigOperators

/-- Restrict the original multiplicities along the actual inclusion of the
real generator set with one generator deleted. -/
def realEulerEraseMultiplicity {Q : Set ℝ} (m : Q → ℕ) (a : ℝ) :
    ↥(Q \ {a}) → ℕ := fun q => m ⟨q, q.property.1⟩

theorem real_euler_erase_multiplicity_pos {Q : Set ℝ} {m : Q → ℕ}
    (hm : ∀ q, 0 < m q) (a : ℝ) (q : ↥(Q \ {a})) :
    0 < realEulerEraseMultiplicity m a q := hm _

/-- The finite-complement subtype used by `HasProd` is exactly the deleted
subset of real generators, with no new indexing or multiplicities. -/
def realEulerEraseEquiv {Q : Set ℝ} (a : Q) :
    ↥(Q \ {(a : ℝ)}) ≃ {q : Q // q ∉ ({a} : Finset Q)} := by
  classical
  refine
    { toFun := fun q => ⟨⟨q, q.property.1⟩, ?_⟩
      invFun := fun q => ⟨q.val, q.val.property, ?_⟩
      left_inv := fun q => rfl
      right_inv := fun q => rfl }
  · simp only [Finset.mem_singleton]
    intro he
    apply q.property.2
    exact Set.mem_singleton_iff.mpr (congrArg (fun r : Q => (r : ℝ)) he)
  · simp only [Set.mem_singleton_iff]
    intro he
    apply q.property
    exact Finset.mem_singleton.mpr (Subtype.ext he)

theorem real_euler_product_remove_generator_set {Q : Set ℝ} {m : Q → ℕ} {s Z : ℝ}
    (hQ : ∀ q ∈ Q, 1 < q) (hs : 0 < s) (hZ : 0 < Z)
    (hprod : HasProd (fun q : Q => realEulerFactor q (m q) s) Z) (a : Q) :
    HasProd (fun q : ↥(Q \ {(a : ℝ)}) =>
      realEulerFactor q (realEulerEraseMultiplicity m a q) s)
        (Z / realEulerFactor a (m a) s) ∧
      0 < Z / realEulerFactor a (m a) s := by
  classical
  obtain ⟨hp,hpos⟩ := real_euler_product_remove_generator hQ hs hZ hprod a
  refine ⟨?_,hpos⟩
  exact (realEulerEraseEquiv a).hasProd_iff.mpr hp

/-- Positive convergence on a terminal real ray survives removal of the
entire factor at one generator. No independence of generator powers is used. -/
theorem real_euler_remove_generator_terminal_convergence
    {Q : Set ℝ} {m : Q → ℕ} {Z : ℝ → ℝ}
    (hQ : ∀ q ∈ Q, 1 < q)
    (hconv : ∃ S : ℝ, ∀ s, S ≤ s → 0 < Z s ∧
      HasProd (fun q : Q => realEulerFactor q (m q) s) (Z s)) (a : Q) :
    ∃ S : ℝ, ∀ s, S ≤ s →
      0 < Z s / realEulerFactor a (m a) s ∧
      HasProd (fun q : ↥(Q \ {(a : ℝ)}) =>
        realEulerFactor q (realEulerEraseMultiplicity m a q) s)
          (Z s / realEulerFactor a (m a) s) := by
  obtain ⟨S,hS⟩ := hconv
  refine ⟨max S 1, fun s hs => ?_⟩
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hs)
  obtain ⟨hz,hp⟩ := hS s ((le_max_left _ _).trans hs)
  exact (real_euler_product_remove_generator_set hQ hs0 hz hp a).symm

theorem real_euler_erase_bounded_ncard_add_one {Q : Set ℝ} {a x : ℝ}
    (ha : a ∈ Q) (hax : a ≤ x) (hfin : (Q ∩ Iic x).Finite) :
    ((Q \ {a}) ∩ Iic x).ncard + 1 = (Q ∩ Iic x).ncard := by
  have he : (Q \ {a}) ∩ Iic x = (Q ∩ Iic x) \ {a} := by
    ext q
    simp only [mem_inter_iff, mem_diff]
    tauto
  rw [he]
  exact Set.ncard_diff_singleton_add_one ⟨ha,hax⟩ hfin

theorem real_euler_erase_bounded_ncard_lt {Q : Set ℝ} {a x : ℝ}
    (ha : a ∈ Q) (hax : a ≤ x) (hfin : (Q ∩ Iic x).Finite) :
    ((Q \ {a}) ∩ Iic x).ncard < (Q ∩ Iic x).ncard := by
  have h := real_euler_erase_bounded_ncard_add_one ha hax hfin
  omega

end
end Sigma
