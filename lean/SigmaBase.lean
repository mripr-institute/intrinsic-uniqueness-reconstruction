import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Exact scalar identities independently checked from the manuscript definitions.
No reconstruction, matrix, or Hermite--Lindemann theorem is asserted here. -/
namespace SigmaBase
noncomputable section

def star (x y : ℝ) : ℝ := x + y + x * y
def invStar (x : ℝ) : ℝ := -x / (1 + x)
def potential (t : ℝ) : ℝ := t - 1 - Real.log t
def displacement (x : ℝ) : ℝ := Real.log (1 + x) - x

theorem one_add_star (x y : ℝ) : 1 + star x y = (1 + x) * (1 + y) := by
  unfold star
  ring

theorem star_assoc (x y z : ℝ) : star (star x y) z = star x (star y z) := by
  unfold star
  ring

theorem star_comm (x y : ℝ) : star x y = star y x := by
  unfold star
  ring

theorem star_zero (x : ℝ) : star x 0 = x := by simp [star]

theorem star_closed {x y : ℝ} (hx : -1 < x) (hy : -1 < y) :
    -1 < star x y := by
  have h := mul_pos (show 0 < 1 + x by linarith) (show 0 < 1 + y by linarith)
  rw [← one_add_star] at h
  linarith

theorem one_add_invStar {x : ℝ} (hx : -1 < x) :
    1 + invStar x = 1 / (1 + x) := by
  have hn : 1 + x ≠ 0 := ne_of_gt (by linarith)
  unfold invStar
  field_simp

theorem invStar_closed {x : ℝ} (hx : -1 < x) : -1 < invStar x := by
  have h : 0 < 1 + invStar x := by
    rw [one_add_invStar hx]
    exact one_div_pos.mpr (by linarith)
  linarith

theorem star_inverse {x : ℝ} (hx : -1 < x) : star x (invStar x) = 0 := by
  have hn : 1 + x ≠ 0 := ne_of_gt (by linarith)
  unfold star invStar
  field_simp
  ring

theorem log_star {x y : ℝ} (hx : -1 < x) (hy : -1 < y) :
    Real.log (1 + star x y) = Real.log (1 + x) + Real.log (1 + y) := by
  rw [one_add_star, Real.log_mul (ne_of_gt (by linarith)) (ne_of_gt (by linarith))]

theorem displacement_cocycle {x y : ℝ} (hx : -1 < x) (hy : -1 < y) :
    displacement (star x y) = displacement x + displacement y - x * y := by
  unfold displacement
  rw [log_star hx hy]
  unfold star
  ring

theorem normalized_bregman {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    potential t - potential s - (1 - 1 / s) * (t - s) = potential (t / s) := by
  unfold potential
  rw [Real.log_div (ne_of_gt ht) (ne_of_gt hs)]
  field_simp
  ring

/-- Pure algebra: d can be any function; no differentiability is asserted. -/
def bregman (f d : ℝ → ℝ) (t s : ℝ) : ℝ := f t - f s - d s * (t - s)

theorem symmetric_bregman (f d : ℝ → ℝ) (t s : ℝ) :
    bregman f d t s + bregman f d s t = (t - s) * (d t - d s) := by
  unfold bregman
  ring

/-- Finite scalar assembly respects pointwise equality; this is not an SPD theorem. -/
theorem finite_scalar_assembly {α : Type*} (S : Finset α) (f g : α → ℝ)
    (h : ∀ i ∈ S, f i = g i) : ∑ i ∈ S, f i = ∑ i ∈ S, g i := by
  exact Finset.sum_congr rfl h

/-- A list functional with specified scalar increments is uniquely their sum.
This encodes only finite scalar assembly, with additivity explicitly assumed. -/
theorem list_scalar_assembly (F : List ℝ → ℝ) (f : ℝ → ℝ)
    (hempty : F [] = 0)
    (hcons : ∀ x xs, F (x :: xs) = f x + F xs) (xs : List ℝ) :
    F xs = (xs.map f).sum := by
  induction xs with
  | nil => simpa using hempty
  | cons x xs ih => simp only [hcons, ih, List.map_cons, List.sum_cons]

#print axioms list_scalar_assembly
#print axioms star_assoc
#print axioms star_closed
#print axioms invStar_closed
#print axioms star_inverse
#print axioms log_star
#print axioms displacement_cocycle
#print axioms normalized_bregman
#print axioms symmetric_bregman
#print axioms finite_scalar_assembly
end
end SigmaBase
