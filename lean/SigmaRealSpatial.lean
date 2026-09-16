import SigmaPresentations
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Sigma
noncomputable section
open scoped InnerProductSpace

/-- The positive-ray power, written through exp/log to retain its derivative. -/
def radialWeight (a x : ℝ) : ℝ := Real.exp (a * Real.log x)

theorem radialWeight_eq_rpow (a x : ℝ) (hx : 0 < x) : radialWeight a x = x ^ a := by
  rw [Real.rpow_def_of_pos hx]
  unfold radialWeight
  congr 1
  ring

theorem radialWeight_pos (a x : ℝ) : 0 < radialWeight a x := Real.exp_pos _

theorem radialWeight_deriv (a x : ℝ) (hx : 0 < x) :
    HasDerivAt (radialWeight a) (a * radialWeight a x / x) x := by
  convert (((Real.hasDerivAt_log (ne_of_gt hx)).const_mul a).exp) using 1
  simp only [radialWeight]
  ring

theorem weighted_profile_deriv (a : ℝ) (f : ℝ → ℝ) (x : ℝ)
    (hx : 0 < x) (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun y => radialWeight a y * f y)
      (a * radialWeight a x / x * f x + radialWeight a x * deriv f x) x :=
  (radialWeight_deriv a x hx).mul hf.hasDerivAt

theorem weighted_profile_second_deriv (a : ℝ) (f : ℝ → ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (x f₂ : ℝ) (hx : 0 < x)
    (hf₂ : HasDerivAt (deriv f) f₂ x) :
    HasDerivAt (deriv (fun y => radialWeight a y * f y))
      (radialWeight a x * f₂ + 2 * a * radialWeight a x / x * deriv f x +
        a * (a - 1) * radialWeight a x / x ^ 2 * f x) x := by
  have hfd := (hf x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
  have hw := radialWeight_deriv a x hx
  have hd := (((hw.const_mul a).div (hasDerivAt_id x) (ne_of_gt hx)).mul
    hfd.hasDerivAt).add (hw.mul hf₂)
  have he : (fun y => a * radialWeight a y / y * f y + radialWeight a y * deriv f y)
      =ᶠ[nhds x] deriv (fun y => radialWeight a y * f y) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact (weighted_profile_deriv a f y hy
      ((hf y hy).differentiableAt (isOpen_Ioi.mem_nhds hy))).deriv.symm
  convert hd.congr_of_eventuallyEq he.symm using 1
  field_simp
  ring

theorem radial_residual (D : ℝ) (f : ℝ → ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (x f₂ : ℝ) (hx : 0 < x)
    (hfx : f x ≠ 0) (hf₂ : HasDerivAt (deriv f) f₂ x) :
    deriv (deriv (fun y => radialWeight ((D - 1) / 2) y * f y)) x /
        (radialWeight ((D - 1) / 2) x * f x) -
      (deriv (deriv f) x / f x + (D - 1) / x * (deriv f x / f x)) =
        (D - 1) * (D - 3) / (4 * x ^ 2) := by
  rw [(weighted_profile_second_deriv ((D - 1) / 2) f hf x f₂ hx hf₂).deriv,
    hf₂.deriv]
  have hw := ne_of_gt (radialWeight_pos ((D - 1) / 2) x)
  field_simp
  ring

theorem radial_laplacian_conjugation (D : ℝ) (u : ℝ → ℝ)
    (hu : DifferentiableOn ℝ u (Set.Ioi 0)) (x u₂ : ℝ) (hx : 0 < x)
    (hu₂ : HasDerivAt (deriv u) u₂ x) :
    -deriv (deriv (fun y => radialWeight (-((D - 1) / 2)) y * u y)) x -
        (D - 1) / x * deriv (fun y => radialWeight (-((D - 1) / 2)) y * u y) x =
      radialWeight (-((D - 1) / 2)) x *
        (-deriv (deriv u) x + (D - 1) * (D - 3) / (4 * x ^ 2) * u x) := by
  rw [(weighted_profile_second_deriv (-((D - 1) / 2)) u hu x u₂ hx hu₂).deriv,
    (weighted_profile_deriv (-((D - 1) / 2)) u x hx
      ((hu x hx).differentiableAt (isOpen_Ioi.mem_nhds hx))).deriv, hu₂.deriv]
  field_simp
  ring

theorem radial_residual_cancellation (D x : ℝ) (hx : 0 < x) :
    (D - 1) * (D - 3) / (4 * x ^ 2) = 0 ↔ D = 1 ∨ D = 3 := by
  have hd : 4 * x ^ 2 ≠ 0 := by positivity
  rw [div_eq_zero_iff]
  simp [hd, mul_eq_zero, sub_eq_zero]

theorem radial_residual_dimension_three (D x : ℝ) (hD : 2 ≤ D) (hx : 0 < x) :
    (D - 1) * (D - 3) / (4 * x ^ 2) = 0 ↔ D = 3 := by
  rw [radial_residual_cancellation D x hx]
  constructor
  · rintro (h | h)
    · linarith
    · exact h
  · exact Or.inr

theorem radial_OU_dimension (D : ℝ) :
    (∀ t : ℝ, D / 2 - t = 2 - t) ↔ D = 4 := by
  constructor
  · intro h
    have h0 := h 0
    linarith
  · rintro rfl t
    ring

/-- The constant profile has the same dimension-three residual cancellation. -/
theorem constant_profile_radial_residual_three (x : ℝ) (hx : 0 < x) :
    deriv (deriv (fun y => radialWeight 1 y)) x / radialWeight 1 x = 0 := by
  have hf : DifferentiableOn ℝ (fun _ : ℝ => (1 : ℝ)) (Set.Ioi 0) :=
    differentiableOn_const 1
  have hd : deriv (fun _ : ℝ => (1 : ℝ)) = fun _ => 0 := by
    funext y
    exact deriv_const y 1
  have hf₂ : HasDerivAt (deriv (fun _ : ℝ => (1 : ℝ))) 0 x := by
    rw [hd]
    exact hasDerivAt_const x 0
  have h := radial_residual 3 (fun _ => 1) hf x 0 hx (by norm_num) hf₂
  norm_num only [show ((3 : ℝ) - 1) / 2 = 1 by norm_num, mul_one,
    hd, deriv_const, sub_self, zero_div, div_one, mul_zero, add_zero, sub_zero] at h
  exact h

theorem constant_profile_differs_from_H_on_positive_ray :
    ¬ (∀ x : ℝ, 0 < x → (1 : ℝ) = SigmaPresentations.H x) := by
  intro h
  have h1 := h 1 (by norm_num)
  norm_num [SigmaPresentations.H] at h1

theorem nonnegative_additive_ray_linear (A : ℝ → ℝ)
    (hpos : ∀ x ≥ 0, 0 ≤ A x)
    (hadd : ∀ x ≥ 0, ∀ y ≥ 0, A (x + y) = A x + A y) :
    ∀ x ≥ 0, A x = A 1 * x := by
  have hzero : A 0 = 0 := by
    have hh := hadd 0 (by norm_num) 0 (by norm_num)
    norm_num at hh
    linarith
  have hmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → A x ≤ A y := by
    intro x y hx hxy
    have hsub := hadd x hx (y - x) (sub_nonneg.mpr hxy)
    have hp := hpos (y - x) (sub_nonneg.mpr hxy)
    rw [add_sub_cancel] at hsub
    linarith
  have hnat : ∀ n : ℕ, ∀ x ≥ 0, A ((n : ℝ) * x) = (n : ℝ) * A x := by
    intro n
    induction n with
    | zero => intro x hx; simp [hzero]
    | succ n ih =>
      intro x hx
      push_cast
      rw [add_mul, one_mul, hadd ((n : ℝ) * x) (by positivity) x hx, ih x hx]
      ring
  have hnval : ∀ n : ℕ, A (n : ℝ) = (n : ℝ) * A 1 := by
    intro n
    simpa using hnat n 1 (by norm_num)
  intro x hx
  have hc : 0 ≤ A 1 := hpos 1 (by norm_num)
  have bounds : ∀ n : ℕ, (n : ℝ) * (A x - A 1 * x) ≤ A 1 ∧
      (n : ℝ) * (A 1 * x - A x) ≤ A 1 := by
    intro n
    let k : ℕ := ⌊(n : ℝ) * x⌋₊
    have hlow : (k : ℝ) ≤ (n : ℝ) * x := Nat.floor_le (by positivity)
    have hupp : (n : ℝ) * x < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hAlo := hmono (k : ℝ) ((n : ℝ) * x) (by positivity) hlow
    have hAup := hmono ((n : ℝ) * x) ((k : ℝ) + 1) (by positivity) (le_of_lt hupp)
    rw [hnval k, hnat n x hx] at hAlo
    rw [hnat n x hx] at hAup
    have hAk : A ((k : ℝ) + 1) = ((k : ℝ) + 1) * A 1 := by
      simpa using hnval (k + 1)
    rw [hAk] at hAup
    constructor <;> nlinarith [mul_nonneg hc (sub_nonneg.mpr hlow),
      mul_nonneg hc (le_of_lt (sub_pos.mpr hupp))]
  have bound_zero : ∀ d : ℝ, (∀ n : ℕ, (n : ℝ) * d ≤ A 1) → d ≤ 0 := by
    intro d hd
    by_contra h
    have hdpos : 0 < d := lt_of_not_ge h
    obtain ⟨n, hn⟩ := exists_nat_gt (A 1 / d)
    have hh : A 1 < (n : ℝ) * d := (div_lt_iff₀ hdpos).mp hn
    exact (not_lt_of_ge (hd n)) hh
  have h1 := bound_zero (A x - A 1 * x) (fun n => (bounds n).1)
  have h2 := bound_zero (A 1 * x - A x) (fun n => (bounds n).2)
  linarith

section InnerProduct
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def OrthogonallyAdditive (f : V → ℝ) : Prop :=
  ∀ x y : V, ⟪x, y⟫_ℝ = 0 → f (x + y) = f x + f y

theorem linear_profile_orthogonally_additive (u : V) :
    OrthogonallyAdditive (fun x : V => ⟪x, u⟫_ℝ) := by
  intro x y _
  exact inner_add_left x y u

theorem linear_profile_negative_at_neg_unit (u : V) (hu : ‖u‖ = 1) :
    ⟪-u, u⟫_ℝ = -1 := by
  simp [inner_neg_left, real_inner_self_eq_norm_sq, hu]

/-- Without nonnegativity, an explicit linear functional defeats the quadratic
conclusion even in every space containing a unit vector. -/
theorem linear_profile_not_quadratic (u : V) (hu : ‖u‖ = 1) :
    ¬ ∃ c : ℝ, ∀ x : V, ⟪x, u⟫_ℝ = c * ‖x‖ ^ 2 := by
  rintro ⟨c, hc⟩
  have hp := hc u
  have hn := hc (-u)
  rw [linear_profile_negative_at_neg_unit u hu] at hn
  simp only [real_inner_self_eq_norm_sq, norm_neg, hu, one_pow, mul_one] at hp hn
  linarith

theorem orthogonal_zero (f : V → ℝ) (hf : OrthogonallyAdditive f) : f 0 = 0 := by
  have h := hf 0 0 (by simp)
  simp only [zero_add] at h
  linarith

theorem even_orthogonal_equal_norm (f : V → ℝ) (hf : OrthogonallyAdditive f)
    (heven : ∀ x, f (-x) = f x) (x y : V) (hxy : ‖x‖ = ‖y‖) : f x = f y := by
  let a := (1 / 2 : ℝ) • (x + y)
  let b := (1 / 2 : ℝ) • (x - y)
  have hinner : ⟪a, b⟫_ℝ = 0 := by
    dsimp [a, b]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left,
      inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm y x, hxy]
    ring
  have hab : a + b = x := by
    dsimp [a, b]
    rw [← smul_add]
    have he : (x + y) + (x - y) = (2 : ℝ) • x := by
      rw [two_smul]
      abel
    rw [he, smul_smul]
    norm_num
  have hab' : a + -b = y := by
    dsimp [a, b]
    rw [← smul_neg, ← smul_add]
    have he : (x + y) + -(x - y) = (2 : ℝ) • y := by
      rw [two_smul]
      abel
    rw [he, smul_smul]
    norm_num
  have h1 := hf a b hinner
  have h2 := hf a (-b) (by simpa using hinner)
  rw [hab] at h1
  rw [hab', heven b] at h2
  exact h1.trans h2.symm

theorem odd_orthogonal_double (f : V → ℝ) (hf : OrthogonallyAdditive f)
    (hodd : ∀ x, f (-x) = -f x) (x y : V)
    (hxy : ⟪x, y⟫_ℝ = 0) (hn : ‖x‖ = ‖y‖) :
    f ((2 : ℝ) • x) = 2 * f x := by
  have hinner : ⟪x + y, x - y⟫_ℝ = 0 := by
    simp only [inner_add_left, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm y x, hxy, hn]
    ring
  have h1 := hf (x + y) (x - y) hinner
  have h2 := hf x y hxy
  have h3 := hf x (-y) (by simpa using hxy)
  have he : (x + y) + (x - y) = (2 : ℝ) • x := by rw [two_smul]; abel
  rw [he, h2] at h1
  rw [hodd y] at h3
  simp only [← sub_eq_add_neg] at h3
  rw [h3] at h1
  linarith

theorem norm_square_orthogonal_additive :
    OrthogonallyAdditive (fun x : V => ‖x‖ ^ 2) := by
  intro x y hxy
  simpa [hxy] using norm_add_sq_real x y

theorem orthogonal_star_log (z : V → ℝ) (hz : ∀ x, 0 ≤ z x)
    (hstar : ∀ x y, ⟪x, y⟫_ℝ = 0 →
      z (x + y) = z x + z y + z x * z y) :
    OrthogonallyAdditive (fun x => Real.log (1 + z x)) := by
  intro x y hxy
  have hx : 1 + z x ≠ 0 := ne_of_gt (by have h := hz x; linarith)
  have hy : 1 + z y ≠ 0 := ne_of_gt (by have h := hz y; linarith)
  dsimp only
  rw [hstar x y hxy]
  have he : 1 + (z x + z y + z x * z y) = (1 + z x) * (1 + z y) := by ring
  rw [he, Real.log_mul hx hy]

end InnerProduct
end
end Sigma
