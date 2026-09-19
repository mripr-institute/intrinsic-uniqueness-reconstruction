import SigmaRealSpatial
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Dimension.Finite

namespace Sigma
noncomputable section
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem perpendicular_equal_norm_from_pair (u v : V)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) (x : V) :
    ∃ y : V, ⟪x, y⟫_ℝ = 0 ∧ ‖y‖ = ‖x‖ := by
  by_cases ha : ⟪x, u⟫_ℝ = 0
  · exact ⟨‖x‖ • u, by simp [real_inner_smul_right, ha], by simp [norm_smul, hu]⟩
  · let w : V := ⟪x, v⟫_ℝ • u - ⟪x, u⟫_ℝ • v
    have hwx : ⟪x, w⟫_ℝ = 0 := by
      simp only [w, inner_sub_right, real_inner_smul_right]
      ring
    have hwv : ⟪w, v⟫_ℝ = -⟪x, u⟫_ℝ := by
      simp [w, inner_sub_left, real_inner_smul_left, huv,
        real_inner_self_eq_norm_sq, hv]
    have hw0 : w ≠ 0 := by
      intro h
      rw [h] at hwv
      simp at hwv
      exact ha hwv
    have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    refine ⟨(‖x‖ / ‖w‖) • w, by simp [real_inner_smul_right, hwx], ?_⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_mul_cancel₀ _ (ne_of_gt hwn)

theorem even_nonnegative_orthogonal_quadratic (f : V → ℝ)
    (hf : OrthogonallyAdditive f) (hpos : ∀ x, 0 ≤ f x)
    (heven : ∀ x, f (-x) = f x)
    (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) :
    ∃ c ≥ 0, ∀ x : V, f x = c * ‖x‖ ^ 2 := by
  let A : ℝ → ℝ := fun s => f (Real.sqrt s • u)
  have hsqrt : ∀ s ≥ 0, ‖Real.sqrt s • u‖ ^ 2 = s := by
    intro s hs
    simp [norm_smul, Real.norm_eq_abs, hu, Real.sq_sqrt hs]
  have hrep : ∀ x : V, f x = A (‖x‖ ^ 2) := by
    intro x
    apply even_orthogonal_equal_norm f hf heven
    have h := hsqrt (‖x‖ ^ 2) (sq_nonneg _)
    nlinarith [norm_nonneg x, norm_nonneg (Real.sqrt (‖x‖ ^ 2) • u)]
  have hadd : ∀ a ≥ 0, ∀ b ≥ 0, A (a + b) = A a + A b := by
    intro a ha b hb
    have ho : ⟪Real.sqrt a • u, Real.sqrt b • v⟫_ℝ = 0 := by
      simp [real_inner_smul_left, real_inner_smul_right, huv]
    have hn : ‖Real.sqrt a • u + Real.sqrt b • v‖ ^ 2 = a + b := by
      rw [norm_add_sq_real]
      simp [ho, norm_smul, Real.norm_eq_abs, hu, hv, Real.sq_sqrt ha, Real.sq_sqrt hb]
    have hsum := hrep (Real.sqrt a • u + Real.sqrt b • v)
    rw [hn, hf _ _ ho] at hsum
    have heq : f (Real.sqrt b • v) = f (Real.sqrt b • u) := by
      apply even_orthogonal_equal_norm f hf heven
      simp [norm_smul, hu, hv]
    rw [heq] at hsum
    exact hsum.symm
  have hlinear := nonnegative_additive_ray_linear A (fun s _ => hpos _) hadd
  refine ⟨A 1, hpos _, ?_⟩
  intro x
  rw [hrep x, hlinear (‖x‖ ^ 2) (sq_nonneg _)]

theorem quadratically_bounded_doubling_zero (f : V → ℝ) (c : ℝ)
    (hbound : ∀ x, |f x| ≤ c * ‖x‖ ^ 2)
    (hdouble : ∀ x, f ((2 : ℝ) • x) = 2 * f x) : ∀ x, f x = 0 := by
  have hscale : ∀ n : ℕ, ∀ x : V,
      f (((1 / 2 : ℝ) ^ n) • x) = (1 / 2 : ℝ) ^ n * f x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      have hd := hdouble (((1 / 2 : ℝ) ^ (n + 1)) • x)
      have he : (2 : ℝ) • (((1 / 2 : ℝ) ^ (n + 1)) • x) =
          ((1 / 2 : ℝ) ^ n) • x := by
        rw [smul_smul]
        congr 1
        rw [pow_succ]
        ring
      rw [he, ih x] at hd
      rw [pow_succ] at hd ⊢
      linarith
  intro x
  have hestimate : ∀ n : ℕ, (2 : ℝ) ^ n * |f x| ≤ c * ‖x‖ ^ 2 := by
    intro n
    have hb := hbound (((1 / 2 : ℝ) ^ n) • x)
    rw [hscale, abs_mul, norm_smul, Real.norm_eq_abs] at hb
    have hq : 0 < (1 / 2 : ℝ) ^ n := by positivity
    rw [abs_of_pos hq] at hb
    have hsmall : |f x| ≤ c * ‖x‖ ^ 2 * (1 / 2 : ℝ) ^ n := by
      apply (mul_le_mul_left hq).mp
      nlinarith [hb]
    have he : (1 / 2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n := by rw [div_pow, one_pow]
    rw [he, ← div_eq_mul_one_div] at hsmall
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mp hsmall
    simpa [mul_comm] using hh
  by_contra hx
  have habs : 0 < |f x| := abs_pos.mpr hx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (c * ‖x‖ ^ 2 / |f x|)
    (show (1 : ℝ) < 2 by norm_num)
  have hlarge := (div_lt_iff₀ habs).mp hn
  exact (not_lt_of_ge (hestimate n)) hlarge

theorem nonnegative_orthogonal_quadratic_of_pair (f : V → ℝ)
    (hf : OrthogonallyAdditive f) (hpos : ∀ x, 0 ≤ f x)
    (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) :
    ∃ c ≥ 0, ∀ x : V, f x = c * ‖x‖ ^ 2 := by
  let e : V → ℝ := fun x => (f x + f (-x)) / 2
  let o : V → ℝ := fun x => (f x - f (-x)) / 2
  have hneg : ∀ x y : V, ⟪x, y⟫_ℝ = 0 →
      f (-(x + y)) = f (-x) + f (-y) := by
    intro x y hxy
    simpa only [neg_add] using hf (-x) (-y) (by simpa using hxy)
  have heorth : OrthogonallyAdditive e := by
    intro x y hxy
    dsimp [e]
    rw [hf x y hxy, hneg x y hxy]
    ring
  have hoorth : OrthogonallyAdditive o := by
    intro x y hxy
    dsimp [o]
    rw [hf x y hxy, hneg x y hxy]
    ring
  have hepos : ∀ x, 0 ≤ e x := by
    intro x
    exact div_nonneg (add_nonneg (hpos x) (hpos (-x))) (by norm_num)
  have heeven : ∀ x, e (-x) = e x := by intro x; simp [e, add_comm]
  have hoodd : ∀ x, o (-x) = -o x := by intro x; simp [o]; ring
  obtain ⟨c, hc, he⟩ := even_nonnegative_orthogonal_quadratic e heorth hepos
    heeven u v hu hv huv
  have hobound : ∀ x, |o x| ≤ c * ‖x‖ ^ 2 := by
    intro x
    rw [← he x]
    apply abs_le.mpr
    dsimp [e, o]
    constructor <;> linarith [hpos x, hpos (-x)]
  have hodouble : ∀ x, o ((2 : ℝ) • x) = 2 * o x := by
    intro x
    obtain ⟨y, hy, hyn⟩ := perpendicular_equal_norm_from_pair u v hu hv huv x
    exact odd_orthogonal_double o hoorth hoodd x y hy hyn.symm
  have hozero := quadratically_bounded_doubling_zero o c hobound hodouble
  refine ⟨c, hc, ?_⟩
  intro x
  have h1 := he x
  have h2 := hozero x
  dsimp [e] at h1
  dsimp [o] at h2
  linarith

theorem nonnegative_orthogonal_quadratic_finiteDimensional [FiniteDimensional ℝ V]
    (hdim : 2 ≤ Module.finrank ℝ V) (f : V → ℝ)
    (hf : OrthogonallyAdditive f) (hpos : ∀ x, 0 ≤ f x) :
    ∃ c ≥ 0, ∀ x : V, f x = c * ‖x‖ ^ 2 := by
  let b := stdOrthonormalBasis ℝ V
  let i : Fin (Module.finrank ℝ V) := ⟨0, by omega⟩
  let j : Fin (Module.finrank ℝ V) := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  exact nonnegative_orthogonal_quadratic_of_pair f hf hpos (b i) (b j)
    (b.orthonormal.1 i) (b.orthonormal.1 j) (b.orthonormal.2 hij)

/-- The original dimension-at-least-two theorem, with no finiteness,
continuity, measurability, radiality, or homogeneity assumption. -/
theorem nonnegative_orthogonal_quadratic
    (hdim : (2 : Cardinal) ≤ Module.rank ℝ V) (f : V → ℝ)
    (hf : OrthogonallyAdditive f) (hpos : ∀ x, 0 ≤ f x) :
    ∃ c ≥ 0, ∀ x : V, f x = c * ‖x‖ ^ 2 := by
  obtain ⟨w, hw⟩ := exists_linearIndependent_of_le_rank (n := 2) hdim
  let v : Fin 2 → V := @gramSchmidtNormed ℝ V _ _ _ (Fin 2)
    (inferInstance : LinearOrder (Fin 2))
    (inferInstance : LocallyFiniteOrderBot (Fin 2))
    (inferInstance : WellFoundedLT (Fin 2)) w
  have ho : Orthonormal ℝ v :=
    @gramSchmidt_orthonormal ℝ V _ _ _ (Fin 2)
      (inferInstance : LinearOrder (Fin 2))
      (inferInstance : LocallyFiniteOrderBot (Fin 2))
      (inferInstance : WellFoundedLT (Fin 2)) w hw
  exact nonnegative_orthogonal_quadratic_of_pair f hf hpos
    (v 0) (v 1)
    (ho.1 0) (ho.1 1) (ho.2 (by decide : (0 : Fin 2) ≠ 1))

theorem nonnegative_orthogonal_quadratic_iff
    (hdim : (2 : Cardinal) ≤ Module.rank ℝ V) (f : V → ℝ) :
    (OrthogonallyAdditive f ∧ ∀ x, 0 ≤ f x) ↔
      ∃ c ≥ 0, ∀ x : V, f x = c * ‖x‖ ^ 2 := by
  constructor
  · rintro ⟨hf, hp⟩
    exact nonnegative_orthogonal_quadratic hdim f hf hp
  · rintro ⟨c, hc, hf⟩
    constructor
    · intro x y hxy
      have hn := norm_square_orthogonal_additive x y hxy
      dsimp only at hn
      rw [hf (x + y), hf x, hf y, hn]
      ring
    · intro x
      rw [hf x]
      positivity

theorem quartic_not_orthogonal_additive_of_pair (u v : V)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) :
    ¬ OrthogonallyAdditive (fun x : V => ‖x‖ ^ 4) := by
  intro h
  have hh := h u v huv
  have hn : ‖u + v‖ ^ 2 = 2 := by
    have h2 := norm_square_orthogonal_additive u v huv
    dsimp only at h2
    norm_num [hu, hv] at h2
    exact h2
  dsimp only at hh
  rw [hu, hv] at hh
  norm_num at hh
  nlinarith [sq_nonneg (‖u + v‖ ^ 2 - 2)]

theorem line_quartic_orthogonal_additive :
    OrthogonallyAdditive (fun x : ℝ => x ^ 4) := by
  intro x y hxy
  have h : x * y = 0 := by simpa [real_inner_comm] using hxy
  rcases mul_eq_zero.mp h with rfl | rfl <;> simp

theorem line_quartic_not_quadratic :
    ¬ ∃ c : ℝ, ∀ x : ℝ, x ^ 4 = c * ‖x‖ ^ 2 := by
  rintro ⟨c, hc⟩
  have h1 := hc 1
  have h2 := hc 2
  norm_num at h1 h2
  linarith

theorem nonnegative_orthogonal_star_finiteDimensional [FiniteDimensional ℝ V]
    (hdim : 2 ≤ Module.finrank ℝ V) (z : V → ℝ) (hz : ∀ x, 0 ≤ z x)
    (hstar : ∀ x y, ⟪x, y⟫_ℝ = 0 → z (x + y) = z x + z y + z x * z y) :
    ∃ c ≥ 0, ∀ x, z x = Real.exp (c * ‖x‖ ^ 2) - 1 := by
  have hlogpos : ∀ x, 0 ≤ Real.log (1 + z x) := by
    intro x
    apply Real.log_nonneg
    linarith [hz x]
  obtain ⟨c, hc, h⟩ := nonnegative_orthogonal_quadratic_finiteDimensional hdim
    (fun x => Real.log (1 + z x)) (orthogonal_star_log z hz hstar) hlogpos
  refine ⟨c, hc, ?_⟩
  intro x
  have he := congrArg Real.exp (h x)
  rw [Real.exp_log (by linarith [hz x] : 0 < 1 + z x)] at he
  linarith

theorem nonnegative_orthogonal_star
    (hdim : (2 : Cardinal) ≤ Module.rank ℝ V)
    (z : V → ℝ) (hz : ∀ x, 0 ≤ z x)
    (hstar : ∀ x y, ⟪x, y⟫_ℝ = 0 → z (x + y) = z x + z y + z x * z y) :
    ∃ c ≥ 0, ∀ x, z x = Real.exp (c * ‖x‖ ^ 2) - 1 := by
  have hlogpos : ∀ x, 0 ≤ Real.log (1 + z x) := by
    intro x
    apply Real.log_nonneg
    linarith [hz x]
  obtain ⟨c, hc, h⟩ := nonnegative_orthogonal_quadratic hdim
    (fun x => Real.log (1 + z x)) (orthogonal_star_log z hz hstar) hlogpos
  refine ⟨c, hc, ?_⟩
  intro x
  have he := congrArg Real.exp (h x)
  rw [Real.exp_log (by linarith [hz x] : 0 < 1 + z x)] at he
  linarith

theorem nonnegative_orthogonal_star_iff
    (hdim : (2 : Cardinal) ≤ Module.rank ℝ V) (z : V → ℝ) :
    ((∀ x, 0 ≤ z x) ∧ (∀ x y, ⟪x, y⟫_ℝ = 0 →
      z (x + y) = z x + z y + z x * z y)) ↔
        ∃ c ≥ 0, ∀ x, z x = Real.exp (c * ‖x‖ ^ 2) - 1 := by
  constructor
  · rintro ⟨hz, hstar⟩
    exact nonnegative_orthogonal_star hdim z hz hstar
  · rintro ⟨c, hc, hz⟩
    constructor
    · intro x
      rw [hz x]
      have h := Real.one_le_exp_iff.mpr (mul_nonneg hc (sq_nonneg ‖x‖))
      linarith
    · intro x y hxy
      have hn := norm_square_orthogonal_additive x y hxy
      dsimp only at hn
      rw [hz (x + y), hz x, hz y, hn, mul_add, Real.exp_add]
      ring

omit [InnerProductSpace ℝ V] in
theorem quadratic_scale_calibration (u : V) (hu : ‖u‖ = 1) (c d : ℝ)
    (h : c * ‖u‖ ^ 2 = d * ‖u‖ ^ 2) : c = d := by simpa [hu] using h

omit [InnerProductSpace ℝ V] in
theorem quadratic_scale_calibration_nonzero (u : V) (hu : u ≠ 0) (c d : ℝ)
    (h : c * ‖u‖ ^ 2 = d * ‖u‖ ^ 2) : c = d :=
  mul_right_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)) h

omit [InnerProductSpace ℝ V] in
theorem quadratic_nontrivial_scale_positive (c : ℝ) (hc : 0 ≤ c)
    (h : ∃ x : V, c * ‖x‖ ^ 2 ≠ 0) : 0 < c := by
  rcases h with ⟨x, hx⟩
  exact lt_of_le_of_ne hc (fun hz => hx (by simp [hz.symm]))

end
end Sigma
