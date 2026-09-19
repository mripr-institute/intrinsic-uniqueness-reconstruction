import SigmaPlacedZeros
import SigmaAffineCurvature

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology

def placedLogDerivative (μ a : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  (-1 : ℝ)^(n+1)*(n+1).factorial*(μ/(μ*r+a))^(n+2)

theorem placedLogDerivative_step (μ a : ℝ) (n : ℕ) (r : ℝ)
    (hr : 0 < μ*r+a) :
    HasDerivAt (placedLogDerivative μ a n) (placedLogDerivative μ a (n+1) r) r := by
  have hd := (((hasDerivAt_const r μ).div
    (((hasDerivAt_id r).const_mul μ).add_const a) (ne_of_gt hr)).pow (n+2)).const_mul
    ((-1 : ℝ)^(n+1)*(n+1).factorial)
  convert hd using 1
  simp only [placedLogDerivative, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat, mul_zero, zero_sub, mul_one]
  have hn : n+1+2 = (n+2)+1 := by omega
  rw [hn, pow_succ, show n+1+1 = (n+1)+1 by omega, pow_succ]
  field_simp
  ring

theorem placed_log_iteratedDeriv (μ a : ℝ) (n : ℕ) :
    ∀ r, 0 < μ*r+a → iteratedDeriv (n+2) (placed μ a) r = placedLogDerivative μ a n r := by
  induction n with
  | zero =>
    intro r hr
    simpa [iteratedDeriv_succ, placedLogDerivative] using placed_second_deriv hr
  | succ n ih =>
    intro r hr
    rw [show n+1+2 = (n+2)+1 by omega, iteratedDeriv_succ]
    have he : iteratedDeriv (n+2) (placed μ a) =ᶠ[𝓝 r] placedLogDerivative μ a n := by
      have ho : IsOpen {x : ℝ | 0 < μ*x+a} :=
        isOpen_lt continuous_const ((continuous_const.mul continuous_id).add continuous_const)
      filter_upwards [ho.mem_nhds hr] with x hx
      exact ih x hx
    exact ((placedLogDerivative_step μ a n r hr).congr_of_eventuallyEq he).deriv

theorem derivative_zero_spacing (μ a : ℝ) (_hμ : μ ≠ 0) (n : ℕ) :
    (((n+1 : ℕ) : ℝ)-a)/μ-((n : ℝ)-a)/μ = 1/μ := by
  push_cast
  ring

theorem two_indexed_derivative_zeros_identify (μ a ν b : ℝ)
    (hμ : μ ≠ 0) (hν : ν ≠ 0) (n : ℕ)
    (h0 : ((n : ℝ)-a)/μ = ((n : ℝ)-b)/ν)
    (h1 : (((n+1 : ℕ) : ℝ)-a)/μ = (((n+1 : ℕ) : ℝ)-b)/ν) :
    μ = ν ∧ a = b := by
  have hs : 1/μ = 1/ν := by
    rw [← derivative_zero_spacing μ a hμ n, h0, h1, derivative_zero_spacing ν b hν n]
  have hm : μ = ν := inv_injective (by simpa only [one_div] using hs)
  refine ⟨hm, ?_⟩
  rw [hm] at h0
  have he := (div_left_inj' hν).mp h0
  linarith

theorem second_difference_sequence_unique (f g : ℕ → ℝ)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (hΔ : ∀ n, f (n+2)-2*f (n+1)+f n = g (n+2)-2*g (n+1)+g n) : f = g := by
  have he : ∀ n, f n = g n ∧ f (n+1) = g (n+1) := by
    intro n
    induction n with
    | zero => exact ⟨h0,h1⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hd := hΔ n
      rw [ih.1, ih.2] at hd
      linarith
  funext n
  exact (he n).1

theorem log_second_difference {x h : ℝ} (hh : 0 < h) (hx : h < x) :
    Real.log (x+h) - 2*Real.log x + Real.log (x-h) =
      Real.log (1-(h/x)^2) := by
  have hx0 : 0 < x := lt_trans hh hx
  have hp : 0 < x+h := by linarith
  have hm : 0 < x-h := sub_pos.mpr hx
  calc
    _ = Real.log (((x+h)*(x-h))/x^2) := by
      rw [Real.log_div (mul_ne_zero hp.ne' hm.ne') (pow_ne_zero 2 hx0.ne'),
        Real.log_mul hp.ne' hm.ne', Real.log_pow]
      ring
    _ = _ := by
      congr 1
      field_simp
      ring

/-- Exact discrete curvature on the full admissible unit-step domain. -/
theorem placed_discrete_curvature {μ a r : ℝ} (hμ : 0 < μ)
    (hr : -a/μ < r-1) :
    placed μ a (r+1) - 2*placed μ a r + placed μ a (r-1) =
      Real.log (1-1/(r-(-a/μ))^2) := by
  have hx : μ < μ*r+a := by
    have h := (placed_coordinate_positive hμ).mp hr
    nlinarith
  have he := log_second_difference hμ hx
  have hp : μ*(r+1)+a = (μ*r+a)+μ := by ring
  have hm : μ*(r-1)+a = (μ*r+a)-μ := by ring
  have hd : μ/(μ*r+a) = 1/(r-(-a/μ)) := by field_simp; ring
  unfold placed H SigmaPresentations.H
  rw [hp, hm]
  calc
    _ = Real.log ((μ*r+a)+μ)-2*Real.log (μ*r+a)+Real.log ((μ*r+a)-μ) := by ring
    _ = Real.log (1-(μ/(μ*r+a))^2) := he
    _ = _ := by rw [hd, div_pow, one_pow]

/-- Two consecutive values and all discrete curvatures recover both lattice directions. -/
theorem second_difference_integer_sequence_unique (f g : ℤ → ℝ)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (hΔ : ∀ n, f (n+1)-2*f n+f (n-1) = g (n+1)-2*g n+g (n-1)) : f = g := by
  have hp : ∀ n : ℕ, f n = g n ∧ f ((n : ℤ)+1) = g ((n : ℤ)+1) := by
    intro n
    induction n with
    | zero => simpa using And.intro h0 h1
    | succ n ih =>
      have hd := hΔ ((n : ℤ)+1)
      rw [add_sub_cancel_right, ih.1, ih.2] at hd
      constructor
      · simpa only [Nat.cast_add, Nat.cast_one] using ih.2
      · push_cast
        linarith
  have hn : ∀ n : ℕ, f (-(n : ℤ)) = g (-(n : ℤ)) ∧
      f (-(n : ℤ)+1) = g (-(n : ℤ)+1) := by
    intro n
    induction n with
    | zero => simpa using And.intro h0 h1
    | succ n ih =>
      have hd := hΔ (-(n : ℤ))
      rw [ih.1, ih.2] at hd
      have he : -((n+1 : ℕ) : ℤ) = -(n : ℤ)-1 := by push_cast; ring
      rw [he]
      constructor
      · linarith
      · simpa only [sub_add_cancel] using ih.1
  funext n
  cases n with
  | ofNat n => exact (hp n).1
  | negSucc n => exact (hn (n+1)).1

/-- No recurrence is required outside the admissible half-lattice. -/
theorem second_difference_half_lattice_unique (f g : ℤ → ℝ) (m k : ℤ)
    (hmk : m ≤ k) (h0 : f k = g k) (h1 : f (k+1) = g (k+1))
    (hΔ : ∀ n, m < n →
      f (n+1)-2*f n+f (n-1) = g (n+1)-2*g n+g (n-1)) :
    ∀ n, m ≤ n → f n = g n := by
  have he : ∀ n, m ≤ n → f n = g n ∧ f (n+1) = g (n+1) := by
    intro n
    refine Int.inductionOn' (C := fun j => m ≤ j → f j = g j ∧ f (j+1) = g (j+1)) n k ?_ ?_ ?_
    · exact fun _ => ⟨h0, h1⟩
    · intro j hj ih _
      have hh := ih (hmk.trans hj)
      have hd := hΔ (j+1) (by omega)
      rw [add_sub_cancel_right, hh.1, hh.2] at hd
      exact ⟨hh.2, by linarith⟩
    · intro j _ ih hn
      have hh := ih (by omega)
      have hd := hΔ j (by omega)
      rw [hh.1, hh.2] at hd
      exact ⟨by linarith, by simpa using hh.1⟩
  exact fun n hn => (he n hn).1

/-- Integer observations cannot identify a real interpolation, even up to smooth perturbations. -/
theorem integer_samples_nonidentifying (f : ℝ → ℝ) :
    ∃ g : ℝ → ℝ, (∀ n : ℤ, g n = f n) ∧ g (1/4) ≠ f (1/4) ∧
      ContDiff ℝ ⊤ (fun x => g x - f x) := by
  let p : ℝ → ℝ := fun x => Real.sin (2*Real.pi*x)
  refine ⟨fun x => f x + p x, ?_, ?_, ?_⟩
  · intro n
    have he : 2*Real.pi*(n : ℝ) = ((2*n : ℤ) : ℝ)*Real.pi := by push_cast; ring
    change f n + Real.sin (2*Real.pi*(n : ℝ)) = f n
    rw [he, Real.sin_int_mul_pi, add_zero]
  · intro he
    have hp : p (1/4) = 1 := by
      dsimp [p]
      rw [show 2*Real.pi*(1/4) = Real.pi/2 by ring, Real.sin_pi_div_two]
    simp only [hp] at he
    linarith
  · have he : (fun x => (f x + p x)-f x) = p := by funext x; ring
    rw [he]
    exact Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)

end
end Sigma
