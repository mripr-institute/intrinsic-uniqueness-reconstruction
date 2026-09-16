import SigmaReconstruction
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Scalar reconstruction and explicit reversible algebra.
The final build script regenerates every local imported object before this file.
All analytic candidate-class assumptions occur in the theorem signatures.
-/
namespace SigmaPresentations
noncomputable section

open SigmaBase

def H (t : ℝ) : ℝ := Real.log t - t + 1
def density (t : ℝ) : ℝ := t * Real.exp (-t)
def centeredCGF (u : ℝ) : ℝ := Real.exp u - 1 - u
def poissonPotential (t : ℝ) : ℝ := t * Real.log t - t + 1

theorem H_eq_neg_potential (t : ℝ) : H t = -potential t := by
  unfold H potential
  ring

theorem density_eq_exp_H {t : ℝ} (ht : 0 < t) :
    density t = Real.exp (H t - 1) := by
  have he : H t - 1 = Real.log t + (-t) := by unfold H; ring
  rw [he, Real.exp_add, Real.exp_log ht]
  rfl

theorem density_eq_exp_potential {t : ℝ} (ht : 0 < t) :
    density t = Real.exp (-1 - potential t) := by
  rw [density_eq_exp_H ht, H_eq_neg_potential]
  congr 1
  ring

theorem density_pos {t : ℝ} (ht : 0 < t) : 0 < density t := by
  exact mul_pos ht (Real.exp_pos _)

theorem reconstruct_derivative (phi : ℝ → ℝ)
    (hdiff : DifferentiableOn ℝ phi (Set.Ioi 0))
    (hnorm : phi 1 = 0)
    (hderiv : ∀ t > 0, deriv phi t = 1 - 1 / t) :
    ∀ t > 0, phi t = potential t :=
  reconstruct_from_derivative phi hdiff hnorm hderiv

/-- Cancellation away from the basepoint is the identifying step. -/
theorem symmetric_slice_identifies_derivative {t d : ℝ}
    (ht : t ≠ 0) (hne : t ≠ 1)
    (h : (t - 1) * d = t + 1 / t - 2) : d = 1 - 1 / t := by
  have hp : (t - 1) * (d - (1 - 1 / t)) = 0 := by
    calc
      _ = (t - 1) * d - (t + 1 / t - 2) := by field_simp; ring
      _ = 0 := by rw [h]; ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hne))

theorem reconstruct_anchored_symmetric_bregman (phi : ℝ → ℝ)
    (hdiff : DifferentiableOn ℝ phi (Set.Ioi 0))
    (hvalue : phi 1 = 0) (hslope : deriv phi 1 = 0)
    (hsym : ∀ t > 0,
      bregman phi (deriv phi) t 1 + bregman phi (deriv phi) 1 t =
        t + 1 / t - 2) :
    ∀ t > 0, phi t = potential t := by
  apply reconstruct_from_derivative phi hdiff hvalue
  intro t ht
  by_cases he : t = 1
  · simp [he, hslope]
  · apply symmetric_slice_identifies_derivative (ne_of_gt ht) he
    simpa [symmetric_bregman, hslope] using hsym t ht

/-- Differentiate the actual group homomorphism equation at its identity. -/
theorem normalized_group_log_derivative (L : ℝ → ℝ)
    (hdiff : DifferentiableOn ℝ L (Set.Ioi (-1)))
    (hnorm : HasDerivAt L 1 0)
    (hhom : ∀ x > -1, ∀ y > -1, L (star x y) = L x + L y)
    (x : ℝ) (hx : -1 < x) : HasDerivAt L (1 / (1 + x)) x := by
  have hd := ((hdiff x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
  have hi : HasDerivAt (fun y => star x y) (1 + x) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_mul (1 + x)).const_add x) using 1
    · funext y
      unfold SigmaBase.star
      simp only [id_eq]
      ring
    · ring
  have hd0 : HasDerivAt L (deriv L x) (star x 0) := by
    simpa only [SigmaBase.star_zero] using hd
  have hlhs := hd0.comp 0 hi
  have hrhs : HasDerivAt (fun y => L (star x y)) 1 0 := by
    apply (hnorm.const_add (L x)).congr_of_eventuallyEq
    filter_upwards [show ∀ᶠ y in nhds (0 : ℝ), -1 < y from
      isOpen_Ioi.mem_nhds (by norm_num)] with y hy
    exact hhom x hx y hy
  have he : deriv L x * (1 + x) = 1 := hlhs.unique hrhs
  have he' : deriv L x = 1 / (1 + x) :=
    (eq_div_iff (ne_of_gt (by linarith))).mpr he
  rwa [he'] at hd

/-- A differentiable homomorphism for x+y+xy, normalized at the identity,
is the complete logarithm on its intrinsic connected domain. -/
theorem normalized_group_log_unique (L : ℝ → ℝ)
    (hdiff : DifferentiableOn ℝ L (Set.Ioi (-1)))
    (hnorm : HasDerivAt L 1 0)
    (hhom : ∀ x > -1, ∀ y > -1, L (star x y) = L x + L y) :
    ∀ x > -1, L x = Real.log (1 + x) := by
  have hzero : L 0 = 0 := by
    have h := hhom 0 (by norm_num) 0 (by norm_num)
    simp only [SigmaBase.star_zero] at h
    linarith
  have hz : ∀ x ∈ Set.Ioi (-1 : ℝ),
      HasDerivWithinAt (fun z => L z - Real.log (1 + z)) 0 (Set.Ioi (-1)) x := by
    intro x hx
    change -1 < x at hx
    have hl : HasDerivAt (fun z => Real.log (1 + z)) (1 / (1 + x)) x := by
      simpa [one_div] using
        (Real.hasDerivAt_log (ne_of_gt (by linarith : 0 < 1 + x))).comp x
          ((hasDerivAt_id x).const_add 1)
    simpa using ((normalized_group_log_derivative L hdiff hnorm hhom x hx).sub hl).hasDerivWithinAt
  intro x hx
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hz
    (by intro y hy; simp) (convex_Ioi (-1 : ℝ))
    (show (0 : ℝ) ∈ Set.Ioi (-1) by norm_num) hx
  have he : L x - Real.log (1 + x) - (L 0 - Real.log (1 + 0)) = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa using hb) (norm_nonneg _)
  apply sub_eq_zero.mp
  simpa [hzero] using he

/-- The recurrence determines all masses from the zeroth mass, before normalization. -/
theorem poisson_recurrence_factorial (pi : ℕ → ℝ)
    (hrec : ∀ n, ((n + 1 : ℕ) : ℝ) * pi (n + 1) = pi n) :
    ∀ n, (n.factorial : ℝ) * pi n = pi 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul]
    calc
      ((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) * pi (n + 1) =
          (n.factorial : ℝ) * (((n + 1 : ℕ) : ℝ) * pi (n + 1)) := by ring
      _ = pi 0 := by rw [hrec, ih]

theorem poisson_recurrence_solution (pi : ℕ → ℝ)
    (hrec : ∀ n, ((n + 1 : ℕ) : ℝ) * pi (n + 1) = pi n) (n : ℕ) :
    pi n = pi 0 / (n.factorial : ℝ) := by
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero n)).mpr
  simpa [mul_comm] using poisson_recurrence_factorial pi hrec n

theorem inverse_factorial_hasSum :
    HasSum (fun n : ℕ => 1 / (n.factorial : ℝ)) (Real.exp 1) := by
  simpa [Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp ℝ (1 : ℝ))

/-- Total mass determines the remaining constant; nonnegativity is then a consequence. -/
theorem poisson_normalized_recurrence (pi : ℕ → ℝ)
    (hrec : ∀ n, ((n + 1 : ℕ) : ℝ) * pi (n + 1) = pi n)
    (hmass : HasSum pi 1) (n : ℕ) :
    pi n = Real.exp (-1) / (n.factorial : ℝ) := by
  have hs : HasSum pi (pi 0 * Real.exp 1) := by
    convert inverse_factorial_hasSum.mul_left (pi 0) using 1
    funext k
    rw [poisson_recurrence_solution pi hrec k]
    ring
  have hzero : pi 0 = Real.exp (-1) := by
    rw [Real.exp_neg, ← one_div]
    exact (eq_div_iff (Real.exp_ne_zero 1)).mpr (hs.unique hmass)
  rw [poisson_recurrence_solution pi hrec n, hzero]

theorem poisson_mgf_hasSum (u : ℝ) :
    HasSum (fun n : ℕ => (Real.exp (-1) / (n.factorial : ℝ)) *
      Real.exp ((n : ℝ) * u)) (Real.exp (Real.exp u - 1)) := by
  have hs : HasSum (fun n : ℕ => (Real.exp u) ^ n / (n.factorial : ℝ))
      (Real.exp (Real.exp u)) := by
    simpa [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ℝ (Real.exp u))
  convert hs.mul_left (Real.exp (-1)) using 1
  · funext n
    rw [Real.exp_nat_mul]
    ring
  · rw [← Real.exp_add]
    congr 1
    ring

theorem centeredCGF_hasDerivAt (u : ℝ) :
    HasDerivAt centeredCGF (Real.exp u - 1) u := by
  simpa [centeredCGF] using ((Real.hasDerivAt_exp u).sub_const 1).sub (hasDerivAt_id u)

theorem centeredCGF_anchors : centeredCGF 0 = 0 ∧ deriv centeredCGF 0 = 0 := by
  constructor
  · simp [centeredCGF]
  · rw [(centeredCGF_hasDerivAt 0).deriv]
    simp

theorem centeredCGF_recovers_exp (u : ℝ) :
    1 + deriv centeredCGF u = Real.exp u := by
  rw [(centeredCGF_hasDerivAt u).deriv]
  ring

theorem poisson_KL_slice {t : ℝ} (ht : 0 < t) :
    Real.log (1 / t) - 1 + t = potential t := by
  rw [Real.log_div (by norm_num) (ne_of_gt ht)]
  simp [potential]
  ring

theorem poisson_mean_bregman {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    bregman poissonPotential Real.log a b = a * Real.log (a / b) - a + b := by
  unfold bregman poissonPotential
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)]
  ring

theorem poisson_KL_orientation {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * Real.log (a / b) - a + b = a * potential (b / a) := by
  unfold potential
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb),
    Real.log_div (ne_of_gt hb) (ne_of_gt ha)]
  field_simp
  ring

theorem centeredCGF_bregman (u v : ℝ) :
    bregman centeredCGF (fun z => Real.exp z - 1) u v =
      Real.exp v * potential (Real.exp (u - v)) := by
  unfold bregman centeredCGF potential
  rw [Real.log_exp, Real.exp_sub]
  field_simp
  ring

/-- A local conservative second-order expression applied to a supplied 2-jet. -/
def localExpression (a b first second : ℝ) : ℝ := -a * second - b * first

/-- Exact jets of 2-t and t²/2-3t+3 identify both coefficients pointwise. -/
theorem low2_identification (a b t : ℝ)
    (hlinear : localExpression a b (-1) 0 = 2 - t)
    (hquadratic : localExpression a b (t - 3) 1 =
      2 * (t ^ 2 / 2 - 3 * t + 3)) : a = t ∧ b = 2 - t := by
  unfold localExpression at *
  have hb : b = 2 - t := by linarith
  constructor
  · rw [hb] at hquadratic
    nlinarith
  · exact hb

theorem low2_canonical (t : ℝ) :
    localExpression t (2 - t) (-1) 0 = 2 - t ∧
    localExpression t (2 - t) (t - 3) 1 =
      2 * (t ^ 2 / 2 - 3 * t + 3) := by
  constructor <;> unfold localExpression <;> ring

def linearEigenfunction (t : ℝ) : ℝ := 2 - t
def quadraticEigenfunction (t : ℝ) : ℝ := t ^ 2 / 2 - 3 * t + 3
def differentialExpression (a b f : ℝ → ℝ) (t : ℝ) : ℝ :=
  localExpression (a t) (b t) (deriv f t) (deriv (deriv f) t)

theorem linearEigenfunction_deriv :
    deriv linearEigenfunction = fun _ => (-1 : ℝ) := by
  funext t
  have hd : HasDerivAt linearEigenfunction (-1) t := by
    simpa [linearEigenfunction] using (hasDerivAt_const t (2 : ℝ)).sub (hasDerivAt_id t)
  exact hd.deriv

theorem quadraticEigenfunction_deriv :
    deriv quadraticEigenfunction = fun t => t - 3 := by
  funext t
  have hd : HasDerivAt quadraticEigenfunction (t - 3) t := by
    convert ((((hasDerivAt_id t).pow 2).div_const 2).sub
      ((hasDerivAt_id t).const_mul 3)).add_const 3 using 1
    simp [quadraticEigenfunction]
  exact hd.deriv

/-- Two actual differential eigenfunction identities identify the expression. -/
theorem differential_low2_identification (a b : ℝ → ℝ)
    (hlinear : ∀ t > 0,
      differentialExpression a b linearEigenfunction t = linearEigenfunction t)
    (hquadratic : ∀ t > 0,
      differentialExpression a b quadraticEigenfunction t = 2 * quadraticEigenfunction t) :
    ∀ t > 0, a t = t ∧ b t = 2 - t := by
  intro t ht
  have hl := hlinear t ht
  have hq := hquadratic t ht
  have hdq : deriv (fun t : ℝ => t - 3) t = 1 :=
    ((hasDerivAt_id t).sub_const 3).deriv
  simp only [differentialExpression, linearEigenfunction_deriv,
    quadraticEigenfunction_deriv, deriv_const, hdq,
    linearEigenfunction, quadraticEigenfunction] at hl hq
  exact low2_identification (a t) (b t) t hl hq

def toddToL (T : ℝ → ℝ) (u : ℝ) : ℝ := T (2 * u) - u
def lToTodd (L : ℝ → ℝ) (u : ℝ) : ℝ := L (u / 2) + u / 2

/-- Canonical real representatives with their removable value filled at zero. -/
def todd (u : ℝ) : ℝ := if u = 0 then 1 else u / (1 - Real.exp (-u))
def lSeries (u : ℝ) : ℝ :=
  if u = 0 then 1 else u * (Real.exp (2 * u) + 1) / (Real.exp (2 * u) - 1)
def ahat (u : ℝ) : ℝ :=
  if u = 0 then 1 else u / (Real.exp (u / 2) - Real.exp (-(u / 2)))

theorem canonical_todd_to_L : toddToL todd = lSeries := by
  funext u
  by_cases hu : u = 0
  · simp [hu, toddToL, todd, lSeries]
  · have h2u : 2 * u ≠ 0 := mul_ne_zero (by norm_num) hu
    have he : Real.exp (2 * u) - 1 ≠ 0 :=
      sub_ne_zero.mpr (fun h => h2u (by simpa using h))
    simp only [toddToL, todd, lSeries, if_neg hu, if_neg h2u, Real.exp_neg]
    field_simp
    ring

theorem canonical_L_recovers_exp (u : ℝ) :
    (lSeries u + u) / (lSeries u - u) = Real.exp (2 * u) := by
  by_cases hu : u = 0
  · simp [hu, lSeries]
  · have h2u : 2 * u ≠ 0 := mul_ne_zero (by norm_num) hu
    have he : Real.exp (2 * u) - 1 ≠ 0 :=
      sub_ne_zero.mpr (fun h => h2u (by simpa using h))
    simp only [lSeries, if_neg hu]
    field_simp [hu]
    ring_nf
    field_simp [hu]

theorem lToTodd_toddToL (T : ℝ → ℝ) : lToTodd (toddToL T) = T := by
  funext u
  simp only [lToTodd, toddToL, sub_add_cancel]
  congr 1
  ring

theorem toddToL_lToTodd (L : ℝ → ℝ) : toddToL (lToTodd L) = L := by
  funext u
  simp [lToTodd, toddToL]

def toddLEquiv : (ℝ → ℝ) ≃ (ℝ → ℝ) where
  toFun := toddToL
  invFun := lToTodd
  left_inv := lToTodd_toddToL
  right_inv := toddToL_lToTodd

def toddToAhat (T : ℝ → ℝ) (u : ℝ) : ℝ := Real.exp (-(u / 2)) * T u
def ahatToTodd (A : ℝ → ℝ) (u : ℝ) : ℝ := Real.exp (u / 2) * A u

theorem canonical_ahat_to_todd : ahatToTodd ahat = todd := by
  funext u
  by_cases hu : u = 0
  · simp [hu, ahatToTodd, ahat, todd]
  · have he : 1 - Real.exp (-u) ≠ 0 := by
      intro h
      have hz : -u = 0 := by simpa using (show Real.exp (-u) = 1 by linarith)
      exact hu (neg_eq_zero.mp hz)
    have hh : Real.exp (u / 2) - Real.exp (-(u / 2)) ≠ 0 := by
      intro h
      have hz := Real.exp_injective (sub_eq_zero.mp h)
      apply hu
      linarith
    simp only [ahatToTodd, ahat, todd, if_neg hu]
    have hh' : Real.exp (u / 2) - Real.exp (-u / 2) ≠ 0 := by
      simpa only [neg_div] using hh
    field_simp [hh', he]
    have hc : Real.exp (u / 2) * Real.exp (-u) = Real.exp (-u / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    linear_combination -u * hc

theorem ahatToTodd_toddToAhat (T : ℝ → ℝ) : ahatToTodd (toddToAhat T) = T := by
  funext u
  simp [ahatToTodd, toddToAhat, ← mul_assoc, ← Real.exp_add]

theorem toddToAhat_ahatToTodd (A : ℝ → ℝ) : toddToAhat (ahatToTodd A) = A := by
  funext u
  simp [ahatToTodd, toddToAhat, ← mul_assoc, ← Real.exp_add]

def toddAhatEquiv : (ℝ → ℝ) ≃ (ℝ → ℝ) where
  toFun := toddToAhat
  invFun := ahatToTodd
  left_inv := ahatToTodd_toddToAhat
  right_inv := toddToAhat_ahatToTodd

def toddToChi (y : ℝ) (T : ℝ → ℝ) (u : ℝ) : ℝ := T ((1 + y) * u) - y * u
def chiToTodd (y : ℝ) (C : ℝ → ℝ) (u : ℝ) : ℝ :=
  C (u / (1 + y)) + y * (u / (1 + y))

theorem chiToTodd_toddToChi {y : ℝ} (hy : y ≠ -1) (T : ℝ → ℝ) :
    chiToTodd y (toddToChi y T) = T := by
  have hn : 1 + y ≠ 0 := by intro h; apply hy; linarith
  funext u
  simp only [chiToTodd, toddToChi, sub_add_cancel]
  congr 1
  field_simp

theorem toddToChi_chiToTodd {y : ℝ} (hy : y ≠ -1) (C : ℝ → ℝ) :
    toddToChi y (chiToTodd y C) = C := by
  have hn : 1 + y ≠ 0 := by intro h; apply hy; linarith
  funext u
  simp [chiToTodd, toddToChi, hn]

def toddChiEquiv (y : ℝ) (hy : y ≠ -1) : (ℝ → ℝ) ≃ (ℝ → ℝ) where
  toFun := toddToChi y
  invFun := chiToTodd y
  left_inv := chiToTodd_toddToChi hy
  right_inv := toddToChi_chiToTodd hy

theorem chi_minus_one_degenerate (T : ℝ → ℝ) (hT : T 0 = 1) (u : ℝ) :
    toddToChi (-1) T u = 1 + u := by simp [toddToChi, hT]

theorem positive_quadratic_branch_unique {w v b : ℝ} (hw : 0 < w) (hv : 0 < v)
    (hew : w - 1 / w = b) (hev : v - 1 / v = b) : w = v := by
  have hw0 := ne_of_gt hw
  have hv0 := ne_of_gt hv
  field_simp at hew hev
  nlinarith [mul_pos hw hv, sq_nonneg (w - v)]

def positiveQuadraticRoot (b : ℝ) : ℝ := (b + Real.sqrt (b ^ 2 + 4)) / 2

theorem positiveQuadraticRoot_spec (b : ℝ) :
    0 < positiveQuadraticRoot b ∧
    positiveQuadraticRoot b - 1 / positiveQuadraticRoot b = b := by
  have hs : 0 < Real.sqrt (b ^ 2 + 4) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ b ^ 2 + 4 by positivity)
  have hb : -b < Real.sqrt (b ^ 2 + 4) := by nlinarith [sq_nonneg b]
  have hw : 0 < positiveQuadraticRoot b := by unfold positiveQuadraticRoot; linarith
  refine ⟨hw, ?_⟩
  have hp : (positiveQuadraticRoot b) ^ 2 - b * positiveQuadraticRoot b = 1 := by
    unfold positiveQuadraticRoot
    nlinarith
  have hn := ne_of_gt hw
  field_simp
  nlinarith

theorem canonical_ahat_recovers_exp (u : ℝ) :
    positiveQuadraticRoot (u / ahat u) = Real.exp (u / 2) := by
  have hs := positiveQuadraticRoot_spec (u / ahat u)
  apply positive_quadratic_branch_unique hs.1 (Real.exp_pos _) hs.2
  by_cases hu : u = 0
  · simp [hu, ahat]
  · have hh : Real.exp (u / 2) - Real.exp (-u / 2) ≠ 0 := by
      intro h
      have hz := Real.exp_injective (sub_eq_zero.mp h)
      apply hu
      linarith
    simp only [ahat, if_neg hu, neg_div]
    rw [one_div, ← Real.exp_neg]
    field_simp [hu, hh]


def blockPotential (xs : List ℝ) : ℝ := (xs.map potential).sum

theorem blockPotential_append (xs ys : List ℝ) :
    blockPotential (xs ++ ys) = blockPotential xs + blockPotential ys := by
  simp [blockPotential]

theorem block_reconstruction (F : List ℝ → ℝ) (phi : ℝ → ℝ)
    (hempty : F [] = 0) (hcons : ∀ x xs, F (x :: xs) = phi x + F xs)
    (hdiff : DifferentiableOn ℝ phi (Set.Ioi 0)) (hvalue : phi 1 = 0)
    (hderiv : ∀ t > 0, deriv phi t = 1 - 1 / t)
    (xs : List ℝ) (hpos : ∀ x ∈ xs, 0 < x) : F xs = blockPotential xs := by
  rw [list_scalar_assembly F phi hempty hcons]
  unfold blockPotential
  congr 1
  apply List.map_congr_left
  intro x hx
  exact reconstruct_from_derivative phi hdiff hvalue hderiv x (hpos x hx)

/-- Explicit transformations above preserve equality exactly, hence reconstruction. -/
theorem closure_under_todd_L (F G : ℝ → ℝ) : toddToL F = toddToL G ↔ F = G :=
  toddLEquiv.injective.eq_iff

theorem closure_under_todd_Ahat (F G : ℝ → ℝ) : toddToAhat F = toddToAhat G ↔ F = G :=
  toddAhatEquiv.injective.eq_iff

theorem closure_under_todd_chi (y : ℝ) (hy : y ≠ -1) (F G : ℝ → ℝ) :
    toddToChi y F = toddToChi y G ↔ F = G :=
  (toddChiEquiv y hy).injective.eq_iff

end
end SigmaPresentations
