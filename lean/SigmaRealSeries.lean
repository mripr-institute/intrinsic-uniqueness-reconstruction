import SigmaFormalSeries

/-! Formal-series proofs.  In particular the recursive
construction below proves existence for arbitrary complete triangular tower
observations; it does not assume an already constructed solution. -/
namespace Sigma
noncomputable section
open PowerSeries

def towerCoefficient (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  if hn : n = 0 then 1 else
    (a n - coeff ℚ n ((PowerSeries.mk fun j =>
      if _hj : j < n then towerCoefficient a j else 0) ^ (n + 1))) / (n + 1)
termination_by n

def towerSolution (a : ℕ → ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (towerCoefficient a)

theorem towerCoefficient_zero (a : ℕ → ℚ) : towerCoefficient a 0 = 1 := by
  rw [towerCoefficient]
  simp

theorem towerSolution_constant (a : ℕ → ℚ) :
    constantCoeff ℚ (towerSolution a) = 1 := by
  simpa [towerSolution] using towerCoefficient_zero a

theorem towerSolution_observation (a : ℕ → ℚ) (n : ℕ) (hn : 0 < n) :
    coeff ℚ n (towerSolution a ^ (n + 1)) = a n := by
  let G : PowerSeries ℚ := PowerSeries.mk fun j =>
    if j < n then towerCoefficient a j else 0
  have hG : constantCoeff ℚ G = 1 := by
    simp [G, hn, towerCoefficient_zero]
  have hlo : ∀ j < n, coeff ℚ j (towerSolution a) = coeff ℚ j G := by
    intro j hj
    simp [towerSolution, G, hj]
  have hd := SigmaPresentations.coefficient_power_difference
    (towerSolution a) G (towerSolution_constant a) hG n (n + 1) hlo
  have hGn : coeff ℚ n G = 0 := by simp [G]
  rw [map_sub, hGn, sub_zero] at hd
  have hcn : coeff ℚ n (towerSolution a) =
      (a n - coeff ℚ n (G ^ (n + 1))) / (n + 1) := by
    simp only [towerSolution, coeff_mk]
    rw [towerCoefficient, dif_neg (Nat.ne_of_gt hn)]
    simp only [dite_eq_ite]
  rw [hcn] at hd
  have hden : (n : ℚ) + 1 ≠ 0 := by positivity
  push_cast at hd
  field_simp at hd
  linarith

theorem complete_tower_exists_unique (a : ℕ → ℚ) :
    ∃! F : PowerSeries ℚ, constantCoeff ℚ F = 1 ∧
      ∀ n > 0, coeff ℚ n (F ^ (n + 1)) = a n := by
  refine ⟨towerSolution a, ⟨towerSolution_constant a,
    fun n hn => towerSolution_observation a n hn⟩, ?_⟩
  intro F hF
  apply SigmaPresentations.todd_observations_injective F (towerSolution a)
    hF.1 (towerSolution_constant a)
  intro n hn
  rw [hF.2 n hn, towerSolution_observation a n hn]

theorem todd_tower_exists_unique :
    ∃! F : PowerSeries ℚ, constantCoeff ℚ F = 1 ∧
      ∀ n > 0, coeff ℚ n (F ^ (n + 1)) = 1 :=
  complete_tower_exists_unique (fun _ => 1)

theorem degree_zero_tower_is_normalization (F : PowerSeries ℚ) :
    coeff ℚ 0 (F ^ (0 + 1)) = 1 ↔ constantCoeff ℚ F = 1 := by simp

theorem omitted_todd_degree (N : ℕ) (hN : 0 < N) :
    ∃ F G : PowerSeries ℚ,
      constantCoeff ℚ F = 1 ∧ constantCoeff ℚ G = 1 ∧ F ≠ G ∧
      (∀ n > 0, coeff ℚ n (F ^ (n + 1)) = 1) ∧
      (∀ n > 0, n ≠ N → coeff ℚ n (G ^ (n + 1)) = 1) := by
  let a : ℕ → ℚ := fun n => if n = N then 2 else 1
  refine ⟨towerSolution (fun _ => 1), towerSolution a,
    towerSolution_constant _, towerSolution_constant _, ?_,
    fun n hn => towerSolution_observation _ n hn, ?_⟩
  · intro h
    have h1 := towerSolution_observation (fun _ => 1) N hN
    have h2 := towerSolution_observation a N hN
    rw [h] at h1
    have haN : a N = 2 := by simp [a]
    rw [haN] at h2
    change coeff ℚ N (towerSolution a ^ (N + 1)) = 1 at h1
    linarith
  · intro n hn hnN
    rw [towerSolution_observation a n hn]
    simp [a, hnN]

def formalToddToL (T : PowerSeries ℚ) : PowerSeries ℚ := rescale 2 T - X
def formalLToTodd (L : PowerSeries ℚ) : PowerSeries ℚ :=
  rescale (1 / 2 : ℚ) L + C ℚ (1 / 2) * X

theorem formal_L_Todd_inverse (T : PowerSeries ℚ) :
    formalLToTodd (formalToddToL T) = T := by
  simp [formalLToTodd, formalToddToL, map_sub, rescale_rescale, rescale_X]

theorem formal_Todd_L_inverse (L : PowerSeries ℚ) :
    formalToddToL (formalLToTodd L) = L := by
  apply PowerSeries.ext
  intro n
  simp only [formalToddToL, formalLToTodd, map_add, map_sub,
    coeff_rescale, coeff_C_mul, coeff_X]
  rw [← mul_assoc, ← mul_pow]
  norm_num
  split_ifs with hn
  · subst n
    norm_num
  · simp

def formalToddToChi (y : ℚ) (T : PowerSeries ℚ) : PowerSeries ℚ :=
  rescale (1 + y) T - C ℚ y * X

def formalChiToTodd (y : ℚ) (Q : PowerSeries ℚ) : PowerSeries ℚ :=
  rescale (1 + y)⁻¹ Q + C ℚ (y / (1 + y)) * X

theorem formal_chi_Todd_inverse (y : ℚ) (hy : y ≠ -1) (T : PowerSeries ℚ) :
    formalChiToTodd y (formalToddToChi y T) = T := by
  have h : 1 + y ≠ 0 := by intro h; apply hy; linarith
  apply PowerSeries.ext
  intro n
  simp only [formalChiToTodd, formalToddToChi, map_add, map_sub,
    coeff_rescale, coeff_C_mul, coeff_X]
  rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ h, one_pow, one_mul]
  split_ifs with hn
  · subst n
    simp
    field_simp
  · simp

theorem formal_Todd_chi_inverse (y : ℚ) (hy : y ≠ -1) (Q : PowerSeries ℚ) :
    formalToddToChi y (formalChiToTodd y Q) = Q := by
  have h : 1 + y ≠ 0 := by intro h; apply hy; linarith
  apply PowerSeries.ext
  intro n
  simp only [formalChiToTodd, formalToddToChi, map_add, map_sub,
    coeff_rescale, coeff_C_mul, coeff_X]
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ h, one_pow, one_mul]
  split_ifs with hn
  · subst n
    simp
    field_simp
  · simp

theorem formal_chi_minus_one (T : PowerSeries ℚ)
    (hT : constantCoeff ℚ T = 1) : formalToddToChi (-1) T = 1 + X := by
  simp [formalToddToChi, rescale_zero_apply, hT]

theorem formal_chi_reconstruction_iff (y : ℚ) (hy : y ≠ -1)
    (T U : PowerSeries ℚ) : formalToddToChi y T = formalToddToChi y U ↔ T = U := by
  constructor
  · intro h
    have hh := congrArg (formalChiToTodd y) h
    simpa [formal_chi_Todd_inverse y hy] using hh
  · rintro rfl
    rfl

theorem universal_line_correction_unique (C D : PowerSeries ℚ)
    (h : X * C = X * D) : C = D :=
  mul_left_cancel₀ PowerSeries.X_ne_zero h

theorem universal_unit_inverse_reconstruction (T U : (PowerSeries ℚ)ˣ) :
    T⁻¹ = U⁻¹ ↔ T = U := inv_inj

end
end Sigma
