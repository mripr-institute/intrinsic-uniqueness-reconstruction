import SigmaOpSpectralMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Sigma
noncomputable section
open scoped ENNReal

def reciprocalSpectralCoordinate (t : ℝ) (ht : 0 ≤ t) : OpUnitInterval :=
  ⟨(1+t)⁻¹, inv_nonneg.mpr (by linarith), inv_le_one_of_one_le₀ (by linarith)⟩

theorem reciprocal_spectral_coordinate_ne_zero (t : ℝ) (ht : 0 ≤ t) :
    (reciprocalSpectralCoordinate t ht : ℝ) ≠ 0 := inv_ne_zero (by linarith)

theorem reciprocal_spectral_coordinate_injective (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (h : reciprocalSpectralCoordinate t ht = reciprocalSpectralCoordinate u hu) : t = u := by
  have he := congrArg (fun x : OpUnitInterval => (x : ℝ)) h
  change (1+t)⁻¹ = (1+u)⁻¹ at he
  exact add_left_cancel (inv_injective he)

/-- Integer shifted spectral data recover the whole eigenvalue multiset.
The exponent q permits tail data; q=2 is exactly the paper's integer category. -/
theorem integer_shifted_spectral_data_equiv {ι κ : Type*}
    (lam : ι → ℝ) (μ : κ → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hμ : ∀ j, 0 ≤ μ j)
    (q : ℕ) (hlamsum : Summable (fun i => ((1+lam i)⁻¹)^q))
    (hμsum : Summable (fun j => ((1+μ j)⁻¹)^q))
    (hdata : ∀ n : ℕ, (∑' i, ((1+lam i)⁻¹)^(n+q)) =
      ∑' j, ((1+μ j)⁻¹)^(n+q)) :
    ∃ e : ι ≃ κ, ∀ i, μ (e i) = lam i := by
  obtain ⟨e, he⟩ := spectral_integer_moments_equiv
    (fun i => reciprocalSpectralCoordinate (lam i) (hlam i))
    (fun j => reciprocalSpectralCoordinate (μ j) (hμ j)) q hlamsum hμsum
    (fun i => reciprocal_spectral_coordinate_ne_zero _ _)
    (fun j => reciprocal_spectral_coordinate_ne_zero _ _) hdata
  exact ⟨e, fun i => reciprocal_spectral_coordinate_injective _ _ _ _ (he i)⟩

/-- Heat traces on any terminal ray suffice. Finiteness is required only on
that ray, and finite or empty spectra are included. -/
theorem heat_spectral_data_equiv {ι κ : Type*}
    (lam : ι → ℝ) (μ : κ → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hμ : ∀ j, 0 ≤ μ j)
    (t₀ : ℝ)
    (hlamsum : ∀ t : ℝ, t₀ < t → Summable (fun i => Real.exp (-t * lam i)))
    (hμsum : ∀ t : ℝ, t₀ < t → Summable (fun j => Real.exp (-t * μ j)))
    (hdata : ∀ t : ℝ, t₀ < t → (∑' i, Real.exp (-t * lam i)) =
      ∑' j, Real.exp (-t * μ j)) :
    ∃ e : ι ≃ κ, ∀ i, μ (e i) = lam i := by
  obtain ⟨q, hq⟩ := exists_nat_gt t₀
  let x : ι → OpUnitInterval := fun i => opExpCoordinate ⟨lam i, hlam i⟩
  let y : κ → OpUnitInterval := fun j => opExpCoordinate ⟨μ j, hμ j⟩
  have hp (t : ℝ) (n : ℕ) : Real.exp (-t)^n = Real.exp (-(n : ℝ)*t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hx : Summable (fun i => (x i : ℝ)^q) := by
    simpa only [x, opExpCoordinate, hp] using hlamsum q hq
  have hy : Summable (fun j => (y j : ℝ)^q) := by
    simpa only [y, opExpCoordinate, hp] using hμsum q hq
  have hm (n : ℕ) : (∑' i, (x i : ℝ)^(n+q)) = ∑' j, (y j : ℝ)^(n+q) := by
    have hh : t₀ < ((n+q : ℕ) : ℝ) := by
      push_cast
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    simpa only [x, y, opExpCoordinate, hp] using
      hdata ((n+q : ℕ) : ℝ) hh
  obtain ⟨e, he⟩ := spectral_integer_moments_equiv x y q hx hy
    (fun i => Real.exp_ne_zero _) (fun j => Real.exp_ne_zero _) hm
  refine ⟨e, fun i => ?_⟩
  have h := congrArg (fun z : OpUnitInterval => (z : ℝ)) (he i)
  change Real.exp (-(μ (e i))) = Real.exp (-(lam i)) at h
  exact neg_injective (Real.exp_injective h)

/-- Shifted zeta data on any real terminal ray determine multiplicities as
well as eigenvalues, by the actual finite-measure inverse. -/
theorem zeta_spectral_data_equiv {ι κ : Type*}
    (lam : ι → ℝ) (μ : κ → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hμ : ∀ j, 0 ≤ μ j)
    (s₀ : ℝ)
    (hlamsum : ∀ s : ℝ, s₀ < s → Summable (fun i => (1+lam i)^(-s)))
    (hμsum : ∀ s : ℝ, s₀ < s → Summable (fun j => (1+μ j)^(-s)))
    (hdata : ∀ s : ℝ, s₀ < s → (∑' i, (1+lam i)^(-s)) = ∑' j, (1+μ j)^(-s)) :
    ∃ e : ι ≃ κ, ∀ i, μ (e i) = lam i := by
  obtain ⟨q, hq⟩ := exists_nat_gt s₀
  have hp (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
      (1+t)^(-(n : ℝ)) = ((1+t)⁻¹)^n := by
    rw [Real.rpow_neg (by linarith : 0 ≤ 1+t), Real.rpow_natCast, inv_pow]
  apply integer_shifted_spectral_data_equiv lam μ hlam hμ q
  · simpa only [hp _ (hlam _) q] using hlamsum q hq
  · simpa only [hp _ (hμ _) q] using hμsum q hq
  · intro n
    have hh : s₀ < ((n+q : ℕ) : ℝ) := by
      push_cast
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    simpa only [hp _ (hlam _) (n+q), hp _ (hμ _) (n+q)] using
      hdata ((n+q : ℕ) : ℝ) hh

end
end Sigma
