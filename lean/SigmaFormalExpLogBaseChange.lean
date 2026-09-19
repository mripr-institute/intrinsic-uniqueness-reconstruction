import SigmaFormalExpLog
import SigmaRealToddAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Sigma
noncomputable section
open PowerSeries
open scoped BigOperators

/-- Coefficientwise formal substitution over a commutative coefficient ring.
As usual its interpretation as substitution requires the inner constant to
vanish; all inverse identities below have this property. -/
def formalComposeOver {A : Type*} [CommRing A] (F G : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n => ∑ j ∈ Finset.range (n+1), coeff A j F*coeff A n (G^j)

theorem formal_compose_over_field {K : Type*} [Field K] (F G : PowerSeries K) :
    formalComposeOver F G=formalCompose F G := rfl

theorem formal_compose_over_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (F G : PowerSeries A) :
    PowerSeries.map f (formalComposeOver F G)=
      formalComposeOver (PowerSeries.map f F) (PowerSeries.map f G) := by
  ext n
  simp only [coeff_map, formalComposeOver, coeff_mk, map_sum, map_mul,
    ← map_pow, coeff_map]

/-- Substitution by a tangent-to-identity series is injective over any
commutative ring, including rings with zero divisors. -/
theorem formal_compose_over_injective {A : Type*} [CommRing A]
    (G : PowerSeries A) (h0 : constantCoeff A G=0) (h1 : coeff A 1 G=1) :
    Function.Injective (fun F => formalComposeOver F G) := by
  obtain ⟨D,hD⟩ := X_dvd_iff.mpr h0
  have hd : constantCoeff A D=1 := by
    have he := coeff_X_pow_mul D 1 0
    simpa only [pow_one, Nat.add_zero, coeff_zero_eq_constantCoeff_apply, ← hD, h1] using he.symm
  have hn (n : ℕ) : coeff A n (G^n)=1 := by
    rw [hD, mul_pow]
    have he := coeff_X_pow_mul (D^n) n 0
    simpa [hd] using he
  intro F H he
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hc := congrArg (coeff A n) he
    simp only [formalComposeOver, coeff_mk, Finset.sum_range_succ, hn, mul_one] at hc
    have hs : (∑ j ∈ Finset.range n, coeff A j F*coeff A n (G^j))=
        ∑ j ∈ Finset.range n, coeff A j H*coeff A n (G^j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih j (Finset.mem_range.mp hj)]
    exact add_left_cancel (hs ▸ hc)

variable (A : Type*) [CommRing A] [Algebra ℚ A]

def formalLogarithmOver : PowerSeries A :=
  PowerSeries.map (algebraMap ℚ A) SigmaPresentations.formalLog

theorem formal_logarithm_over_constant : constantCoeff A (formalLogarithmOver A)=0 := by
  simp [formalLogarithmOver, ← coeff_zero_eq_constantCoeff_apply,
    coeff_map, SigmaPresentations.formalLog]

theorem formal_exp_log_over_inverse :
    formalComposeOver (formalExponentialOver A 1-1) (formalLogarithmOver A)=X := by
  have h := congrArg (PowerSeries.map (algebraMap ℚ A)) (formal_exp_log_inverse ℚ)
  change PowerSeries.map (algebraMap ℚ A)
    (formalComposeOver (formalExponential ℚ 1-1) (formalLogarithm ℚ))=_ at h
  rw [formal_compose_over_map, map_sub, map_one, formal_exponential_over_map, map_one] at h
  simpa only [PowerSeries.map_X, formalLogarithmOver, formal_logarithm_rational] using h

theorem formal_log_exp_over_inverse :
    formalComposeOver (formalLogarithmOver A) (formalExponentialOver A 1-1)=X := by
  have h := congrArg (PowerSeries.map (algebraMap ℚ A)) (formal_log_exp_inverse ℚ)
  change PowerSeries.map (algebraMap ℚ A)
    (formalComposeOver (formalLogarithm ℚ) (formalExponential ℚ 1-1))=_ at h
  rw [formal_compose_over_map, map_sub, map_one, formal_exponential_over_map, map_one] at h
  simpa only [PowerSeries.map_X, formalLogarithmOver, formal_logarithm_rational] using h

/-- The formal logarithm is the unique compositional inverse over the full
commutative Q-algebra category, not only over coefficient fields. -/
theorem formal_log_exp_over_inverse_unique (F : PowerSeries A)
    (h : formalComposeOver F (formalExponentialOver A 1-1)=X) :
    F=formalLogarithmOver A := by
  apply formal_compose_over_injective (formalExponentialOver A 1-1)
  · rw [← coeff_zero_eq_constantCoeff_apply]
    simp [formalExponentialOver, coeff_rescale, coeff_exp]
  · simp [formalExponentialOver, coeff_rescale, coeff_exp]
  · exact h.trans (formal_log_exp_over_inverse A).symm

theorem formal_logarithm_over_field {K : Type*} [Field K] [CharZero K] :
    formalLogarithmOver K=formalLogarithm K := by
  ext n
  cases n with
  | zero => simp [formalLogarithmOver, formalLogarithm, coeff_map, SigmaPresentations.formalLog]
  | succ n =>
    simp [formalLogarithmOver, formalLogarithm, coeff_map, SigmaPresentations.formalLog]

omit [Algebra ℚ A] in
theorem formal_compose_over_constant (F G : PowerSeries A) :
    constantCoeff A (formalComposeOver F G)=constantCoeff A F := by
  simp [formalComposeOver]

/-- The recovered formal logarithm has its usual convergent real expansion
on the full open unit disc. This supplies an actual germ, not just the name
of a formal series. -/
theorem formal_logarithm_real_hasSum (z : ℝ) (hz : |z| < 1) :
    HasSum (fun n => coeff ℝ n (formalLogarithm ℝ)*z^n) (Real.log (1+z)) := by
  have hs := (Real.hasSum_pow_div_log_of_abs_lt_one (by simpa using hz : |-z|<1)).neg
  have ht : HasSum (fun n => coeff ℝ (n+1) (formalLogarithm ℝ)*z^(n+1))
      (Real.log (1+z)) := by
    convert hs using 1
    · funext n
      simp only [formalLogarithm, coeff_mk]
      rw [neg_pow z (n+1), pow_succ (-1:ℝ) n]
      push_cast
      ring
    · simp
  apply (hasSum_nat_add_iff' 1).mp
  simpa only [Finset.sum_range_one, formalLogarithm, coeff_mk, zero_mul, sub_zero] using ht

/-- The formal intrinsic entropy germ reconstructed from the logarithm. -/
def formalEntropyGerm : PowerSeries ℝ := formalLogarithm ℝ-X

theorem formal_entropy_germ_hasSum (z : ℝ) (hz : |z| < 1) :
    HasSum (fun n => coeff ℝ n formalEntropyGerm*z^n) (Real.log (1+z)-z) := by
  have hX : HasSum (fun n => coeff ℝ n (X:PowerSeries ℝ)*z^n) z := by
    convert (hasSum_ite_eq (1:ℕ) z) using 1
    funext n
    by_cases hn : n=1
    · simp [hn]
    · simp [coeff_X, hn]
  simpa only [formalEntropyGerm, map_sub, sub_mul] using
    (formal_logarithm_real_hasSum z hz).sub hX

theorem formal_entropy_germ_intrinsic (z : ℝ) (hz : |z| < 1) :
    HasSum (fun n => coeff ℝ n formalEntropyGerm*z^n) (SigmaPresentations.H (1+z)) := by
  convert formal_entropy_germ_hasSum z hz using 1
  unfold SigmaPresentations.H
  ring

end
end Sigma
