import SigmaRealCharacteristic

namespace Sigma
noncomputable section
open PowerSeries

variable (K : Type*) [Field K] [CharZero K]

theorem formal_ahat_inverse_denominator : (formalAhat K)⁻¹ = ahatDenominator K := by
  apply (PowerSeries.inv_eq_iff_mul_eq_one (by simp [formal_ahat_constant])).2
  exact PowerSeries.mul_inv_cancel _ (by simp [ahat_denominator_constant])

theorem formal_ahat_b :
    X * (formalAhat K)⁻¹ =
      formalExponential K (1 / 2) - formalExponential K (-(1 / 2)) := by
  rw [formal_ahat_inverse_denominator, mul_comm, ahat_denominator_mul_X]

def formalAhatSquareRoot : PowerSeries K :=
  formalExponential K (1 / 2) + formalExponential K (-(1 / 2))

theorem formal_ahat_square_root_constant : constantCoeff K (formalAhatSquareRoot K) = 2 := by
  norm_num [formalAhatSquareRoot, formal_exponential_constant]

theorem formal_ahat_square_root_equation :
    formalAhatSquareRoot K ^ 2 = (X * (formalAhat K)⁻¹) ^ 2 + 4 := by
  rw [formal_ahat_b]
  dsimp [formalAhatSquareRoot]
  have he := formal_exponential_inverse_product K (1 / 2)
  linear_combination 4 * he

theorem normalized_formal_square_root_unique (S R B : PowerSeries K)
    (hS : constantCoeff K S = 2) (hR : constantCoeff K R = 2)
    (hsq : S ^ 2 = B) (hrq : R ^ 2 = B) : S = R := by
  have hprod : (S - R) * (S + R) = 0 := by linear_combination hsq - hrq
  have hne : S + R ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff K) h
    norm_num [hS, hR] at hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hne)

/-- The square root in the A-hat reconstruction exists and has exactly the
specified constant-two branch. It is proved from the actual A-hat quotient. -/
theorem formal_ahat_square_root_exists_unique :
    ∃! S : PowerSeries K, constantCoeff K S = 2 ∧
      S ^ 2 = (X * (formalAhat K)⁻¹) ^ 2 + 4 := by
  refine ⟨formalAhatSquareRoot K,
    ⟨formal_ahat_square_root_constant K, formal_ahat_square_root_equation K⟩, ?_⟩
  intro S hS
  exact normalized_formal_square_root_unique K S (formalAhatSquareRoot K) _
    hS.1 (formal_ahat_square_root_constant K) hS.2 (formal_ahat_square_root_equation K)

theorem formal_ahat_square_root_reconstruction :
    C K (1 / 2) * (X * (formalAhat K)⁻¹ + formalAhatSquareRoot K) =
      formalExponential K (1 / 2) := by
  rw [formal_ahat_b]
  dsimp [formalAhatSquareRoot]
  have hc : C K (1 / 2) * (2 : PowerSeries K) = 1 := by
    have h : (1 / 2 : K) * 2 = 1 := by norm_num
    simpa only [map_mul, map_ofNat, map_one] using congrArg (C K) h
  linear_combination formalExponential K (1 / 2) * hc

theorem formal_ahat_square_root_recovers_todd :
    (C K (1 / 2) * (X * (formalAhat K)⁻¹ + formalAhatSquareRoot K)) *
      formalAhat K = formalTodd K := by
  rw [formal_ahat_square_root_reconstruction, formal_ahat_to_todd]

/-- Recovery is stated for the branch specified from the supplied A-hat data,
not as an assumption that its output is already the exponential. -/
theorem formal_ahat_recovers_todd_from_any_normalized_root (S : PowerSeries K)
    (hS : constantCoeff K S = 2)
    (heq : S ^ 2 = (X * (formalAhat K)⁻¹) ^ 2 + 4) :
    (C K (1 / 2) * (X * (formalAhat K)⁻¹ + S)) * formalAhat K = formalTodd K := by
  have hs := normalized_formal_square_root_unique K S (formalAhatSquareRoot K) _
    hS (formal_ahat_square_root_constant K) heq (formal_ahat_square_root_equation K)
  rw [hs, formal_ahat_square_root_recovers_todd]

theorem formal_L_exponential_recovery_product :
    formalExponential K 2 * (formalL K - X) = formalL K + X := by
  have h := formal_L_quotient K
  linear_combination h

theorem formal_L_recovers_exponential :
    (formalL K + X) * (formalL K - X)⁻¹ = formalExponential K 2 := by
  symm
  apply (PowerSeries.eq_mul_inv_iff_mul_eq ?_).2
  · exact formal_L_exponential_recovery_product K
  · simp [formal_L_constant]

end
end Sigma
