import SigmaToddArbitraryPower
import SigmaRealToddAlgebra

namespace Sigma
noncomputable section
open PowerSeries
open scoped BigOperators
variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- Formal binomial powers over any rational algebra, using the canonical
rational inverses of the factorials. No field or no-zero-divisors assumption. -/
def formalBinomialPowerOver (F : PowerSeries A) (k : A) : PowerSeries A :=
  PowerSeries.mk fun n => ∑ M ∈ Finset.range (n+1),
    scalarFallingFactorial k M * algebraMap ℚ A ((M.factorial : ℚ)⁻¹) *
      coeff A n ((F-1)^M)

theorem scalar_falling_factorial_nat_inverse_over (k M : ℕ) :
    scalarFallingFactorial (k:A) M * algebraMap ℚ A ((M.factorial : ℚ)⁻¹) =
      (k.choose M : A) := by
  have h : scalarFallingFactorial (k:ℚ) M * (M.factorial : ℚ)⁻¹ =
      (k.choose M : ℚ) := by
    rw [scalar_falling_factorial_nat, Nat.descFactorial_eq_factorial_mul_choose,
      Nat.cast_mul]
    have hM : (M.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero M
    field_simp
  have ha := congrArg (algebraMap ℚ A) h
  simpa only [scalarFallingFactorial, map_mul, map_prod, map_sub, map_natCast] using ha

theorem formal_binomial_power_over_nat (F : PowerSeries A)
    (hF : constantCoeff A F=1) (k : ℕ) :
    formalBinomialPowerOver F (k:A) = F^k := by
  ext n
  rw [formalBinomialPowerOver, coeff_mk]
  simp_rw [scalar_falling_factorial_nat_inverse_over]
  let f := fun M => (k.choose M : A)*coeff A n ((F-1)^M)
  have hleft : (∑ M ∈ Finset.range (n+1), f M) =
      ∑ M ∈ Finset.range (max n k+1), f M := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro M _ hM
    have hnM : n < M := by simp only [Finset.mem_range] at hM; omega
    simp [f, normalized_sub_one_power_coefficient_zero F hF n M hnM]
  have hright : (∑ M ∈ Finset.range (k+1), f M) =
      ∑ M ∈ Finset.range (max n k+1), f M := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro M _ hM
    have hkM : k < M := by simp only [Finset.mem_range] at hM; omega
    simp [f, Nat.choose_eq_zero_of_lt hkM]
  change (∑ M ∈ Finset.range (n+1), f M) = _
  rw [hleft, ← hright]
  conv_rhs => rw [show F=(F-1)+1 by ring, add_pow]
  simp only [map_sum, one_pow, mul_one, map_natCast]
  apply Finset.sum_congr rfl
  intro M _
  rw [show (k.choose M : PowerSeries A)=C A (k.choose M : A) by simp,
    mul_comm, coeff_C_mul]

theorem multinomial_factorial_inverse_over (n M : ℕ) (m : ℕ → ℕ)
    (hm : m ∈ Finset.piAntidiag (Finset.range n) M) :
    (Nat.multinomial (Finset.range n) m : A) *
      algebraMap ℚ A ((M.factorial : ℚ)⁻¹) =
        ∏ j ∈ Finset.range n, algebraMap ℚ A (((m j).factorial : ℚ)⁻¹) := by
  have h := multinomial_div_factorial (K := ℚ) n M m hm
  rw [div_eq_mul_inv, ← Finset.prod_inv_distrib] at h
  have ha := congrArg (algebraMap ℚ A) h
  simpa only [map_mul, map_natCast, map_prod] using ha

theorem formal_binomial_power_over_multiplicity (F : PowerSeries A)
    (hF : constantCoeff A F=1) (k : A) (n : ℕ) :
    coeff A n (formalBinomialPowerOver F k) =
      ∑ M ∈ Finset.range (n+1), ∑ m ∈ Finset.piAntidiag (Finset.range n) M,
        if (∑ j ∈ Finset.range n, (j+1)*m j)=n then
          scalarFallingFactorial k M *
            ∏ j ∈ Finset.range n,
              (coeff A (j+1) F)^(m j) * algebraMap ℚ A (((m j).factorial : ℚ)⁻¹)
        else 0 := by
  rw [formalBinomialPowerOver, coeff_mk]
  apply Finset.sum_congr rfl
  intro M _
  rw [normalized_sub_one_power_coefficient F hF, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  split_ifs
  · rw [Finset.prod_mul_distrib]
    have he := multinomial_factorial_inverse_over (A := A) n M m hm
    calc
      _ = scalarFallingFactorial k M *
          ((Nat.multinomial (Finset.range n) m : A) *
            algebraMap ℚ A ((M.factorial : ℚ)⁻¹)) *
          (∏ j ∈ Finset.range n, (coeff A (j+1) F)^(m j)) := by ring
      _ = _ := by rw [he]; ring
  · simp

theorem formal_binomial_power_over_exact_multiplicities (F : PowerSeries A)
    (hF : constantCoeff A F=1) (k : A) (n : ℕ) :
    coeff A n (formalBinomialPowerOver F k) =
      ∑ m ∈ positiveDegreeMultiplicities n,
        scalarFallingFactorial k (∑ j ∈ Finset.range n, m j) *
          ∏ j ∈ Finset.range n,
            (coeff A (j+1) F)^(m j) * algebraMap ℚ A (((m j).factorial : ℚ)⁻¹) := by
  classical
  rw [formal_binomial_power_over_multiplicity F hF,
    positiveDegreeMultiplicities, Finset.sum_filter, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro M _
    apply Finset.sum_congr rfl
    intro m hm
    rw [(Finset.mem_piAntidiag.mp hm).1]
  · intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro m ha hb
    exact hab ((Finset.mem_piAntidiag.mp ha).1.symm.trans (Finset.mem_piAntidiag.mp hb).1)

theorem todd_arbitrary_power_coefficient_over_Q_algebra (k : A) (n : ℕ) :
    coeff A n (formalBinomialPowerOver (formalToddUnitOver A : PowerSeries A) k) =
      ∑ m ∈ positiveDegreeMultiplicities n,
        scalarFallingFactorial k (∑ j ∈ Finset.range n, m j) *
          ∏ j ∈ Finset.range n,
            (coeff A (j+1) (formalToddUnitOver A : PowerSeries A))^(m j) *
              algebraMap ℚ A (((m j).factorial : ℚ)⁻¹) :=
  formal_binomial_power_over_exact_multiplicities _ (formal_todd_over_constant A) k n

theorem formal_binomial_power_over_field {K : Type*} [Field K] [CharZero K]
    (F : PowerSeries K) (k : K) :
    formalBinomialPowerOver F k = formalBinomialPower F k := by
  ext n
  simp only [formalBinomialPowerOver, formalBinomialPower, coeff_mk,
    map_inv₀, map_natCast, div_eq_mul_inv]

end
end Sigma
