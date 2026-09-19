import SigmaRealToddTower
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Data.Nat.Choose.Multinomial

namespace Sigma
noncomputable section
open PowerSeries
open scoped BigOperators

variable {K : Type*}
section RingCoefficients
variable [CommRing K]

theorem coefficient_power_depends_on_truncation (F : PowerSeries K) (n k : ℕ) :
    coeff K n (F^k) = coeff K n ((trunc (n+1) F : PowerSeries K)^k) := by
  have h := congrArg (fun P : Polynomial K => P.coeff n)
    (trunc_trunc_pow F (n+1) k)
  simpa only [coeff_trunc, Nat.lt_succ_self, if_true] using h.symm

theorem power_series_truncation_sum (F : PowerSeries K) (n : ℕ) :
    (trunc (n+1) F : PowerSeries K) =
      ∑ j ∈ Finset.range (n+1), C K (coeff K j F) * X^j := by
  ext i
  simp [Polynomial.coeff_coe, coeff_trunc, coeff_C_mul, coeff_X_pow,
    mul_ite]

theorem monomial_product_power_series {ι : Type*} (s : Finset ι)
    (q : ι → K) (w m : ι → ℕ) :
    (∏ j ∈ s, (C K (q j)*X^(w j))^(m j)) =
      C K (∏ j ∈ s, q j^(m j)) * X^(∑ j ∈ s, w j*m j) := by
  simp only [mul_pow, ← map_pow, ← pow_mul, Finset.prod_mul_distrib,
    ← map_prod, Finset.prod_pow_eq_pow_sum]

theorem power_series_multinomial_coefficient (F : PowerSeries K) (n k : ℕ) :
    coeff K n (F^k) =
      ∑ m ∈ Finset.piAntidiag (Finset.range (n+1)) k,
        if (∑ j ∈ Finset.range (n+1), j*m j)=n then
          (Nat.multinomial (Finset.range (n+1)) m : K) *
            ∏ j ∈ Finset.range (n+1), (coeff K j F)^(m j)
        else 0 := by
  rw [coefficient_power_depends_on_truncation, power_series_truncation_sum,
    Finset.sum_pow_eq_sum_piAntidiag]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [monomial_product_power_series]
  rw [show (Nat.multinomial (Finset.range (n+1)) m : PowerSeries K) =
    C K (Nat.multinomial (Finset.range (n+1)) m : K) by simp]
  rw [← mul_assoc, ← map_mul, coeff_C_mul, coeff_X_pow]
  by_cases hm : (∑ j ∈ Finset.range (n+1), j*m j)=n
  · simp [hm]
  · simp [hm, Ne.symm hm]

end RingCoefficients
section FieldCoefficients
variable [Field K]

theorem multinomial_zero_slot [CharZero K] (m : ℕ → ℕ) (n k : ℕ)
    (hm : m ∈ Finset.piAntidiag (Finset.range (n+1)) k) :
    (Nat.multinomial (Finset.range (n+1)) m : K) =
      (k.descFactorial (∑ j ∈ Finset.range n, m (j+1)) : K) /
        ∏ j ∈ Finset.range n, ((m (j+1)).factorial : K) := by
  have hsum := (Finset.mem_piAntidiag.mp hm).1
  rw [Finset.sum_range_succ'] at hsum
  have hle : (∑ j ∈ Finset.range n, m (j+1)) ≤ k := by omega
  have hzero : m 0=k-(∑ j ∈ Finset.range n, m (j+1)) := by omega
  have ha := Nat.multinomial_spec (Finset.range (n+1)) m
  rw [(Finset.mem_piAntidiag.mp hm).1, Finset.prod_range_succ'] at ha
  have hb := Nat.factorial_mul_descFactorial hle
  rw [← hzero] at hb
  have haK := congrArg (fun a : ℕ => (a : K)) ha
  have hbK := congrArg (fun a : ℕ => (a : K)) hb
  push_cast at haK hbK
  have hz : ((m 0).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m 0)
  have hp : (∏ j ∈ Finset.range n, ((m (j+1)).factorial : K)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact_mod_cast Nat.factorial_ne_zero (m (j+1))
  apply (eq_div_iff hp).mpr
  apply mul_left_cancel₀ hz
  calc
    _ = ((∏ j ∈ Finset.range n, ((m (j+1)).factorial : K)) *
      ((m 0).factorial : K)) * (Nat.multinomial (Finset.range (n+1)) m : K) := by ring
    _ = (k.factorial : K) := haK
    _ = _ := hbK.symm

/-- Natural powers in multiplicity coordinates, with the zero-degree slot
recording the unused factors. This is not yet the arbitrary-field-exponent
formula: its finite index set still retains that zero-degree slot. -/
theorem normalized_power_multiplicity_coefficient [CharZero K]
    (F : PowerSeries K) (hF : constantCoeff K F=1) (n k : ℕ) :
    coeff K n (F^k) =
      ∑ m ∈ Finset.piAntidiag (Finset.range (n+1)) k,
        if (∑ j ∈ Finset.range n, (j+1)*m (j+1))=n then
          (k.descFactorial (∑ j ∈ Finset.range n, m (j+1)) : K) *
            ∏ j ∈ Finset.range n,
              (coeff K (j+1) F)^(m (j+1)) / ((m (j+1)).factorial : K)
        else 0 := by
  rw [power_series_multinomial_coefficient]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_range_succ']
  simp only [zero_mul, add_zero]
  split_ifs
  · rw [multinomial_zero_slot m n k hm, Finset.prod_range_succ']
    simp only [coeff_zero_eq_constantCoeff_apply, hF, one_pow, mul_one]
    rw [Finset.prod_div_distrib]
    ring
  · rfl

theorem todd_nat_power_multiplicity_coefficient [CharZero K] (n k : ℕ) :
    coeff K n ((formalTodd K)^k) =
      ∑ m ∈ Finset.piAntidiag (Finset.range (n+1)) k,
        if (∑ j ∈ Finset.range n, (j+1)*m (j+1))=n then
          (k.descFactorial (∑ j ∈ Finset.range n, m (j+1)) : K) *
            ∏ j ∈ Finset.range n,
              (coeff K (j+1) (formalTodd K))^(m (j+1)) /
                ((m (j+1)).factorial : K)
        else 0 :=
  normalized_power_multiplicity_coefficient _ (formal_todd_constant K) n k

end FieldCoefficients
section RingBinomialCoefficients
variable [CommRing K]

theorem normalized_sub_one_truncation (F : PowerSeries K)
    (hF : constantCoeff K F=1) (n : ℕ) :
    (trunc (n+1) (F-1) : PowerSeries K) =
      ∑ j ∈ Finset.range n, C K (coeff K (j+1) F)*X^(j+1) := by
  rw [power_series_truncation_sum, Finset.sum_range_succ']
  simp only [map_sub, coeff_zero_eq_constantCoeff_apply, hF, map_one, sub_self,
    map_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  simp [coeff_one]

theorem normalized_sub_one_power_coefficient (F : PowerSeries K)
    (hF : constantCoeff K F=1) (n M : ℕ) :
    coeff K n ((F-1)^M) =
      ∑ m ∈ Finset.piAntidiag (Finset.range n) M,
        if (∑ j ∈ Finset.range n, (j+1)*m j)=n then
          (Nat.multinomial (Finset.range n) m : K) *
            ∏ j ∈ Finset.range n, (coeff K (j+1) F)^(m j)
        else 0 := by
  rw [coefficient_power_depends_on_truncation, normalized_sub_one_truncation F hF,
    Finset.sum_pow_eq_sum_piAntidiag]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [monomial_product_power_series]
  rw [show (Nat.multinomial (Finset.range n) m : PowerSeries K) =
    C K (Nat.multinomial (Finset.range n) m : K) by simp]
  rw [← mul_assoc, ← map_mul, coeff_C_mul, coeff_X_pow]
  by_cases hm : (∑ j ∈ Finset.range n, (j+1)*m j)=n
  · simp [hm]
  · simp [hm, Ne.symm hm]

/-- The usual scalar falling factorial, with the empty product convention. -/
def scalarFallingFactorial (k : K) (M : ℕ) : K :=
  ∏ j ∈ Finset.range M, (k-(j:K))

theorem normalized_sub_one_power_coefficient_zero (F : PowerSeries K)
    (hF : constantCoeff K F=1) (n M : ℕ) (hn : n < M) :
    coeff K n ((F-1)^M)=0 := by
  have hd : (X : PowerSeries K) ∣ F-1 := X_dvd_iff.mpr (by simp [hF])
  exact X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hd M) n hn

end RingBinomialCoefficients
section FieldBinomialCoefficients
variable [Field K]

/-- Formal scalar powers of a normalized series, by the standard formal
binomial expansion. Local finiteness follows from the vanishing constant
coefficient of F-1; the definition uses native powers, not multiplicities. -/
def formalBinomialPower [CharZero K] (F : PowerSeries K) (k : K) : PowerSeries K :=
  PowerSeries.mk fun n => ∑ M ∈ Finset.range (n+1),
    scalarFallingFactorial k M / (M.factorial : K) * coeff K n ((F-1)^M)

theorem multinomial_div_factorial [CharZero K] (n M : ℕ) (m : ℕ → ℕ)
    (hm : m ∈ Finset.piAntidiag (Finset.range n) M) :
    (Nat.multinomial (Finset.range n) m : K) / (M.factorial : K) =
      (∏ j ∈ Finset.range n, ((m j).factorial : K))⁻¹ := by
  have h := Nat.multinomial_spec (Finset.range n) m
  rw [(Finset.mem_piAntidiag.mp hm).1] at h
  have hc := congrArg (fun a : ℕ => (a:K)) h
  push_cast at hc
  have hM : (M.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero M
  have hp : (∏ j ∈ Finset.range n, ((m j).factorial : K)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact_mod_cast Nat.factorial_ne_zero (m j)
  field_simp
  linear_combination hc

theorem formal_binomial_power_multiplicity [CharZero K] (F : PowerSeries K)
    (hF : constantCoeff K F=1) (k : K) (n : ℕ) :
    coeff K n (formalBinomialPower F k) =
      ∑ M ∈ Finset.range (n+1), ∑ m ∈ Finset.piAntidiag (Finset.range n) M,
        if (∑ j ∈ Finset.range n, (j+1)*m j)=n then
          scalarFallingFactorial k M *
            ∏ j ∈ Finset.range n,
              (coeff K (j+1) F)^(m j) / ((m j).factorial : K)
        else 0 := by
  rw [formalBinomialPower, coeff_mk]
  apply Finset.sum_congr rfl
  intro M _
  rw [normalized_sub_one_power_coefficient F hF, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  split_ifs
  · rw [Finset.prod_div_distrib]
    have he := multinomial_div_factorial (K := K) n M m hm
    calc
      _ = scalarFallingFactorial k M *
          ((Nat.multinomial (Finset.range n) m : K)/(M.factorial : K)) *
          (∏ j ∈ Finset.range n, (coeff K (j+1) F)^(m j)) := by ring
      _ = _ := by rw [he]; ring
  · simp

theorem scalar_falling_factorial_nat (k M : ℕ) :
    scalarFallingFactorial (k:K) M = (k.descFactorial M : K) := by
  by_cases h : k < M
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h, Nat.cast_zero]
    apply Finset.prod_eq_zero (Finset.mem_range.mpr h)
    simp
  · rw [scalarFallingFactorial, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Nat.cast_sub (by have := Finset.mem_range.mp hj; omega)]

theorem formal_binomial_power_nat [CharZero K] (F : PowerSeries K)
    (hF : constantCoeff K F=1) (k : ℕ) :
    formalBinomialPower F (k:K) = F^k := by
  ext n
  rw [formalBinomialPower, coeff_mk]
  have hc (M : ℕ) : scalarFallingFactorial (k:K) M/(M.factorial : K) =
      (k.choose M : K) := by
    rw [scalar_falling_factorial_nat, Nat.descFactorial_eq_factorial_mul_choose,
      Nat.cast_mul, mul_div_cancel_left₀]
    exact_mod_cast Nat.factorial_ne_zero M
  simp_rw [hc]
  let f := fun M => (k.choose M : K)*coeff K n ((F-1)^M)
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
  rw [show (k.choose M : PowerSeries K)=C K (k.choose M : K) by simp,
    mul_comm, coeff_C_mul]

/-- The finite set of all positive-degree multiplicity vectors of weight n.
Index j represents the paper's degree j+1; values outside that range vanish. -/
def positiveDegreeMultiplicities (n : ℕ) : Finset (ℕ → ℕ) := by
  classical
  exact ((Finset.range (n+1)).biUnion (Finset.piAntidiag (Finset.range n))).filter
    (fun m => (∑ j ∈ Finset.range n, (j+1)*m j)=n)

theorem mem_positiveDegreeMultiplicities (n : ℕ) (m : ℕ → ℕ) :
    m ∈ positiveDegreeMultiplicities n ↔
      (∀ j, m j ≠ 0 → j < n) ∧ (∑ j ∈ Finset.range n, (j+1)*m j)=n := by
  classical
  simp only [positiveDegreeMultiplicities, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_range, Finset.mem_piAntidiag]
  constructor
  · rintro ⟨⟨M, _, hM, hs⟩, hw⟩
    exact ⟨hs, hw⟩
  · rintro ⟨hs, hw⟩
    refine ⟨⟨∑ j ∈ Finset.range n, m j, ?_, rfl, hs⟩, hw⟩
    have hle : (∑ j ∈ Finset.range n, m j) ≤ n := by
      calc
        _ ≤ ∑ j ∈ Finset.range n, (j+1)*m j := by
          apply Finset.sum_le_sum
          intro j _
          nlinarith
        _ = n := hw
    omega

theorem formal_binomial_power_exact_multiplicities [CharZero K] (F : PowerSeries K)
    (hF : constantCoeff K F=1) (k : K) (n : ℕ) :
    coeff K n (formalBinomialPower F k) =
      ∑ m ∈ positiveDegreeMultiplicities n,
        scalarFallingFactorial k (∑ j ∈ Finset.range n, m j) *
          ∏ j ∈ Finset.range n,
            (coeff K (j+1) F)^(m j) / ((m j).factorial : K) := by
  classical
  rw [formal_binomial_power_multiplicity F hF,
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

/-- The paper's arbitrary-power Todd coefficient formula, for every scalar
exponent in every characteristic-zero field. The formal scalar power uses the
standard binomial expansion and agrees with native powers at natural exponents. -/
theorem todd_arbitrary_power_coefficient [CharZero K] (k : K) (n : ℕ) :
    coeff K n (formalBinomialPower (formalTodd K) k) =
      ∑ m ∈ positiveDegreeMultiplicities n,
        scalarFallingFactorial k (∑ j ∈ Finset.range n, m j) *
          ∏ j ∈ Finset.range n,
            (coeff K (j+1) (formalTodd K))^(m j) / ((m j).factorial : K) :=
  formal_binomial_power_exact_multiplicities _ (formal_todd_constant K) k n


end FieldBinomialCoefficients
end
end Sigma
