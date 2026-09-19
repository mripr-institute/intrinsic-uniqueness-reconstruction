import SigmaArithmeticTransport
import Mathlib.Data.PNat.Factors
import Mathlib.GroupTheory.Perm.Basic

namespace Sigma
noncomputable section
open Set

section Inventory
variable {M : Type*} [CommMonoid M] (E : ℕ+ ≃* M)

/-- Factorization is recovered from the labelled monoid inverse. -/
def labelledFactors (x : M) : PrimeMultiset := (E.symm x).factorMultiset

def labelledValuation (p : Nat.Primes) (x : M) : ℕ :=
  (labelledFactors E x).count p

theorem labelled_factorization_inverse (x : M) :
    E (labelledFactors E x).prod=x := by
  simp only [labelledFactors, PNat.prod_factorMultiset, E.apply_symm_apply]

theorem labelled_factorization_unique (s : PrimeMultiset) :
    labelledFactors E (E s.prod)=s := by
  simp only [labelledFactors, E.symm_apply_apply, PrimeMultiset.factorMultiset_prod]

theorem labelled_factors_mul (x y : M) :
    labelledFactors E (x*y)=labelledFactors E x+labelledFactors E y := by
  simp only [labelledFactors, map_mul, PNat.factorMultiset_mul]

theorem labelled_dvd_iff (x y : M) : x ∣ y ↔ E.symm x ∣ E.symm y := by
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨E.symm z,map_mul E.symm _ _⟩
  · rintro ⟨z,hz⟩
    refine ⟨E z, ?_⟩
    simpa using congrArg E hz

theorem labelled_dvd_iff_factors (x y : M) :
    x ∣ y ↔ labelledFactors E x ≤ labelledFactors E y := by
  rw [labelled_dvd_iff E]
  exact PNat.factorMultiset_le_iff.symm

/-- The actual divisibility maximum, including exponent zero and the unit. -/
theorem labelled_valuation_maximum (p : Nat.Primes) (x : M) (k : ℕ) :
    E (p : ℕ+)^k ∣ x ↔ k ≤ labelledValuation E p x := by
  rw [labelled_dvd_iff E, map_pow, E.symm_apply_apply]
  exact PNat.count_factorMultiset _ _ _

theorem labelled_valuation_mul (p : Nat.Primes) (x y : M) :
    labelledValuation E p (x*y)=labelledValuation E p x+labelledValuation E p y := by
  unfold labelledValuation
  rw [labelled_factors_mul]
  exact Multiset.count_add _ _ _

def labelledGcd (x y : M) : M := E (PNat.gcd (E.symm x) (E.symm y))
def labelledLcm (x y : M) : M := E (PNat.lcm (E.symm x) (E.symm y))

theorem labelled_gcd_universal (d x y : M) :
    d ∣ labelledGcd E x y ↔ d ∣ x ∧ d ∣ y := by
  simp only [labelled_dvd_iff E, labelledGcd, E.symm_apply_apply]
  constructor
  · intro h
    exact ⟨dvd_trans h (PNat.gcd_dvd_left _ _), dvd_trans h (PNat.gcd_dvd_right _ _)⟩
  · rintro ⟨h₁,h₂⟩
    exact PNat.dvd_gcd h₁ h₂

theorem labelled_lcm_universal (d x y : M) :
    labelledLcm E x y ∣ d ↔ x ∣ d ∧ y ∣ d := by
  simp only [labelled_dvd_iff E, labelledLcm, E.symm_apply_apply]
  constructor
  · intro h
    exact ⟨dvd_trans (PNat.dvd_lcm_left _ _) h, dvd_trans (PNat.dvd_lcm_right _ _) h⟩
  · rintro ⟨h₁,h₂⟩
    exact PNat.lcm_dvd h₁ h₂

theorem labelled_valuation_gcd (p : Nat.Primes) (x y : M) :
    labelledValuation E p (labelledGcd E x y)=
      min (labelledValuation E p x) (labelledValuation E p y) := by
  simp only [labelledValuation, labelledFactors, labelledGcd,
    E.symm_apply_apply, PNat.factorMultiset_gcd]
  exact Multiset.count_inter _ _ _

theorem labelled_valuation_lcm (p : Nat.Primes) (x y : M) :
    labelledValuation E p (labelledLcm E x y)=
      max (labelledValuation E p x) (labelledValuation E p y) := by
  simp only [labelledValuation, labelledFactors, labelledLcm,
    E.symm_apply_apply, PNat.factorMultiset_lcm]
  exact Multiset.count_union _ _ _

/-- Divisors correspond bijectively to submultisets, with actual monoid
divisibility corresponding to componentwise exponent order. -/
def labelledDivisorEquiv (x : M) :
    {d : M // d ∣ x} ≃ {s : PrimeMultiset // s ≤ labelledFactors E x} where
  toFun d := ⟨labelledFactors E d.val, (labelled_dvd_iff_factors E _ _).mp d.property⟩
  invFun s := ⟨E s.val.prod, by
    rw [labelled_dvd_iff_factors E, labelled_factorization_unique]
    exact s.property⟩
  left_inv d := Subtype.ext (labelled_factorization_inverse E d.val)
  right_inv s := Subtype.ext (labelled_factorization_unique E s.val)

theorem labelled_divisor_order (x : M) (a b : {d : M // d ∣ x}) :
    a.val ∣ b.val ↔ (labelledDivisorEquiv E x a).val ≤
      (labelledDivisorEquiv E x b).val := labelled_dvd_iff_factors E _ _

end Inventory

/-- Every permutation of numerical primes extends to an actual automorphism
of the positive-integer multiplication monoid. -/
def primePermutationMonoid (σ : Equiv.Perm Nat.Primes) : ℕ+ ≃* ℕ+ where
  toFun n := PrimeMultiset.prod (n.factorMultiset.map σ)
  invFun n := PrimeMultiset.prod (n.factorMultiset.map σ.symm)
  left_inv n := by
    dsimp only
    rw [PrimeMultiset.factorMultiset_prod, Multiset.map_map]
    simpa using PNat.prod_factorMultiset n
  right_inv n := by
    dsimp only
    rw [PrimeMultiset.factorMultiset_prod, Multiset.map_map]
    simpa using PNat.prod_factorMultiset n
  map_mul' n m := by
    dsimp only
    rw [PNat.factorMultiset_mul, Multiset.map_add]
    exact PrimeMultiset.prod_add _ _

theorem prime_permutation_on_prime (σ : Equiv.Perm Nat.Primes) (p : Nat.Primes) :
    primePermutationMonoid σ (p : ℕ+)=(σ p : ℕ+) := by
  change PrimeMultiset.prod ((p : ℕ+).factorMultiset.map σ)=_
  rw [PNat.factorMultiset_ofPrime]
  change PrimeMultiset.prod (({p} : Multiset Nat.Primes).map σ)=_
  rw [Multiset.map_singleton]
  exact PrimeMultiset.prod_ofPrime _

def swapTwoThree : ℕ+ ≃* ℕ+ :=
  primePermutationMonoid (Equiv.swap (⟨2,Nat.prime_two⟩ : Nat.Primes) ⟨3,Nat.prime_three⟩)

theorem swap_two_three_two : swapTwoThree 2=3 := by
  exact prime_permutation_on_prime
    (Equiv.swap (⟨2,Nat.prime_two⟩ : Nat.Primes) ⟨3,Nat.prime_three⟩) ⟨2,Nat.prime_two⟩

theorem swap_two_three_not_additive : swapTwoThree (1+1) ≠ swapTwoThree 1+swapTwoThree 1 := by
  rw [map_one]
  change swapTwoThree 2 ≠ 2
  rw [swap_two_three_two]
  decide

end
end Sigma
