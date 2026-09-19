import SigmaArithmeticConvolution

namespace Sigma
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {M R : Type*} [CommMonoid M]

def LabelledCoprime (E : ℕ+ ≃* M) (x y : M) : Prop :=
  Nat.Coprime (E.symm x).val (E.symm y).val

def IsLabelledMultiplicative [Monoid R] (E : ℕ+ ≃* M) (f : M → R) : Prop :=
  f 1=1 ∧ ∀ x y, LabelledCoprime E x y → f (x*y)=f x*f y

theorem labelled_arithmetic_multiplicative_iff [MonoidWithZero R]
    (E : ℕ+ ≃* M) (f : M → R) :
    (labelledArithmetic E f).IsMultiplicative ↔ IsLabelledMultiplicative E f := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · rintro ⟨h1,hm⟩
    refine ⟨?_, ?_⟩
    · simpa [labelledArithmetic] using h1
    · intro x y hxy
      have h := hm (E.symm x).ne_zero (E.symm y).ne_zero hxy
      change labelledArithmetic E f ((E.symm x*E.symm y).val)=_ at h
      simpa only [labelled_arithmetic_positive, map_mul, E.apply_symm_apply] using h
  · rintro ⟨h1,hm⟩
    refine ⟨by simpa [labelledArithmetic] using h1, ?_⟩
    intro m n hm0 hn0 hmn
    let a : ℕ+ := ⟨m,Nat.pos_of_ne_zero hm0⟩
    let b : ℕ+ := ⟨n,Nat.pos_of_ne_zero hn0⟩
    have hc : LabelledCoprime E (E a) (E b) := by simpa [LabelledCoprime, a, b] using hmn
    have h := hm (E a) (E b) hc
    change labelledArithmetic E f ((a*b).val)=
      labelledArithmetic E f a.val*labelledArithmetic E f b.val
    simpa only [labelled_arithmetic_positive, map_mul] using h

/-- Each numerical prime and positive exponent receives an arbitrary value.
There is no value prescribed at exponent zero, which is the common unit. -/
def primePowerPrescription [One R] (v : Nat.Primes → ℕ+ → R) (p k : ℕ) : R :=
  if hp : Nat.Prime p then if hk : 0 < k then v ⟨p,hp⟩ ⟨k,hk⟩ else 1 else 1

def primePowerArithmetic [CommMonoidWithZero R] (v : Nat.Primes → ℕ+ → R) : ArithmeticFunction R where
  toFun n := if n=0 then 0 else n.factorization.prod (primePowerPrescription v)
  map_zero' := by simp

theorem prime_power_arithmetic_multiplicative [CommMonoidWithZero R]
    (v : Nat.Primes → ℕ+ → R) : (primePowerArithmetic v).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [primePowerArithmetic], ?_⟩
  intro m n hm hn hmn
  simp only [primePowerArithmetic, ArithmeticFunction.coe_mk, if_neg hm, if_neg hn,
    if_neg (Nat.mul_ne_zero hm hn), Nat.factorization_mul_of_coprime hmn]
  exact Finsupp.prod_add_index_of_disjoint hmn.disjoint_primeFactors _

theorem prime_power_arithmetic_prescribed [CommMonoidWithZero R]
    (v : Nat.Primes → ℕ+ → R) (p : Nat.Primes) (k : ℕ+) :
    primePowerArithmetic v (p.val^k.val)=v p k := by
  have h0 : p.val^k.val ≠ 0 := pow_ne_zero _ p.property.ne_zero
  simp only [primePowerArithmetic, ArithmeticFunction.coe_mk, if_neg h0,
    p.property.factorization_pow]
  rw [Finsupp.prod_single_index]
  · simp only [primePowerPrescription, dif_pos p.property, dif_pos k.pos]
    congr 2
  · simp [primePowerPrescription]

def labelledPrimePowerExtension [CommMonoidWithZero R] (E : ℕ+ ≃* M)
    (v : Nat.Primes → ℕ+ → R) : M → R := arithmeticLabelled E (primePowerArithmetic v)

theorem labelled_prime_power_extension_multiplicative [CommMonoidWithZero R]
    (E : ℕ+ ≃* M) (v : Nat.Primes → ℕ+ → R) :
    IsLabelledMultiplicative E (labelledPrimePowerExtension E v) := by
  rw [← labelled_arithmetic_multiplicative_iff, labelledPrimePowerExtension,
    labelled_arithmetic_inverse]
  exact prime_power_arithmetic_multiplicative v

theorem labelled_prime_power_extension_prescribed [CommMonoidWithZero R]
    (E : ℕ+ ≃* M) (v : Nat.Primes → ℕ+ → R) (p : Nat.Primes) (k : ℕ+) :
    labelledPrimePowerExtension E v (E (p : ℕ+)^k.val)=v p k := by
  simp only [labelledPrimePowerExtension, arithmeticLabelled, map_pow,
    E.symm_apply_apply, PNat.pow_coe]
  exact prime_power_arithmetic_prescribed v p k

theorem labelled_multiplicative_unique [CommMonoidWithZero R]
    (E : ℕ+ ≃* M) (f g : M → R) (hf : IsLabelledMultiplicative E f)
    (hg : IsLabelledMultiplicative E g)
    (h : ∀ p : Nat.Primes, ∀ k : ℕ+, f (E (p : ℕ+)^k.val)=g (E (p : ℕ+)^k.val)) : f=g := by
  apply (labelledArithmeticEquiv E).injective
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((labelled_arithmetic_multiplicative_iff E f).mpr hf) _
    ((labelled_arithmetic_multiplicative_iff E g).mpr hg)).mpr
  intro p k hp
  by_cases hk : k=0
  · subst k
    simpa [labelledArithmetic] using hf.1.trans hg.1.symm
  · let P : Nat.Primes := ⟨p,hp⟩
    let a : ℕ+ := ⟨k,Nat.pos_of_ne_zero hk⟩
    have he := h P a
    change labelledArithmetic E f (((P:ℕ+)^k).val)=labelledArithmetic E g (((P:ℕ+)^k).val)
    simpa only [labelled_arithmetic_positive, map_pow] using he

theorem labelled_prime_power_values_exists_unique [CommMonoidWithZero R]
    (E : ℕ+ ≃* M) (v : Nat.Primes → ℕ+ → R) :
    ∃! f : M → R, IsLabelledMultiplicative E f ∧
      ∀ p : Nat.Primes, ∀ k : ℕ+, f (E (p : ℕ+)^k.val)=v p k := by
  refine ⟨labelledPrimePowerExtension E v,
    ⟨labelled_prime_power_extension_multiplicative E v,
      labelled_prime_power_extension_prescribed E v⟩, ?_⟩
  intro f hf
  apply labelled_multiplicative_unique E f _ hf.1 (labelled_prime_power_extension_multiplicative E v)
  intro p k
  rw [hf.2, labelled_prime_power_extension_prescribed]

theorem labelled_coprime_iff_gcd_one (E : ℕ+ ≃* M) (x y : M) :
    LabelledCoprime E x y ↔ labelledGcd E x y=1 := by
  rw [← labelled_index_one_iff E]
  simp only [labelledGcd, E.symm_apply_apply, PNat.gcd_coe]
  rfl

theorem labelled_valuation_native_factorization (E : ℕ+ ≃* M)
    (p : Nat.Primes) (x : M) :
    labelledValuation E p x=(E.symm x).val.factorization p.val := by
  have h (k : ℕ) : k ≤ labelledValuation E p x ↔
      k ≤ (E.symm x).val.factorization p.val := by
    rw [← labelled_valuation_maximum E p x k, labelled_dvd_iff, map_pow,
      E.symm_apply_apply, PNat.dvd_iff, PNat.pow_coe]
    exact p.property.pow_dvd_iff_le_factorization (E.symm x).ne_zero
  exact Nat.le_antisymm ((h _).mp le_rfl) ((h _).mpr le_rfl)

theorem labelled_multiplicative_product [CommMonoidWithZero R]
    (E : ℕ+ ≃* M) (f : M → R) (hf : IsLabelledMultiplicative E f) (x : M) :
    f x=∏ p ∈ (labelledFactors E x).toFinset,
      f (E (p : ℕ+)^labelledValuation E p x) := by
  have h := ArithmeticFunction.IsMultiplicative.multiplicative_factorization
    (labelledArithmetic E f) ((labelled_arithmetic_multiplicative_iff E f).mpr hf)
    (E.symm x).ne_zero
  rw [labelled_arithmetic_positive, E.apply_symm_apply] at h
  rw [h]
  symm
  refine Finset.prod_bij (fun p _ => p.val) ?_ ?_ ?_ ?_
  · intro p hp
    change p.val ∈ (E.symm x).val.factorization.support
    rw [Finsupp.mem_support_iff, ← labelled_valuation_native_factorization]
    exact Nat.ne_of_gt ((labelled_valuation_support E x p).mp hp)
  · intro p hp q hq hpq
    exact Subtype.ext hpq
  · intro p hp
    let P : Nat.Primes := ⟨p,Nat.prime_of_mem_primeFactors hp⟩
    refine ⟨P, ?_, rfl⟩
    rw [labelled_valuation_support, labelled_valuation_native_factorization]
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  · intro p hp
    rw [← labelled_valuation_native_factorization E p x]
    have he := labelled_arithmetic_positive E f ((p : ℕ+)^labelledValuation E p x)
    simpa only [PNat.pow_coe, map_pow] using he.symm

theorem labelled_prime_power_extension_injective [CommMonoidWithZero R]
    (E : ℕ+ ≃* M) : Function.Injective (labelledPrimePowerExtension (R:=R) E) := by
  intro v w h
  funext p k
  have he := congrFun h (E (p : ℕ+)^k.val)
  simpa only [labelled_prime_power_extension_prescribed] using he

theorem labelled_nonzero_multiplicative_normalized [Field R]
    (E : ℕ+ ≃* M) (f : M → R) (hf : f ≠ 0)
    (hm : ∀ x y, LabelledCoprime E x y → f (x*y)=f x*f y) :
    IsLabelledMultiplicative E f := by
  have hex : ∃ x, f x ≠ 0 := by
    by_contra h
    apply hf
    funext x
    simpa using not_exists.mp h x
  obtain ⟨x,hx⟩ := hex
  refine ⟨?_,hm⟩
  have h := hm x 1 (by simp [LabelledCoprime])
  simp only [mul_one] at h
  exact mul_left_cancel₀ hx (h.symm.trans (mul_one (f x)).symm)

theorem labelled_unnormalized_multiplicative_dichotomy [Field R]
    (E : ℕ+ ≃* M) (f : M → R)
    (hm : ∀ x y, LabelledCoprime E x y → f (x*y)=f x*f y) :
    f=0 ∨ IsLabelledMultiplicative E f := by
  by_cases hf : f=0
  · exact Or.inl hf
  · exact Or.inr (labelled_nonzero_multiplicative_normalized E f hf hm)

theorem labelled_unnormalized_multiplicative_iff [Field R]
    (E : ℕ+ ≃* M) (f : M → R) :
    (∀ x y, LabelledCoprime E x y → f (x*y)=f x*f y) ↔
      f=0 ∨ IsLabelledMultiplicative E f := by
  constructor
  · exact labelled_unnormalized_multiplicative_dichotomy E f
  · rintro (rfl | hf)
    · simp
    · exact hf.2

theorem labelled_zero_not_normalized [MonoidWithZero R] [Nontrivial R]
    (E : ℕ+ ≃* M) : ¬ IsLabelledMultiplicative E (0 : M → R) := by
  intro h
  exact zero_ne_one h.1

end
end Sigma
