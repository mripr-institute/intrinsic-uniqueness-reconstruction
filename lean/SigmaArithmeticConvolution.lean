import SigmaArithmeticDivisors
import Mathlib.NumberTheory.ArithmeticFunction

namespace Sigma
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {M R : Type*} [CommMonoid M]

/-- The actual positive-integer labelled functions, with the auxiliary zero
value required by Mathlib's arithmetic-function type. -/
def labelledArithmetic [Zero R] (E : ℕ+ ≃* M) (f : M → R) : ArithmeticFunction R where
  toFun n := if h : n=0 then 0 else f (E ⟨n,Nat.pos_of_ne_zero h⟩)
  map_zero' := by simp

def arithmeticLabelled [Zero R] (E : ℕ+ ≃* M) (f : ArithmeticFunction R) (x : M) : R :=
  f (E.symm x).val

@[simp] theorem labelled_arithmetic_positive [Zero R] (E : ℕ+ ≃* M) (f : M → R) (n : ℕ+) :
    labelledArithmetic E f n.val=f (E n) := by
  simp only [labelledArithmetic, ArithmeticFunction.coe_mk, dif_neg n.ne_zero]
  congr 2

@[simp] theorem arithmetic_labelled_inverse [Zero R] (E : ℕ+ ≃* M) (f : M → R) :
    arithmeticLabelled E (labelledArithmetic E f)=f := by
  funext x
  simp [arithmeticLabelled]

@[simp] theorem labelled_arithmetic_inverse [Zero R] (E : ℕ+ ≃* M) (f : ArithmeticFunction R) :
    labelledArithmetic E (arithmeticLabelled E f)=f := by
  ext n
  by_cases hn : n=0
  · subst n
    simp
  · simpa [arithmeticLabelled] using
      labelled_arithmetic_positive E (arithmeticLabelled E f) (⟨n,Nat.pos_of_ne_zero hn⟩ : ℕ+)

def labelledArithmeticEquiv [Zero R] (E : ℕ+ ≃* M) : (M → R) ≃ ArithmeticFunction R where
  toFun := labelledArithmetic E
  invFun := arithmeticLabelled E
  left_inv := arithmetic_labelled_inverse E
  right_inv := labelled_arithmetic_inverse E

def labelledQuotient (E : ℕ+ ≃* M) (x d : M) : M :=
  E (PNat.divExact (E.symm x) (E.symm d))

theorem labelled_quotient_mul (E : ℕ+ ≃* M) {x d : M} (hd : d ∣ x) :
    d*labelledQuotient E x d=x := by
  have h := congrArg E (PNat.mul_div_exact ((labelled_dvd_iff E d x).mp hd))
  simpa only [map_mul, E.apply_symm_apply, labelledQuotient] using h

theorem labelled_quotient_index (E : ℕ+ ≃* M) {x d : M} (hd : d ∣ x) :
    (E.symm (labelledQuotient E x d)).val=(E.symm x).val/(E.symm d).val := by
  have h := congrArg (fun x => (E.symm x).val) (labelled_quotient_mul E hd)
  simp only [map_mul, PNat.mul_coe] at h
  rw [← h, Nat.mul_div_cancel_left _ (E.symm d).pos]

theorem labelled_divisor_sum [AddCommMonoid R] (E : ℕ+ ≃* M) (f : M → R) (x : M) :
    ∑ d ∈ labelledDivisors E x, f d =
      ∑ n ∈ (E.symm x).val.divisors, labelledArithmetic E f n := by
  classical
  apply Finset.sum_bij (fun d _ => (E.symm d).val)
  · intro d hd
    exact Nat.mem_divisors.mpr ⟨PNat.dvd_iff.mp ((labelled_dvd_iff E d x).mp
      ((mem_labelled_divisors E x d).mp hd)), (E.symm x).ne_zero⟩
  · intro d hd e he hde
    exact E.symm.injective (Subtype.ext hde)
  · intro n hn
    let d : M := E ⟨n,Nat.pos_of_mem_divisors hn⟩
    refine ⟨d, (mem_labelled_divisors E x d).mpr ?_, ?_⟩
    · rw [labelled_dvd_iff, show E.symm d=⟨n,Nat.pos_of_mem_divisors hn⟩ by simp [d]]
      exact PNat.dvd_iff.mpr (Nat.mem_divisors.mp hn).1
    · simp [d]
  · intro d _
    simp

def labelledConvolution [Semiring R] (E : ℕ+ ≃* M) (f g : M → R) : M → R :=
  arithmeticLabelled E (labelledArithmetic E f*labelledArithmetic E g)

def labelledDelta [Zero R] [One R] (x : M) : R := by
  classical
  exact if x=1 then 1 else 0

theorem labelled_convolution_sum [Semiring R] (E : ℕ+ ≃* M) (f g : M → R) (x : M) :
    labelledConvolution E f g x =
      ∑ d ∈ labelledDivisors E x, f d*g (labelledQuotient E x d) := by
  rw [labelled_divisor_sum]
  unfold labelledConvolution arithmeticLabelled
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => labelledArithmetic E f a*labelledArithmetic E g b)]
  apply Finset.sum_congr rfl
  intro n hn
  let d : M := E ⟨n,Nat.pos_of_mem_divisors hn⟩
  have hd : d ∣ x := by
    rw [labelled_dvd_iff, show E.symm d=⟨n,Nat.pos_of_mem_divisors hn⟩ by simp [d]]
    exact PNat.dvd_iff.mpr (Nat.mem_divisors.mp hn).1
  have hdi : (E.symm d).val=n := by simp [d]
  have hq := labelled_quotient_index E hd
  rw [hdi] at hq
  rw [← hq, labelled_arithmetic_positive]
  simp only [E.apply_symm_apply]
  rw [← hdi, labelled_arithmetic_positive, labelled_arithmetic_positive]
  simp [d]

theorem labelled_convolution_assoc [Semiring R] (E : ℕ+ ≃* M) (f g h : M → R) :
    labelledConvolution E (labelledConvolution E f g) h =
      labelledConvolution E f (labelledConvolution E g h) := by
  simp only [labelledConvolution, labelled_arithmetic_inverse, mul_assoc]

theorem labelled_convolution_comm [CommSemiring R] (E : ℕ+ ≃* M) (f g : M → R) :
    labelledConvolution E f g=labelledConvolution E g f := by
  simp only [labelledConvolution, mul_comm]

theorem labelled_index_one_iff (E : ℕ+ ≃* M) (x : M) : (E.symm x).val=1 ↔ x=1 := by
  constructor
  · intro h
    have hp : E.symm x=1 := Subtype.ext h
    simpa using congrArg E hp
  · rintro rfl
    simp

theorem arithmetic_labelled_one [Semiring R] (E : ℕ+ ≃* M) :
    arithmeticLabelled E (1 : ArithmeticFunction R)=labelledDelta := by
  classical
  funext x
  simp only [arithmeticLabelled, ArithmeticFunction.one_apply, labelledDelta,
    labelled_index_one_iff]

theorem arithmetic_labelled_zeta [Semiring R] (E : ℕ+ ≃* M) :
    arithmeticLabelled E (ArithmeticFunction.zeta : ArithmeticFunction R)=fun _ => 1 := by
  funext x
  simp [arithmeticLabelled, ArithmeticFunction.zeta_apply_ne (E.symm x).ne_zero]

theorem labelled_convolution_one_left [Semiring R] (E : ℕ+ ≃* M) (f : M → R) :
    labelledConvolution E labelledDelta f=f := by
  rw [← arithmetic_labelled_one E]
  simp [labelledConvolution]

theorem labelled_convolution_one_right [Semiring R] (E : ℕ+ ≃* M) (f : M → R) :
    labelledConvolution E f labelledDelta=f := by
  rw [← arithmetic_labelled_one E]
  simp [labelledConvolution]

def labelledMoebius (E : ℕ+ ≃* M) (x : M) : ℤ :=
  ArithmeticFunction.moebius (E.symm x).val

theorem labelled_moebius_one (E : ℕ+ ≃* M) : labelledMoebius E 1=1 := by
  simp [labelledMoebius]

theorem arithmetic_labelled_moebius [Ring R] (E : ℕ+ ≃* M) :
    arithmeticLabelled E (ArithmeticFunction.moebius : ArithmeticFunction R)=
      fun x => (labelledMoebius E x : R) := by
  funext x
  simp [arithmeticLabelled, labelledMoebius]

theorem labelled_moebius_convolution [Ring R] (E : ℕ+ ≃* M) :
    labelledConvolution E (fun x => (labelledMoebius E x : R)) (fun _ => 1)=labelledDelta := by
  rw [← arithmetic_labelled_moebius, ← arithmetic_labelled_zeta E]
  simp only [labelledConvolution, labelled_arithmetic_inverse,
    ArithmeticFunction.coe_moebius_mul_coe_zeta, arithmetic_labelled_one]

theorem labelled_sum_moebius (E : ℕ+ ≃* M) (x : M) :
    ∑ d ∈ labelledDivisors E x, labelledMoebius E d = labelledDelta x := by
  have h := congrFun (labelled_moebius_convolution (R := ℤ) E) x
  simpa only [labelled_convolution_sum, Int.cast_id, mul_one] using h

theorem labelled_divisor_sum_as_convolution [Semiring R] (E : ℕ+ ≃* M) (f : M → R) (x : M) :
    ∑ d ∈ labelledDivisors E x, f d=labelledConvolution E f (fun _ => 1) x := by
  simp only [labelled_convolution_sum, mul_one]

theorem labelled_moebius_inversion [CommRing R] (E : ℕ+ ≃* M) (f F : M → R)
    (hF : ∀ x, F x=∑ d ∈ labelledDivisors E x, f d) (x : M) :
    f x=∑ d ∈ labelledDivisors E x, (labelledMoebius E d : R)*F (labelledQuotient E x d) := by
  have he : F=labelledConvolution E f (fun _ => 1) := by
    funext x
    rw [hF, labelled_divisor_sum_as_convolution]
  rw [← labelled_convolution_sum, he, labelled_convolution_comm E f,
    ← labelled_convolution_assoc, labelled_moebius_convolution,
    labelled_convolution_one_left]

theorem labelled_moebius_inversion_iff [CommRing R] (E : ℕ+ ≃* M) (f F : M → R) :
    (∀ x, F x=∑ d ∈ labelledDivisors E x, f d) ↔
      ∀ x, f x=∑ d ∈ labelledDivisors E x, (labelledMoebius E d : R)*F (labelledQuotient E x d) := by
  constructor
  · exact fun h x => labelled_moebius_inversion E f F h x
  · intro h
    have he : f=labelledConvolution E (fun x => (labelledMoebius E x : R)) F := by
      funext x
      rw [h, labelled_convolution_sum]
    intro x
    rw [labelled_divisor_sum_as_convolution, he, labelled_convolution_comm E _ F,
      labelled_convolution_assoc, labelled_moebius_convolution,
      labelled_convolution_one_right]

theorem labelled_squarefree_iff (E : ℕ+ ≃* M) (x : M) :
    Squarefree (E.symm x).val ↔ ∀ p : Nat.Primes, labelledValuation E p x ≤ 1 := by
  rw [Nat.squarefree_iff_prime_squarefree]
  constructor
  · intro h p
    by_contra hn
    have hd := (labelled_valuation_maximum E p x 2).mpr (by omega)
    have hd' := PNat.dvd_iff.mp ((labelled_dvd_iff E _ _).mp hd)
    simp only [map_pow, E.symm_apply_apply, PNat.pow_coe] at hd'
    exact h p p.property (by simpa only [pow_two] using hd')
  · intro h p hp hd
    have hd' : E (⟨p,hp.pos⟩ : ℕ+)^2 ∣ x := by
      rw [labelled_dvd_iff, map_pow, E.symm_apply_apply]
      exact PNat.dvd_iff.mpr (by simpa only [PNat.pow_coe, pow_two] using hd)
    have hv := (labelled_valuation_maximum E (⟨p,hp⟩ : Nat.Primes) x 2).mp hd'
    have := h ⟨p,hp⟩
    omega

theorem labelled_factor_count_native (E : ℕ+ ≃* M) (x : M) :
    ArithmeticFunction.cardFactors (E.symm x).val=labelledOmega E x := by
  rw [ArithmeticFunction.cardFactors_apply]
  have h := congrArg Multiset.card (PNat.coeNat_factorMultiset (E.symm x))
  change ((E.symm x).factorMultiset.map (fun p : Nat.Primes => (p:ℕ))).card=
    ((E.symm x).val.primeFactorsList : Multiset ℕ).card at h
  simpa only [Multiset.card_map, Multiset.coe_card] using h.symm

theorem labelled_squarefree_factor_counts (E : ℕ+ ≃* M) (x : M)
    (hx : Squarefree (E.symm x).val) : labelledOmega E x=labelledLittleOmega E x := by
  classical
  have hn : (labelledFactors E x).Nodup :=
    Multiset.nodup_iff_count_le_one.mpr ((labelled_squarefree_iff E x).mp hx)
  exact (Multiset.toFinset_card_of_nodup hn).symm

theorem labelled_moebius_formula (E : ℕ+ ≃* M) (x : M) :
    labelledMoebius E x =
      if ∃ p : Nat.Primes, 2 ≤ labelledValuation E p x then 0
      else (-1 : ℤ)^(labelledLittleOmega E x) := by
  classical
  by_cases h : ∃ p : Nat.Primes, 2 ≤ labelledValuation E p x
  · rw [if_pos h]
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro hs
    obtain ⟨p,hp⟩ := h
    have := (labelled_squarefree_iff E x).mp hs p
    omega
  · rw [if_neg h]
    have hs : Squarefree (E.symm x).val := (labelled_squarefree_iff E x).mpr (by
      intro p
      by_contra hp
      exact h ⟨p,by omega⟩)
    rw [labelledMoebius, ArithmeticFunction.moebius_apply_of_squarefree hs,
      labelled_factor_count_native, labelled_squarefree_factor_counts E x hs]

end
end Sigma
