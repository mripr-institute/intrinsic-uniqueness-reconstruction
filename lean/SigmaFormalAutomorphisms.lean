import SigmaToddArbitraryPower
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.Polynomial.Roots

namespace Sigma
noncomputable section
open PowerSeries
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]

/-- Standard formal scalar power of 1+X. -/
def formalBinomialUnit (c : K) : PowerSeries K :=
  formalBinomialPower (1+X) c

theorem formal_binomial_unit_coeff (c : K) (n : ℕ) :
    coeff K n (formalBinomialUnit c) = scalarFallingFactorial c n/(n.factorial : K) := by
  simp only [formalBinomialUnit, formalBinomialPower, coeff_mk,
    show (1+(X : PowerSeries K))-1=X by ring, coeff_X_pow]
  simp [mul_ite]

omit [CharZero K] in
theorem scalar_falling_factorial_succ (c : K) (n : ℕ) :
    scalarFallingFactorial c (n+1)=scalarFallingFactorial c n*(c-n) := by
  exact Finset.prod_range_succ _ _

theorem formal_binomial_unit_recurrence (c : K) (n : ℕ) :
    coeff K (n+1) (formalBinomialUnit c)*((n:K)+1) =
      (c-n)*coeff K n (formalBinomialUnit c) := by
  rw [formal_binomial_unit_coeff, formal_binomial_unit_coeff,
    scalar_falling_factorial_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  have hn : (n:K)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial:K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp
  ring

theorem formal_binomial_unit_constant (c : K) : constantCoeff K (formalBinomialUnit c)=1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, formal_binomial_unit_coeff]
  simp [scalarFallingFactorial]

theorem formal_binomial_unit_ode (c : K) :
    (1+X)*derivative K (formalBinomialUnit c)=C K c*formalBinomialUnit c := by
  ext n
  rw [add_mul, one_mul, map_add, coeff_C_mul]
  cases n with
  | zero =>
    simp only [coeff_zero_X_mul, add_zero, coeff_derivative, Nat.cast_zero, zero_add, mul_one]
    simpa using formal_binomial_unit_recurrence c 0
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative, coeff_derivative]
    have h := formal_binomial_unit_recurrence c (n+1)
    push_cast at h ⊢
    linear_combination h

theorem formal_binomial_ode_unique (F G : PowerSeries K) (c : K)
    (h0 : constantCoeff K F=constantCoeff K G)
    (hF : (1+X)*derivative K F=C K c*F)
    (hG : (1+X)*derivative K G=C K c*G) : F=G := by
  ext n
  induction n with
  | zero => simpa only [coeff_zero_eq_constantCoeff_apply] using h0
  | succ n ih =>
    have hf := congrArg (coeff K n) hF
    have hg := congrArg (coeff K n) hG
    rw [add_mul, one_mul, map_add, coeff_derivative, coeff_C_mul] at hf hg
    have hx : coeff K n (X*derivative K F)=coeff K n (X*derivative K G) := by
      cases n with
      | zero => simp
      | succ n => rw [coeff_succ_X_mul, coeff_succ_X_mul, coeff_derivative, coeff_derivative, ih]
    have hn : (n:K)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    apply mul_right_cancel₀ hn
    rw [ih, hx] at hf
    linear_combination hf-hg

/-- The family in the paper: (1+X)^c-1, with scalar powers interpreted by the
usual formal binomial expansion. -/
def formalStarPower (c : K) : PowerSeries K := formalBinomialUnit c-1

theorem formal_star_power_constant (c : K) : constantCoeff K (formalStarPower c)=0 := by
  simp [formalStarPower, formal_binomial_unit_constant]

theorem formal_star_power_tangent (c : K) : coeff K 1 (formalStarPower c)=c := by
  simp [formalStarPower, formal_binomial_unit_coeff, scalarFallingFactorial]

theorem formal_star_power_ode (c : K) :
    (1+X)*derivative K (formalStarPower c)=C K c*(1+formalStarPower c) := by
  simpa [formalStarPower] using formal_binomial_unit_ode c

/-- Actual substitution by X+Y+XY, expanded in Y. Its Y^j coefficient is the
j-th formal Taylor coefficient at X, multiplied by (1+X)^j. -/
def formalStarPullback (F : PowerSeries K) : PowerSeries (PowerSeries K) :=
  PowerSeries.mk fun j => (1+X)^j *
    PowerSeries.mk (fun i => (coeff K (i+j) F)*((i+j).choose j : K))

/-- The full two-variable multiplicative formal-group identity, not its
first-order differential consequence. -/
def IsFormalStarEndomorphism (F : PowerSeries K) : Prop :=
  constantCoeff K F=0 ∧
    formalStarPullback F = C (PowerSeries K) F + PowerSeries.map (C K) F +
      C (PowerSeries K) F*PowerSeries.map (C K) F

omit [CharZero K] in
theorem formal_star_pullback_one (F : PowerSeries K) :
    coeff (PowerSeries K) 1 (formalStarPullback F) = (1+X)*derivative K F := by
  simp only [formalStarPullback, coeff_mk, pow_one]
  congr 1
  ext i
  simp [coeff_derivative]

omit [CharZero K] in
theorem formal_star_endomorphism_ode (F : PowerSeries K)
    (hF : IsFormalStarEndomorphism F) :
    (1+X)*derivative K F=C K (coeff K 1 F)*(1+F) := by
  have h := congrArg (coeff (PowerSeries K) 1) hF.2
  rw [formal_star_pullback_one] at h
  simp only [map_add, coeff_C, one_ne_zero, if_false, coeff_map,
    coeff_C_mul, zero_add] at h
  linear_combination h

theorem formal_star_endomorphism_classification (F : PowerSeries K)
    (hF : IsFormalStarEndomorphism F) : F=formalStarPower (coeff K 1 F) := by
  have h := formal_binomial_ode_unique (1+F) (formalBinomialUnit (coeff K 1 F))
    (coeff K 1 F) (by simp [hF.1, formal_binomial_unit_constant])
    (by simpa using formal_star_endomorphism_ode F hF)
    (formal_binomial_unit_ode _)
  unfold formalStarPower
  linear_combination h

theorem formal_binomial_ode_of_recurrence (F : PowerSeries K) (c : K)
    (h : ∀ n, coeff K (n+1) F*((n:K)+1)=(c-n)*coeff K n F) :
    (1+X)*derivative K F=C K c*F := by
  ext n
  rw [add_mul, one_mul, map_add, coeff_C_mul]
  cases n with
  | zero =>
    simp only [coeff_zero_X_mul, add_zero, coeff_derivative, Nat.cast_zero, zero_add, mul_one]
    simpa using h 0
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative, coeff_derivative]
    have hn := h (n+1)
    push_cast at hn ⊢
    linear_combination hn

omit [CharZero K] in
theorem formal_binomial_ode_mul (F G : PowerSeries K) (c d : K)
    (hF : (1+X)*derivative K F=C K c*F)
    (hG : (1+X)*derivative K G=C K d*G) :
    (1+X)*derivative K (F*G)=C K (c+d)*(F*G) := by
  rw [map_add, (derivative K).leibniz]
  simp only [smul_eq_mul]
  linear_combination G*hF+F*hG

theorem formal_binomial_unit_add (c d : K) :
    formalBinomialUnit c*formalBinomialUnit d=formalBinomialUnit (c+d) := by
  apply formal_binomial_ode_unique _ _ (c+d)
  · simp [formal_binomial_unit_constant]
  · exact formal_binomial_ode_mul _ _ c d (formal_binomial_unit_ode c) (formal_binomial_unit_ode d)
  · exact formal_binomial_unit_ode _

theorem formal_binomial_unit_nat (n : ℕ) : formalBinomialUnit (n:K)=(1+X)^n := by
  exact formal_binomial_power_nat _ (by simp) n

def formalTaylorCoefficient (F : PowerSeries K) (j : ℕ) : PowerSeries K :=
  PowerSeries.mk fun i => coeff K (i+j) F*((i+j).choose j : K)

theorem binomial_taylor_recurrence (c : K) (i j : ℕ) :
    coeff K (i+1) (formalTaylorCoefficient (formalBinomialUnit c) j)*((i:K)+1) =
      (c-j-i)*coeff K i (formalTaylorCoefficient (formalBinomialUnit c) j) := by
  simp only [formalTaylorCoefficient, coeff_mk]
  have h := formal_binomial_unit_recurrence c (i+j)
  have hn := Nat.choose_mul_succ_eq (i+j) j
  rw [show i+j+1-j=i+1 by omega] at hn
  have hc := congrArg (fun n : ℕ => (n:K)) hn
  push_cast at h hc
  rw [show i+1+j=i+j+1 by omega]
  calc
    _ = coeff K (i+j+1) (formalBinomialUnit c)*
        (((i+j+1).choose j:K)*((i:K)+1)) := by ring
    _ = coeff K (i+j+1) (formalBinomialUnit c)*
        (((i+j).choose j:K)*((i:K)+j+1)) := by rw [hc]
    _ = _ := by linear_combination ((i+j).choose j:K)*h

theorem formal_binomial_taylor (c : K) (j : ℕ) :
    formalTaylorCoefficient (formalBinomialUnit c) j =
      C K (coeff K j (formalBinomialUnit c))*formalBinomialUnit (c-j) := by
  apply formal_binomial_ode_unique _ _ (c-j)
  · rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
      coeff_C_mul, formalTaylorCoefficient, coeff_mk]
    simp [formal_binomial_unit_coeff, scalarFallingFactorial]
  · apply formal_binomial_ode_of_recurrence
    intro i
    exact binomial_taylor_recurrence c i j
  · rw [(derivative K).leibniz]
    simp only [derivative_C, smul_eq_mul, mul_zero, zero_add]
    linear_combination C K (coeff K j (formalBinomialUnit c))*formal_binomial_unit_ode (c-j)

theorem formal_binomial_unit_pullback (c : K) :
    formalStarPullback (formalBinomialUnit c) =
      C (PowerSeries K) (formalBinomialUnit c)*PowerSeries.map (C K) (formalBinomialUnit c) := by
  apply PowerSeries.ext
  intro j
  rw [coeff_C_mul, coeff_map]
  simp only [formalStarPullback, coeff_mk]
  change (1+X)^j*formalTaylorCoefficient (formalBinomialUnit c) j = _
  rw [formal_binomial_taylor, ← formal_binomial_unit_nat]
  calc
    _ = C K (coeff K j (formalBinomialUnit c)) *
        (formalBinomialUnit (j:K)*formalBinomialUnit (c-j)) := by ring
    _ = _ := by rw [formal_binomial_unit_add, add_sub_cancel]; ring

theorem formal_star_power_is_endomorphism (c : K) :
    IsFormalStarEndomorphism (formalStarPower c) := by
  refine ⟨formal_star_power_constant c, ?_⟩
  have hp := formal_binomial_unit_pullback c
  have hsub : formalStarPullback (formalStarPower c) =
      formalStarPullback (formalBinomialUnit c)-1 := by
    apply PowerSeries.ext
    intro j
    have ht : formalTaylorCoefficient (formalStarPower c) j =
        formalTaylorCoefficient (formalBinomialUnit c) j-
          formalTaylorCoefficient (1 : PowerSeries K) j := by
      ext i
      simp [formalTaylorCoefficient, formalStarPower, sub_mul]
    rw [formalStarPullback, coeff_mk]
    change (1+X)^j*formalTaylorCoefficient (formalStarPower c) j = _
    rw [ht, mul_sub, map_sub]
    simp only [formalStarPullback, coeff_mk]
    congr 1
    by_cases hj : j=0
    · subst j
      simp only [pow_zero, one_mul, coeff_one, if_true]
      ext i
      simp [formalTaylorCoefficient]
    · have hz : formalTaylorCoefficient (1 : PowerSeries K) j=0 := by
        ext i
        simp [formalTaylorCoefficient, coeff_one, hj]
      simp [hz, hj]
  rw [hsub, hp]
  simp only [formalStarPower, map_sub, map_one]
  ring

/-- Genuine coefficientwise substitution. For a zero-constant inner series,
terms above the observed degree vanish, making the displayed sum exact. -/
def formalCompose (F G : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => ∑ j ∈ Finset.range (n+1), coeff K j F*coeff K n (G^j)

theorem formal_compose_star_power (c : K) (G : PowerSeries K) :
    formalCompose (formalStarPower c) G=formalBinomialPower (1+G) c-1 := by
  ext n
  simp only [formalCompose, formalStarPower, coeff_mk, map_sub,
    formal_binomial_unit_coeff, sub_mul, Finset.sum_sub_distrib,
    formalBinomialPower, show (1+G)-1=G by ring]
  congr 1
  simp [coeff_one, ite_mul]

theorem formal_binomial_unit_pow (c : K) (m : ℕ) :
    formalBinomialUnit c^m=formalBinomialUnit ((m:K)*c) := by
  induction m with
  | zero => simpa using (formal_binomial_unit_nat (K := K) 0).symm
  | succ m hm =>
    rw [pow_succ, hm, formal_binomial_unit_add]
    push_cast
    rw [add_mul, one_mul]

def scalarBinomialPolynomial (n : ℕ) : Polynomial K :=
  Polynomial.C ((n.factorial:K)⁻¹) *
    ∏ j ∈ Finset.range n, (Polynomial.X-Polynomial.C (j:K))

theorem scalar_binomial_polynomial_eval (n : ℕ) (c : K) :
    (scalarBinomialPolynomial (K := K) n).eval c =
      scalarFallingFactorial c n/(n.factorial:K) := by
  simp only [scalarBinomialPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, scalarFallingFactorial]
  ring

theorem polynomial_eq_of_nat_evals (P Q : Polynomial K)
    (h : ∀ m : ℕ, P.eval (m:K)=Q.eval (m:K)) : P=Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := K))).mono
  rintro _ ⟨m,rfl⟩
  exact h m

theorem formal_binomial_unit_nested (c d : K) :
    formalBinomialPower (formalBinomialUnit d) c=formalBinomialUnit (c*d) := by
  ext n
  let P : Polynomial K := ∑ j ∈ Finset.range (n+1),
    scalarBinomialPolynomial j * Polynomial.C (coeff K n ((formalBinomialUnit d-1)^j))
  let Q : Polynomial K := (scalarBinomialPolynomial n).comp (Polynomial.X*Polynomial.C d)
  have hP (a : K) : P.eval a=coeff K n (formalBinomialPower (formalBinomialUnit d) a) := by
    simp only [P, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      scalar_binomial_polynomial_eval, formalBinomialPower, coeff_mk]
  have hQ (a : K) : Q.eval a=coeff K n (formalBinomialUnit (a*d)) := by
    simp only [Q, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C, scalar_binomial_polynomial_eval, formal_binomial_unit_coeff]
  have he : P=Q := by
    apply polynomial_eq_of_nat_evals
    intro m
    rw [hP, hQ, formal_binomial_power_nat _ (formal_binomial_unit_constant d),
      formal_binomial_unit_pow]
  rw [← hP, ← hQ, he]

theorem formal_star_power_composition (c d : K) :
    formalCompose (formalStarPower c) (formalStarPower d)=formalStarPower (c*d) := by
  rw [formal_compose_star_power]
  simp only [formalStarPower, add_sub_cancel_left, add_sub_cancel_right,
    show ∀ U : PowerSeries K, 1+(U-1)=U by intro U; ring]
  rw [formal_binomial_unit_nested]

theorem formal_star_power_one : formalStarPower (1:K)=X := by
  have h := formal_binomial_unit_nat (K := K) 1
  simp only [Nat.cast_one, pow_one] at h
  simp [formalStarPower, h]

theorem formal_star_power_inverse (c : K) (hc : c ≠ 0) :
    formalCompose (formalStarPower c) (formalStarPower c⁻¹)=X ∧
      formalCompose (formalStarPower c⁻¹) (formalStarPower c)=X := by
  simp only [formal_star_power_composition, mul_inv_cancel₀ hc, inv_mul_cancel₀ hc,
    formal_star_power_one, and_self]

/-- A formal automorphism includes an actual zero-constant compositional
inverse. In particular nonzero tangent is a conclusion, not an assumption. -/
def IsFormalStarAutomorphism (F : PowerSeries K) : Prop :=
  IsFormalStarEndomorphism F ∧ ∃ G : PowerSeries K,
    constantCoeff K G=0 ∧ formalCompose F G=X ∧ formalCompose G F=X

omit [CharZero K] in
theorem formal_compose_tangent (F G : PowerSeries K) :
    coeff K 1 (formalCompose F G)=coeff K 1 F*coeff K 1 G := by
  simp [formalCompose, Finset.sum_range_succ]

theorem formal_star_automorphism_classification (F : PowerSeries K) :
    IsFormalStarAutomorphism F ↔ ∃ c : K, c ≠ 0 ∧ F=formalStarPower c := by
  constructor
  · rintro ⟨hF,G,hG,hFG,_⟩
    refine ⟨coeff K 1 F, ?_, formal_star_endomorphism_classification F hF⟩
    have h := congrArg (coeff K 1) hFG
    rw [formal_compose_tangent F G, coeff_X] at h
    simp only [if_pos rfl] at h
    intro hc
    rw [hc, zero_mul] at h
    exact zero_ne_one h
  · rintro ⟨c,hc,rfl⟩
    exact ⟨formal_star_power_is_endomorphism c, formalStarPower c⁻¹,
      formal_star_power_constant _, (formal_star_power_inverse c hc).1,
      (formal_star_power_inverse c hc).2⟩

omit [CharZero K] in
theorem formal_compose_monomial (a : K) (m : ℕ) (G : PowerSeries K)
    (hG : constantCoeff K G=0) :
    formalCompose (PowerSeries.monomial K m a) G=C K a*G^m := by
  ext n
  rw [formalCompose, coeff_mk, coeff_C_mul]
  simp only [coeff_monomial, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  by_cases hm : m < n+1
  · simp [hm]
  · have hz : coeff K n (G^m)=0 :=
      X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hG) m) n (by omega)
    simp [hm, hz]

omit [CharZero K] in
theorem formal_compose_add (F H G : PowerSeries K) :
    formalCompose (F+H) G=formalCompose F G+formalCompose H G := by
  ext n
  simp [formalCompose, add_mul, Finset.sum_add_distrib]

omit [CharZero K] in
theorem formal_compose_polynomial (P : Polynomial K) (G : PowerSeries K)
    (hG : constantCoeff K G=0) :
    formalCompose (P : PowerSeries K) G=P.eval₂ (C K) G := by
  induction P using Polynomial.induction_on' with
  | h_add P Q hP hQ => simp [Polynomial.coe_add, formal_compose_add, hP, hQ]
  | h_monomial n a =>
    rw [Polynomial.coe_monomial, formal_compose_monomial a n G hG,
      Polynomial.eval₂_monomial]

theorem formal_star_endomorphism_iff (F : PowerSeries K) :
    IsFormalStarEndomorphism F ↔ ∃ c : K, F=formalStarPower c := by
  constructor
  · intro h
    exact ⟨coeff K 1 F, formal_star_endomorphism_classification F h⟩
  · rintro ⟨c,rfl⟩
    exact formal_star_power_is_endomorphism c

theorem power_series_affine_coeff {R : Type*} [CommRing R] (a b : R) (m j : ℕ) :
    coeff R j ((C R b*X+C R a)^m) = b^j*a^(m-j)*(m.choose j : R) := by
  rw [add_pow, map_sum]
  have ht (i : ℕ) :
      coeff R j ((C R b*X)^i*(C R a)^(m-i)*(m.choose i : PowerSeries R)) =
        if j=i then b^i*a^(m-i)*(m.choose i : R) else 0 := by
    have he : (C R b*X)^i*(C R a)^(m-i)*(m.choose i : PowerSeries R) =
        C R (b^i*a^(m-i)*(m.choose i : R))*X^i := by
      simp only [mul_pow, ← map_pow, map_mul, map_natCast]
      ring
    rw [he, coeff_C_mul_X_pow]
  simp_rw [ht]
  rw [Finset.sum_ite_eq]
  by_cases hj : j < m+1
  · simp [hj]
  · simp [hj, Nat.choose_eq_zero_of_lt (by omega : m < j)]

omit [CharZero K] in
theorem formal_taylor_X_pow (m j : ℕ) :
    formalTaylorCoefficient ((X : PowerSeries K)^m) j =
      C K (m.choose j : K)*X^(m-j) := by
  ext i
  simp only [formalTaylorCoefficient, coeff_mk, coeff_X_pow, coeff_C_mul]
  by_cases hj : j ≤ m
  · have he : i+j=m ↔ i=m-j := by omega
    by_cases hi : i=m-j
    · have him : i+j=m := he.mpr hi
      simp [hi, him, Nat.sub_add_cancel hj]
    · simp [hi, he]
  · have him : i+j≠m := by omega
    simp [him, Nat.choose_eq_zero_of_lt (by omega : m < j)]

omit [CharZero K] in
/-- The pullback really substitutes the native two-variable group polynomial:
on every monomial it is exactly the corresponding native power. -/
theorem formal_star_pullback_X_pow (m : ℕ) :
    formalStarPullback ((X : PowerSeries K)^m) =
      (C (PowerSeries K) X+X+C (PowerSeries K) X*X)^m := by
  apply PowerSeries.ext
  intro j
  have he : (C (PowerSeries K) X+X+C (PowerSeries K) X*X) =
      C (PowerSeries K) (1+X)*X+C (PowerSeries K) X := by
    rw [map_add, map_one]
    ring
  rw [he, power_series_affine_coeff]
  simp only [formalStarPullback, coeff_mk]
  change (1+X)^j*formalTaylorCoefficient ((X : PowerSeries K)^m) j = _
  rw [formal_taylor_X_pow]
  simp only [map_natCast]
  ring

omit [CharZero K] in
/-- Total-degree locality makes the two-variable pullback the unique formal
extension of its polynomial substitution, rather than an ODE-defined operator. -/
theorem formal_star_pullback_locality (F G : PowerSeries K) (i j : ℕ)
    (h : ∀ n ≤ i+j, coeff K n F=coeff K n G) :
    coeff K i (coeff (PowerSeries K) j (formalStarPullback F)) =
      coeff K i (coeff (PowerSeries K) j (formalStarPullback G)) := by
  simp only [formalStarPullback, coeff_mk, coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hpi := Finset.mem_antidiagonal.mp hp
  rw [h (p.2+j) (by omega)]

theorem formal_star_automorphism_tangent_iff (F : PowerSeries K) :
    IsFormalStarAutomorphism F ↔ IsFormalStarEndomorphism F ∧ coeff K 1 F ≠ 0 := by
  rw [formal_star_automorphism_classification]
  constructor
  · rintro ⟨c,hc,rfl⟩
    exact ⟨formal_star_power_is_endomorphism c, by simpa [formal_star_power_tangent] using hc⟩
  · rintro ⟨hF,hc⟩
    exact ⟨coeff K 1 F,hc,formal_star_endomorphism_classification F hF⟩

theorem formal_star_power_parameter_injective : Function.Injective (formalStarPower (K := K)) := by
  intro c d h
  have ht := congrArg (coeff K 1) h
  simpa only [formal_star_power_tangent] using ht

theorem formal_star_endomorphism_calibration (F : PowerSeries K)
    (hF : IsFormalStarEndomorphism F) : coeff K 1 F=1 ↔ F=X := by
  constructor
  · intro h
    rw [formal_star_endomorphism_classification F hF, h, formal_star_power_one]
  · rintro rfl
    simp

end
end Sigma
