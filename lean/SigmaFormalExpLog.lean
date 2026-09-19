import SigmaFormalAutomorphisms
import SigmaRealTreesExponential
import SigmaFormalSeries

namespace Sigma
noncomputable section
open PowerSeries
open scoped BigOperators
variable (K : Type*) [Field K] [CharZero K]

def formalLogarithm : PowerSeries K := PowerSeries.mk fun n =>
  match n with
  | 0 => 0
  | n+1 => (-1:K)^n / ((n+1:ℕ):K)

omit [CharZero K] in
theorem formal_logarithm_constant : constantCoeff K (formalLogarithm K)=0 := by
  simp [formalLogarithm]

theorem formal_logarithm_derivative_coeff (n : ℕ) :
    coeff K n (derivative K (formalLogarithm K))=(-1:K)^n := by
  have hn : (n:K)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp [coeff_derivative, formalLogarithm, hn]

theorem formal_logarithm_ode : (1+X)*derivative K (formalLogarithm K)=1 := by
  ext n
  rw [add_mul, one_mul, map_add]
  cases n with
  | zero => rw [formal_logarithm_derivative_coeff]; simp
  | succ n =>
    rw [coeff_succ_X_mul, formal_logarithm_derivative_coeff, formal_logarithm_derivative_coeff]
    simp [coeff_one, pow_succ]

theorem formal_logarithm_unique (F : PowerSeries K)
    (h0 : constantCoeff K F=0) (hd : (1+X)*derivative K F=1) :
    F=formalLogarithm K := by
  apply PowerSeries.derivative.ext _ (h0.trans (formal_logarithm_constant K).symm)
  apply mul_left_cancel₀ (show (1+(X:PowerSeries K)) ≠ 0 from ?_)
  · exact hd.trans (formal_logarithm_ode K).symm
  · intro h
    have hc := congrArg (constantCoeff K) h
    simp at hc

theorem formal_compose_exp (G : PowerSeries K) :
    formalCompose (formalExponential K 1) G=treeExp K G := by
  ext n
  simp [formalCompose, formalExponential, treeExp, treeExpPartial, coeff_rescale, coeff_exp]

omit [CharZero K] in
theorem formal_compose_sub (F H G : PowerSeries K) :
    formalCompose (F-H) G=formalCompose F G-formalCompose H G := by
  ext n
  simp [formalCompose, sub_mul, Finset.sum_sub_distrib]

omit [CharZero K] in
theorem formal_compose_one (G : PowerSeries K) : formalCompose 1 G=1 := by
  ext n
  simp [formalCompose, coeff_one, ite_mul]

theorem formal_exp_log_inverse :
    formalCompose (formalExponential K 1-1) (formalLogarithm K)=X := by
  rw [formal_compose_sub, formal_compose_exp, formal_compose_one]
  have he : treeExp K (formalLogarithm K)=1+X := by
    apply formal_binomial_ode_unique _ _ (1:K)
    · simp [tree_exp_constant]
    · rw [tree_exp_derivative K _ (formal_logarithm_constant K)]
      simp only [map_one, one_mul]
      linear_combination treeExp K (formalLogarithm K)*formal_logarithm_ode K
    · simp
  rw [he]
  ring

def formalLogPartial (G : PowerSeries K) (m : ℕ) : PowerSeries K :=
  ∑ j ∈ Finset.range m, C K ((-1:K)^j/((j+1:ℕ):K))*G^(j+1)

omit [CharZero K] in
theorem formal_log_partial_coeff (G : PowerSeries K) (hG : constantCoeff K G=0)
    (n m : ℕ) (hnm : n < m) :
    coeff K n (formalLogPartial K G m)=coeff K n (formalCompose (formalLogarithm K) G) := by
  simp only [formalLogPartial, map_sum, coeff_C_mul, formalCompose, coeff_mk]
  rw [Finset.sum_range_succ', show coeff K 0 (formalLogarithm K)=0 by simp [formalLogarithm],
    zero_mul, add_zero]
  simp only [formalLogarithm, coeff_mk]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j hj hnot
  rw [tree_power_coeff_above K G hG n (j+1) (by simp only [Finset.mem_range] at hnot; omega), mul_zero]

theorem formal_log_partial_derivative (G : PowerSeries K) (m : ℕ) :
    (1+G)*derivative K (formalLogPartial K G m)=
      derivative K G*(1-(-G)^m) := by
  induction m with
  | zero => simp [formalLogPartial]
  | succ m ih =>
    have hm : ((m+1:ℕ):K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    have hc : C K ((-1:K)^m/((m+1:ℕ):K))*((m+1:ℕ):PowerSeries K)=C K ((-1:K)^m) := by
      have he := congrArg (C K) (div_mul_cancel₀ ((-1:K)^m) hm)
      simpa only [map_mul, map_natCast] using he
    simp only [formalLogPartial, Finset.sum_range_succ] at ih ⊢
    rw [map_add, Derivation.leibniz, derivative_C, smul_zero, add_zero,
      Derivation.leibniz_pow]
    simp only [Nat.succ_sub_one, smul_eq_mul, nsmul_eq_mul]
    rw [show C K ((-1:K)^m/((m+1:ℕ):K))*
        (((m+1:ℕ):PowerSeries K)*(G^m*derivative K G))=
        C K ((-1:K)^m)*G^m*derivative K G by rw [← hc]; ring]
    rw [pow_succ (-G) m, neg_pow G m]
    simp only [map_pow, map_neg, map_one]
    linear_combination ih

theorem formal_log_compose_derivative (G : PowerSeries K) (hG : constantCoeff K G=0) :
    (1+G)*derivative K (formalCompose (formalLogarithm K) G)=derivative K G := by
  ext n
  have he : (X:PowerSeries K)^(n+1) ∣
      derivative K (formalCompose (formalLogarithm K) G)-derivative K (formalLogPartial K G (n+2)) := by
    apply X_pow_dvd_iff.mpr
    intro i hi
    simp only [map_sub, coeff_derivative,
      formal_log_partial_coeff K G hG (i+1) (n+2) (by omega), sub_self]
  have hc := X_pow_dvd_iff.mp (he.mul_left (1+G)) n (by omega)
  rw [mul_sub, map_sub, formal_log_partial_derivative] at hc
  have hz : coeff K n (derivative K G*(-G)^(n+2))=0 := by
    apply X_pow_dvd_iff.mp _ n (by omega : n < n+2)
    exact (pow_dvd_pow_of_dvd (X_dvd_iff.mpr (by simp [hG])) (n+2)).mul_left _
  simpa only [mul_sub, mul_one, map_sub, hz, sub_zero] using sub_eq_zero.mp hc

theorem formal_log_exp_inverse :
    formalCompose (formalLogarithm K) (formalExponential K 1-1)=X := by
  apply PowerSeries.derivative.ext
  · have h := formal_log_compose_derivative K (formalExponential K 1-1)
      (by simp [formal_exponential_constant])
    simp only [map_sub, Derivation.map_one_eq_zero, formal_exponential_derivative, map_one, one_mul,
      sub_zero, show 1+(formalExponential K 1-1)=formalExponential K 1 by ring] at h
    apply mul_left_cancel₀ (show formalExponential K 1 ≠ 0 from ?_)
    · simpa using h
    · intro hz
      have hc := congrArg (constantCoeff K) hz
      simp [formal_exponential_constant] at hc
  · simp [formalCompose, formalLogarithm]

theorem formal_exp_inverse_unique (F : PowerSeries K) (h0 : constantCoeff K F=0)
    (hi : formalCompose (formalExponential K 1-1) F=X) : F=formalLogarithm K := by
  rw [formal_compose_sub, formal_compose_exp, formal_compose_one] at hi
  have he : treeExp K F=1+X := by linear_combination hi
  apply formal_logarithm_unique K F h0
  have hd := congrArg (derivative K) he
  rw [tree_exp_derivative K F h0, he] at hd
  simpa [mul_comm] using hd

theorem formal_logarithm_rational : formalLogarithm ℚ=SigmaPresentations.formalLog := rfl

end
end Sigma
