import SigmaRealTreesExponential

namespace Sigma
noncomputable section
open PowerSeries

variable (K : Type*) [Field K] [CharZero K]

/-- Coefficient recursion for R=X exp(R); the right side uses only earlier coefficients. -/
def rootedCoefficient (n : ℕ) : K :=
  if _hn : n = 0 then 0 else
    coeff K (n - 1) (treeExp K (PowerSeries.mk fun j =>
      if _hj : j < n then rootedCoefficient j else 0))
termination_by n

def rootedSeries : PowerSeries K := PowerSeries.mk (rootedCoefficient K)

omit [CharZero K] in
theorem rooted_coefficient_zero : rootedCoefficient K 0 = 0 := by
  rw [rootedCoefficient]
  simp

omit [CharZero K] in
theorem rooted_series_constant : constantCoeff K (rootedSeries K) = 0 := by
  simp [rootedSeries, rooted_coefficient_zero]

omit [CharZero K] in
theorem rooted_series_coefficient_succ (n : ℕ) :
    coeff K (n + 1) (rootedSeries K) = coeff K n (treeExp K (rootedSeries K)) := by
  simp only [rootedSeries, coeff_mk]
  rw [rootedCoefficient, dif_neg (Nat.succ_ne_zero n)]
  simp only [Nat.add_sub_cancel, dite_eq_ite]
  apply tree_exp_coeff_congr K
  intro j hj
  simp [hj, show j < n + 1 by omega]

omit [CharZero K] in
theorem rooted_series_fixed_point : rootedSeries K = X * treeExp K (rootedSeries K) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [rooted_series_constant]
  | succ n =>
    rw [rooted_series_coefficient_succ]
    simp [pow_one, Nat.add_comm]

omit [CharZero K] in
theorem rooted_series_linear : coeff K 1 (rootedSeries K) = 1 := by
  rw [show 1 = 0 + 1 from rfl, rooted_series_coefficient_succ]
  simp [tree_exp_constant]

omit [CharZero K] in
theorem rooted_series_unique (F : PowerSeries K)
    (hF : F = X * treeExp K F) : F = rootedSeries K := by
  have hf0 : constantCoeff K F = 0 := by rw [hF]; simp
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa using hf0.trans (rooted_series_constant K).symm
    | succ n =>
      have hc : coeff K (n + 1) F = coeff K n (treeExp K F) := by
        calc
          coeff K (n + 1) F = coeff K (n + 1) (X * treeExp K F) := congrArg (coeff K (n + 1)) hF
          _ = coeff K n (treeExp K F) := by simp [Nat.add_comm]
      rw [hc, rooted_series_coefficient_succ]
      exact tree_exp_coeff_congr K F (rootedSeries K) n (fun j hj => ih j (by omega))

omit [CharZero K] in
theorem rooted_series_exists_unique :
    ∃! F : PowerSeries K, F = X * treeExp K F :=
  ⟨rootedSeries K, rooted_series_fixed_point K, fun F hF => rooted_series_unique K F hF⟩

/-- Formal substitution into t exp(-t) is the marked inverse identity. -/
theorem rooted_series_inverse_identity :
    rootedSeries K * treeExp K (-rootedSeries K) = X := by
  have h := tree_exp_neg_product K (rootedSeries K) (rooted_series_constant K)
  calc
    rootedSeries K * treeExp K (-rootedSeries K) =
        (X * treeExp K (rootedSeries K)) * treeExp K (-rootedSeries K) :=
          congrArg (fun r => r * treeExp K (-rootedSeries K)) (rooted_series_fixed_point K)
    _ = X * (treeExp K (rootedSeries K) * treeExp K (-rootedSeries K)) := by ring
    _ = X := by rw [h, mul_one]

theorem rooted_series_differential :
    X * (1 - rootedSeries K) * derivative K (rootedSeries K) = rootedSeries K := by
  have hf := rooted_series_fixed_point K
  have hd := congrArg (derivative K) hf
  rw [Derivation.leibniz, derivative_X,
    tree_exp_derivative K (rootedSeries K) (rooted_series_constant K)] at hd
  simp only [smul_eq_mul, mul_one] at hd
  linear_combination X * hd - (X * derivative K (rootedSeries K) + 1) * hf

end
end Sigma
