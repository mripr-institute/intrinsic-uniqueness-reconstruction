import SigmaOpNuclearTrace

namespace Sigma
noncomputable section
open scoped Topology
set_option maxHeartbeats 800000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem hilbert_basis_operator_ext (b : HilbertBasis ℕ ℂ H) (S T : H →L[ℂ] H)
    (h : ∀ n, S (b n) = T (b n)) : S = T := by
  ext x
  have hs := S.hasSum (b.hasSum_repr x)
  have ht := T.hasSum (b.hasSum_repr x)
  simp only [map_smul, h] at hs ht
  exact hs.unique ht

omit [CompleteSpace H] in
theorem rank_one_diagonal_basis (b : HilbertBasis ℕ ℂ H) (f : ℕ → ℂ) (k n : ℕ) :
    rankOneOperator (f k • b k) (b k) (b n) =
      if k = n then f n • b n else 0 := by
  classical
  rw [rankOneOperator_apply, ← b.repr_apply_apply, b.repr_self]
  by_cases h : k = n
  · subst k
    simp only [lp.single_apply_self, one_smul, if_true]
  · simp [h, lp.single_apply_ne _ _ _ h]

/-- Summable diagonal magnitudes yield a nuclear representation converging in
bounded-operator norm. The input is an actual operator with the stated action. -/
theorem diagonal_operator_nuclear_of_summable (b : HilbertBasis ℕ ℂ H)
    (T : H →L[ℂ] H) (f : ℕ → ℂ) (hT : ∀ n, T (b n) = f n • b n)
    (hf : Summable (fun n => ‖f n‖)) : IsNuclearOperator T := by
  have hb (n : ℕ) : ‖b n‖ = 1 := b.orthonormal.1 n
  have hprod : Summable (fun n => ‖f n • b n‖*‖b n‖) := by
    simpa only [norm_smul, hb, mul_one] using hf
  have hs : Summable (fun n => rankOneOperator (f n • b n) (b n)) :=
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => rankOneOperator_norm_le _ _) hprod).of_norm
  have he : (∑' n, rankOneOperator (f n • b n) (b n)) = T := by
    apply hilbert_basis_operator_ext b
    intro n
    have hsum := (ContinuousLinearMap.apply ℂ H (b n)).hasSum hs.hasSum
    have hone := hasSum_ite_eq n (f n • b n)
    simp only [ContinuousLinearMap.apply_apply, rank_one_diagonal_basis] at hsum
    exact hsum.unique (by simpa only [hT n] using hone)
  exact ⟨fun n => f n • b n, fun n => b n, hprod, he ▸ hs.hasSum⟩

omit [CompleteSpace H] in
theorem diagonal_operator_trace (b : HilbertBasis ℕ ℂ H)
    (T : H →L[ℂ] H) (f : ℕ → ℂ) (hT : ∀ n, T (b n) = f n • b n) :
    hilbertBasisTrace b T = ∑' n, f n := by
  unfold hilbertBasisTrace
  apply tsum_congr
  intro n
  rw [hT n, inner_smul_right]
  have hb : @inner ℂ H _ (b n) (b n) = 1 := by
    rw [← b.repr_apply_apply, b.repr_self]
    exact lp.single_apply_self _ _ _
  rw [hb, mul_one]

theorem diagonal_operator_nuclear_iff (b : HilbertBasis ℕ ℂ H)
    (T : H →L[ℂ] H) (f : ℕ → ℂ) (hT : ∀ n, T (b n) = f n • b n) :
    IsNuclearOperator T ↔ Summable (fun n => ‖f n‖) := by
  constructor
  · intro hn
    have hdiag := nuclear_diagonal_summable b hn
    have he (n : ℕ) : @inner ℂ H _ (b n) (T (b n)) = f n := by
      rw [hT n, inner_smul_right, ← b.repr_apply_apply, b.repr_self,
        lp.single_apply_self, mul_one]
    simpa only [he] using hdiag
  · exact diagonal_operator_nuclear_of_summable b T f hT

omit [CompleteSpace H] in
theorem diagonal_operator_nuclear_trace (b : HilbertBasis ℕ ℂ H)
    (T : H →L[ℂ] H) (f : ℕ → ℂ) (hT : ∀ n, T (b n) = f n • b n)
    (hn : IsNuclearOperator T) : nuclearTrace T hn = ∑' n, f n := by
  rw [trace_eq_basis_sum b]
  exact diagonal_operator_trace b T f hT

end
end Sigma
