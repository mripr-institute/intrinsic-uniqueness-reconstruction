import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace Sigma
noncomputable section
open scoped ComplexConjugate ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A genuine rank-one bounded operator: `x ↦ ⟪v,x⟫ u`. -/
def rankOneOperator (u v : H) : H →L[ℂ] H := (innerSL ℂ v).smulRight u

theorem rankOneOperator_apply (u v x : H) :
    rankOneOperator u v x = @inner ℂ H _ v x • u := rfl

theorem rankOneOperator_norm_le (u v : H) : ‖rankOneOperator u v‖ ≤ ‖u‖*‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  rw [rankOneOperator_apply,norm_smul]
  calc
    _ ≤ (‖v‖*‖x‖)*‖u‖ := mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
    _ = _ := by ring

/-- The standard nuclear/rank-one characterization on a complex Hilbert
space. The series converges in the actual bounded-operator norm. -/
def IsNuclearOperator (T : H →L[ℂ] H) : Prop :=
  ∃ u v : ℕ → H, Summable (fun n => ‖u n‖*‖v n‖) ∧
    HasSum (fun n => rankOneOperator (u n) (v n)) T

def hilbertBasisTrace (b : HilbertBasis ℕ ℂ H) (T : H →L[ℂ] H) : ℂ :=
  ∑' n, @inner ℂ H _ (b n) (T (b n))

theorem nuclear_representation_apply_hasSum
    (T : H →L[ℂ] H) (u v : ℕ → H)
    (hrep : HasSum (fun n => rankOneOperator (u n) (v n)) T) (x : H) :
    HasSum (fun n => @inner ℂ H _ (v n) x • u n) (T x) :=
  hrep.mapL (ContinuousLinearMap.apply ℂ H x)

theorem nuclear_representation_pairing_summable (u v : ℕ → H)
    (huv : Summable (fun n => ‖u n‖*‖v n‖)) :
    Summable (fun n => ‖@inner ℂ H _ (v n) (u n)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ huv
  intro n
  simpa only [mul_comm] using norm_inner_le_norm (𝕜 := ℂ) (v n) (u n)

theorem rankOneOperator_diagonal (b : HilbertBasis ℕ ℂ H) (u v : H) (n : ℕ) :
    @inner ℂ H _ (b n) (rankOneOperator u v (b n)) =
      @inner ℂ H _ v (b n) * @inner ℂ H _ (b n) u := by
  rw [rankOneOperator_apply,inner_smul_right]

theorem rankOneOperator_diagonal_norm_summable (b : HilbertBasis ℕ ℂ H) (u v : H) :
    Summable (fun n => ‖@inner ℂ H _ (b n) (rankOneOperator u v (b n))‖) := by
  have h := lp.summable_mul (by rw [Real.isConjExponent_iff]; norm_num :
    (2:ℝ≥0∞).toReal.IsConjExponent (2:ℝ≥0∞).toReal)
    (b.repr v) (b.repr u)
  convert h using 1
  funext n
  rw [rankOneOperator_diagonal,norm_mul,b.repr_apply_apply,b.repr_apply_apply,norm_inner_symm]

theorem rankOneOperator_diagonal_norm_tsum_le (b : HilbertBasis ℕ ℂ H) (u v : H) :
    (∑' n, ‖@inner ℂ H _ (b n) (rankOneOperator u v (b n))‖) ≤ ‖u‖*‖v‖ := by
  have h := lp.tsum_mul_le_mul_norm'
    (by rw [Real.isConjExponent_iff]; norm_num :
      (2:ℝ≥0∞).toReal.IsConjExponent (2:ℝ≥0∞).toReal) (b.repr v) (b.repr u)
  convert h using 1
  · apply tsum_congr
    intro n
    rw [rankOneOperator_diagonal,norm_mul,b.repr_apply_apply,b.repr_apply_apply,norm_inner_symm]
  · simp [mul_comm]

theorem rankOneOperator_trace (b : HilbertBasis ℕ ℂ H) (u v : H) :
    hilbertBasisTrace b (rankOneOperator u v) = @inner ℂ H _ v u := by
  unfold hilbertBasisTrace
  simp only [rankOneOperator_diagonal]
  exact b.tsum_inner_mul_inner v u

theorem nuclear_representation_double_norm_summable
    (b : HilbertBasis ℕ ℂ H) (u v : ℕ → H)
    (huv : Summable (fun n => ‖u n‖*‖v n‖)) :
    Summable (fun p : ℕ × ℕ =>
      ‖@inner ℂ H _ (b p.2) (rankOneOperator (u p.1) (v p.1) (b p.2))‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun n => rankOneOperator_diagonal_norm_summable b (u n) (v n), ?_⟩
  exact Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun i => norm_nonneg _))
    (fun n => rankOneOperator_diagonal_norm_tsum_le b (u n) (v n)) huv

theorem nuclear_representation_diagonal_hasSum
    (b : HilbertBasis ℕ ℂ H) (T : H →L[ℂ] H) (u v : ℕ → H)
    (hT : HasSum (fun n => rankOneOperator (u n) (v n)) T) (i : ℕ) :
    HasSum (fun n => @inner ℂ H _ (b i) (rankOneOperator (u n) (v n) (b i)))
      (@inner ℂ H _ (b i) (T (b i))) := by
  exact hT.mapL ((innerSL ℂ (b i)).comp (ContinuousLinearMap.apply ℂ H (b i)))

theorem nuclear_diagonal_summable (b : HilbertBasis ℕ ℂ H)
    {T : H →L[ℂ] H} (hT : IsNuclearOperator T) :
    Summable (fun i => ‖@inner ℂ H _ (b i) (T (b i))‖) := by
  obtain ⟨u,v,huv,hrep⟩ := hT
  have hn := nuclear_representation_double_norm_summable b u v huv
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hn.prod_symm.prod
  intro i
  rw [← (nuclear_representation_diagonal_hasSum b T u v hrep i).tsum_eq]
  exact norm_tsum_le_tsum_norm (hn.prod_symm.prod_factor i)

/-- For every nuclear representation, the diagonal sum in any Hilbert basis
equals the same rank-one pairing series. Absolute double summability justifies
interchanging the two sums. -/
theorem nuclear_trace_representation (b : HilbertBasis ℕ ℂ H)
    (T : H →L[ℂ] H) (u v : ℕ → H)
    (huv : Summable (fun n => ‖u n‖*‖v n‖))
    (hrep : HasSum (fun n => rankOneOperator (u n) (v n)) T) :
    hilbertBasisTrace b T = ∑' n, @inner ℂ H _ (v n) (u n) := by
  have hn := nuclear_representation_double_norm_summable b u v huv
  have hd : Summable (fun p : ℕ × ℕ =>
      @inner ℂ H _ (b p.2) (rankOneOperator (u p.1) (v p.1) (b p.2))) := hn.of_norm
  calc
    _ = ∑' i, ∑' n, @inner ℂ H _ (b i) (rankOneOperator (u n) (v n) (b i)) := by
      apply tsum_congr
      intro i
      exact (nuclear_representation_diagonal_hasSum b T u v hrep i).tsum_eq.symm
    _ = ∑' n, ∑' i, @inner ℂ H _ (b i) (rankOneOperator (u n) (v n) (b i)) :=
      tsum_comm hd
    _ = _ := by
      apply tsum_congr
      intro n
      exact rankOneOperator_trace b (u n) (v n)

theorem nuclear_trace_basis_independent (b c : HilbertBasis ℕ ℂ H)
    {T : H →L[ℂ] H} (hT : IsNuclearOperator T) :
    hilbertBasisTrace b T = hilbertBasisTrace c T := by
  obtain ⟨u,v,huv,hrep⟩ := hT
  exact (nuclear_trace_representation b T u v huv hrep).trans
    (nuclear_trace_representation c T u v huv hrep).symm

/-- The trace is selected from a genuine nuclear representation. The theorem
below proves equality with every Hilbert-basis diagonal sum, so neither the
selected representation nor the basis affects its value. -/
def nuclearTrace (T : H →L[ℂ] H) (hT : IsNuclearOperator T) : ℂ :=
  ∑' n, @inner ℂ H _ (hT.choose_spec.choose n) (hT.choose n)

theorem trace_eq_basis_sum (b : HilbertBasis ℕ ℂ H)
    (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    nuclearTrace T hT = ∑' n, @inner ℂ H _ (b n) (T (b n)) := by
  exact (nuclear_trace_representation b T hT.choose hT.choose_spec.choose
    hT.choose_spec.choose_spec.1 hT.choose_spec.choose_spec.2).symm

end
end Sigma
