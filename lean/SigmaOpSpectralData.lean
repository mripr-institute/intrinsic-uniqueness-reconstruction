import SigmaOpDiagonalNuclear
import SigmaOpSpectralMeasure

namespace Sigma
noncomputable section
open MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 800000

variable {ι κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem rank_one_arbitrary_basis_diagonal (b : HilbertBasis ι ℂ H) (u v : H) (i : ι) :
    @inner ℂ H _ (b i) (rankOneOperator u v (b i)) =
      @inner ℂ H _ v (b i) * @inner ℂ H _ (b i) u := by
  rw [rankOneOperator_apply, inner_smul_right]

theorem rank_one_arbitrary_basis_norm_summable (b : HilbertBasis ι ℂ H) (u v : H) :
    Summable (fun i => ‖@inner ℂ H _ (b i) (rankOneOperator u v (b i))‖) := by
  have h := lp.summable_mul (by rw [Real.isConjExponent_iff]; norm_num :
    (2:ℝ≥0∞).toReal.IsConjExponent (2:ℝ≥0∞).toReal) (b.repr v) (b.repr u)
  convert h using 1
  funext i
  rw [rank_one_arbitrary_basis_diagonal, norm_mul, b.repr_apply_apply,
    b.repr_apply_apply, norm_inner_symm]

theorem rank_one_arbitrary_basis_norm_tsum_le (b : HilbertBasis ι ℂ H) (u v : H) :
    (∑' i, ‖@inner ℂ H _ (b i) (rankOneOperator u v (b i))‖) ≤ ‖u‖*‖v‖ := by
  have h := lp.tsum_mul_le_mul_norm'
    (by rw [Real.isConjExponent_iff]; norm_num :
      (2:ℝ≥0∞).toReal.IsConjExponent (2:ℝ≥0∞).toReal) (b.repr v) (b.repr u)
  convert h using 1
  · apply tsum_congr
    intro i
    rw [rank_one_arbitrary_basis_diagonal, norm_mul, b.repr_apply_apply,
      b.repr_apply_apply, norm_inner_symm]
  · simp [mul_comm]

theorem nuclear_arbitrary_basis_double_norm_summable
    (b : HilbertBasis ι ℂ H) (u v : ℕ → H)
    (huv : Summable (fun n => ‖u n‖*‖v n‖)) :
    Summable (fun p : ℕ × ι =>
      ‖@inner ℂ H _ (b p.2) (rankOneOperator (u p.1) (v p.1) (b p.2))‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun n => rank_one_arbitrary_basis_norm_summable b (u n) (v n), ?_⟩
  exact Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun i => norm_nonneg _))
    (fun n => rank_one_arbitrary_basis_norm_tsum_le b (u n) (v n)) huv

theorem nuclear_arbitrary_basis_diagonal_hasSum
    (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) (u v : ℕ → H)
    (hT : HasSum (fun n => rankOneOperator (u n) (v n)) T) (i : ι) :
    HasSum (fun n => @inner ℂ H _ (b i) (rankOneOperator (u n) (v n) (b i)))
      (@inner ℂ H _ (b i) (T (b i))) :=
  hT.mapL ((innerSL ℂ (b i)).comp (ContinuousLinearMap.apply ℂ H (b i)))

/-- Absolute diagonal summability for every Hilbert basis, including finite and empty ones. -/
theorem nuclear_arbitrary_basis_diagonal_summable (b : HilbertBasis ι ℂ H)
    {T : H →L[ℂ] H} (hT : IsNuclearOperator T) :
    Summable (fun i => ‖@inner ℂ H _ (b i) (T (b i))‖) := by
  obtain ⟨u,v,huv,hrep⟩ := hT
  have hn := nuclear_arbitrary_basis_double_norm_summable b u v huv
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hn.prod_symm.prod
  intro i
  rw [← (nuclear_arbitrary_basis_diagonal_hasSum b T u v hrep i).tsum_eq]
  exact norm_tsum_le_tsum_norm (hn.prod_symm.prod_factor i)

theorem nuclear_arbitrary_basis_trace_representation (b : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (u v : ℕ → H)
    (huv : Summable (fun n => ‖u n‖*‖v n‖))
    (hrep : HasSum (fun n => rankOneOperator (u n) (v n)) T) :
    (∑' i, @inner ℂ H _ (b i) (T (b i))) = ∑' n, @inner ℂ H _ (v n) (u n) := by
  have hn := nuclear_arbitrary_basis_double_norm_summable b u v huv
  have hd : Summable (fun p : ℕ × ι =>
      @inner ℂ H _ (b p.2) (rankOneOperator (u p.1) (v p.1) (b p.2))) := hn.of_norm
  calc
    _ = ∑' i, ∑' n, @inner ℂ H _ (b i) (rankOneOperator (u n) (v n) (b i)) := by
      apply tsum_congr
      intro i
      exact (nuclear_arbitrary_basis_diagonal_hasSum b T u v hrep i).tsum_eq.symm
    _ = ∑' n, ∑' i, @inner ℂ H _ (b i) (rankOneOperator (u n) (v n) (b i)) := tsum_comm hd
    _ = _ := by
      apply tsum_congr
      intro n
      simp only [rank_one_arbitrary_basis_diagonal]
      exact b.tsum_inner_mul_inner (v n) (u n)

theorem nuclear_trace_eq_arbitrary_basis_sum (b : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    nuclearTrace T hT = ∑' i, @inner ℂ H _ (b i) (T (b i)) :=
  (nuclear_arbitrary_basis_trace_representation b T hT.choose hT.choose_spec.choose
    hT.choose_spec.choose_spec.1 hT.choose_spec.choose_spec.2).symm

theorem nuclear_arbitrary_basis_trace_independent
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H)
    (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    (∑' i, @inner ℂ H _ (b i) (T (b i))) = ∑' j, @inner ℂ H _ (c j) (T (c j)) := by
  rw [← nuclear_trace_eq_arbitrary_basis_sum b T hT,
    ← nuclear_trace_eq_arbitrary_basis_sum c T hT]

/-- The nuclear hypothesis is about the actual bounded operator; summability
and its trace series are conclusions, for an arbitrary spectral index type. -/
theorem nuclear_positive_diagonal_summable_trace (b : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hact : ∀ i, T (b i) = (f i : ℂ) • b i) (hT : IsNuclearOperator T) :
    Summable f ∧ nuclearTrace T hT = ((∑' i, f i : ℝ) : ℂ) := by
  classical
  have he (i : ι) : @inner ℂ H _ (b i) (T (b i)) = (f i : ℂ) := by
    rw [hact i, inner_smul_right, ← b.repr_apply_apply, b.repr_self,
      lp.single_apply_self, mul_one]
  constructor
  · have hn := nuclear_arbitrary_basis_diagonal_summable b hT
    simpa only [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf _)] using hn
  · rw [nuclear_trace_eq_arbitrary_basis_sum b, Complex.ofReal_tsum]
    exact tsum_congr he

/-- Summable spectral coefficients give an actual nuclear representation even
for an arbitrary index type. Only their derived countable support is enumerated. -/
theorem arbitrary_diagonal_nuclear_of_summable [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) (f : ι → ℂ)
    (hact : ∀ i, T (b i) = f i • b i)
    (hf : Summable (fun i => ‖f i‖)) : IsNuclearOperator T := by
  classical
  have hb (i : ι) : ‖b i‖ = 1 := b.orthonormal.1 i
  have hp : Summable (fun i => ‖f i • b i‖ * ‖b i‖) := by
    simpa only [norm_smul, hb, mul_one] using hf
  have hs : Summable (fun i => rankOneOperator (f i • b i) (b i)) :=
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun i => rankOneOperator_norm_le _ _) hp).of_norm
  have hr (i j : ι) : rankOneOperator (f i • b i) (b i) (b j) =
      if i = j then f j • b j else 0 := by
    rw [rankOneOperator_apply, ← b.repr_apply_apply, b.repr_self]
    by_cases h : i = j
    · subst i
      simp only [lp.single_apply_self, one_smul, if_true]
    · simp [h, lp.single_apply_ne _ _ _ h]
  have he : (∑' i, rankOneOperator (f i • b i) (b i)) = T := by
    have hbas (i : ι) : (∑' j, rankOneOperator (f j • b j) (b j)) (b i) = T (b i) := by
      have hsum := (ContinuousLinearMap.apply ℂ H (b i)).hasSum hs.hasSum
      simp only [ContinuousLinearMap.apply_apply, hr] at hsum
      exact hsum.unique (by simpa only [hact i] using hasSum_ite_eq i (f i • b i))
    ext x
    have hleft := (∑' i, rankOneOperator (f i • b i) (b i)).hasSum (b.hasSum_repr x)
    have hright := T.hasSum (b.hasSum_repr x)
    simp only [map_smul, hbas] at hleft hright
    exact hleft.unique hright
  let S := Function.support f
  letI : Encodable S := hf.of_norm.countable_support.toEncodable
  let u : S → H := fun i => f i • b i
  let v : S → H := fun i => b i
  have hsupport : Function.support (fun i => rankOneOperator (f i • b i) (b i)) ⊆ S := by
    intro i hi
    contrapose! hi
    have hf0 : f i = 0 := by simpa only [S, Function.mem_support, not_not] using hi
    simp only [Function.mem_support, not_not]
    ext x
    simp [hf0, rankOneOperator_apply]
  have hrep : HasSum (fun i : S => rankOneOperator (u i) (v i)) T :=
    (hasSum_subtype_iff_of_support_subset hsupport).mpr (he ▸ hs.hasSum)
  let U : ℕ → H := Function.extend Encodable.encode u 0
  let V : ℕ → H := Function.extend Encodable.encode v 0
  have heprod : (fun n => ‖U n‖ * ‖V n‖) =
      Function.extend Encodable.encode (fun i => ‖u i‖ * ‖v i‖) 0 := by
    funext n
    by_cases h : ∃ i : S, Encodable.encode i = n
    · obtain ⟨i, rfl⟩ := h
      simp only [U, V, Encodable.encode_injective.extend_apply]
    · simp only [U, V, Function.extend_apply' _ _ n h, Pi.zero_apply, norm_zero, zero_mul]
  have herank : (fun n => rankOneOperator (U n) (V n)) =
      Function.extend Encodable.encode (fun i => rankOneOperator (u i) (v i)) 0 := by
    funext n
    by_cases h : ∃ i : S, Encodable.encode i = n
    · obtain ⟨i, rfl⟩ := h
      simp only [U, V, Encodable.encode_injective.extend_apply]
    · simp only [U, V, Function.extend_apply' _ _ n h, Pi.zero_apply]
      ext x
      simp [rankOneOperator_apply]
  refine ⟨U, V, ?_, ?_⟩
  · rw [heprod]
    exact (summable_extend_zero Encodable.encode_injective).mpr (hp.subtype S)
  · rw [herank]
    exact (hasSum_extend_zero Encodable.encode_injective).mpr hrep

theorem nuclear_spectral_higher_power [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) (x : ι → OpUnitInterval) (q n : ℕ)
    (Tq Tn : H →L[ℂ] H)
    (hqact : ∀ i, Tq (b i) = (((x i : ℝ)^q : ℝ) : ℂ) • b i)
    (hnact : ∀ i, Tn (b i) = (((x i : ℝ)^(n+q) : ℝ) : ℂ) • b i)
    (hTq : IsNuclearOperator Tq) : IsNuclearOperator Tn := by
  have hs := (nuclear_positive_diagonal_summable_trace b Tq _
    (fun i => pow_nonneg (x i).property.1 q) hqact hTq).1
  apply arbitrary_diagonal_nuclear_of_summable b Tn _ hnact
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (x _).property.1 _)]
  apply Summable.of_nonneg_of_le (fun i => pow_nonneg (x i).property.1 _) _ hs
  intro i
  rw [pow_add]
  exact mul_le_of_le_one_left (pow_nonneg (x i).property.1 _)
    (pow_le_one₀ (x i).property.1 (x i).property.2)

theorem nuclear_spectral_power_summable (b : HilbertBasis ι ℂ H)
    (x : ι → OpUnitInterval) (q : ℕ) (T : H →L[ℂ] H)
    (hact : ∀ i, T (b i) = (((x i : ℝ)^q : ℝ) : ℂ) • b i)
    (hT : IsNuclearOperator T) : Summable (fun i => (x i : ℝ)^q) :=
  (nuclear_positive_diagonal_summable_trace b T _
    (fun i => pow_nonneg (x i).property.1 q) hact hT).1

/-- Every actual integer power trace is a moment of the weighted spectral
measure. The sole finiteness premise on the base power is nuclearity. -/
theorem nuclear_integer_trace_eq_spectral_moment (b : HilbertBasis ι ℂ H)
    (x : ι → OpUnitInterval) (q n : ℕ) (Tq Tn : H →L[ℂ] H)
    (hqact : ∀ i, Tq (b i) = (((x i : ℝ)^q : ℝ) : ℂ) • b i)
    (hnact : ∀ i, Tn (b i) = (((x i : ℝ)^(n+q) : ℝ) : ℂ) • b i)
    (hTq : IsNuclearOperator Tq) (hTn : IsNuclearOperator Tn) :
    nuclearTrace Tn hTn =
      ((∫ y : OpUnitInterval, (y : ℝ)^n ∂spectralWeightedMeasure x q : ℝ) : ℂ) := by
  rw [spectral_weighted_measure_moment x q
    (nuclear_spectral_power_summable b x q Tq hqact hTq)]
  exact (nuclear_positive_diagonal_summable_trace b Tn _
    (fun i => pow_nonneg (x i).property.1 (n+q)) hnact hTn).2

end
end Sigma
